#!/usr/bin/env python3
"""Replay external SQL through PostgreSQL's raw parser and SQLean's syntax tier.

No statement is executed. pglast is an optional audit dependency, not a Lean or
normal CI dependency. Source SQL is supplied on stdin, never through a shell.
"""
from __future__ import annotations

import argparse
from collections import Counter
from concurrent.futures import ThreadPoolExecutor
import hashlib
import json
from pathlib import Path
import platform
import re
import subprocess
import sys

ROOT = Path(__file__).resolve().parents[1]
PG_LAST_VERSION = "v7.21"
PG_VERSION = (17, 7)
ACCEPTED_REPORT = {
    "assurance": "syntax", "evidence": "parsed-ast",
    "profile": "sqlean-syntax-v0", "status": "parsed",
}
PARSE_ERROR = re.compile(r"^parse error: (\d+):(\d+): (.+)$", re.S)


def sha256(data: bytes) -> str:
    return hashlib.sha256(data).hexdigest()


def load_cases(paths: list[Path]) -> list[dict]:
    cases, ids, seen_sql = [], set(), {}
    for path in paths:
        for line, raw in enumerate(path.read_text(encoding="utf-8").splitlines(), 1):
            if not raw.strip():
                raise ValueError(f"{path}:{line}: blank record")
            case = json.loads(raw)
            for key in ("id", "source", "sql", "source_url"):
                if not isinstance(case.get(key), str) or not case[key].strip():
                    raise ValueError(f"{path}:{line}: missing/non-string {key}")
            if case["id"] in ids:
                raise ValueError(f"duplicate id: {case['id']}")
            if "\x00" in case["sql"]:
                raise ValueError(f"{case['id']}: embedded NUL")
            ids.add(case["id"])
            digest = sha256(case["sql"].encode())
            case = {**case, "sql_sha256": digest,
                    "duplicate_of": seen_sql.get(digest)}
            seen_sql.setdefault(digest, case["id"])
            cases.append(case)
    if not cases:
        raise ValueError("empty corpus")
    return cases


def strings(nodes: list[dict]) -> list[str]:
    return [n["String"]["sval"] for n in nodes if "String" in n]


def features(tree: dict) -> list[str]:
    """Candidate feature tags from the PG AST, not inferred repair counts.

    Tags may overlap and may describe supported syntax used in a more complex
    context. They identify what to inspect, not the first cause of rejection.
    """
    found = set()
    ordinary_functions = {"count", "sum", "avg", "min", "max"}
    basic_types = {"int", "int2", "int4", "int8", "integer", "bigint", "smallint",
                   "text", "varchar", "bpchar", "bool", "boolean", "numeric",
                   "decimal", "real", "float4", "float8", "double precision"}

    def walk(value):
        if isinstance(value, list):
            for child in value:
                walk(child)
        elif isinstance(value, dict):
            for kind, node in value.items():
                # PostgreSQL also uses names such as "typeName" for list-valued
                # fields (for example CREATE TYPE AS ENUM's name). Traverse
                # containers without treating every matching key as a node.
                if not isinstance(node, dict):
                    walk(node)
                    continue
                if kind == "FuncCall":
                    names = strings(node.get("funcname", []))
                    if len(names) != 1 or names[0] not in ordinary_functions:
                        found.add("general-function-call")
                    if node.get("over"):
                        found.add("window-function")
                    if node.get("agg_order") or node.get("agg_within_group"):
                        found.add("ordered-aggregate")
                elif kind in {"CaseExpr", "CoalesceExpr", "MinMaxExpr", "NullIfExpr"}:
                    found.add("conditional-expression")
                elif kind in {"A_ArrayExpr", "A_Indices", "A_Indirection"}:
                    found.add("array-or-subscripting")
                elif kind == "TypeName" or kind == "typeName":
                    names = strings(node.get("names", []))
                    if names and names[-1] not in basic_types:
                        found.add("extended-type")
                    if node.get("arrayBounds"):
                        found.add("array-or-subscripting")
                elif kind == "SQLValueFunction":
                    found.add("sql-value-keyword")
                elif kind in {"RangeVar", "relation"} and node.get("schemaname"):
                    found.add("schema-qualified-relation")
                elif kind == "ColumnRef" and len(node.get("fields", [])) > 2:
                    found.add("multi-part-column")
                elif kind == "SelectStmt":
                    if len(node.get("fromClause", [])) > 1:
                        found.add("comma-from")
                    if node.get("valuesLists"):
                        found.add("values-query")
                    if node.get("lockingClause"):
                        found.add("row-locking")
                    if node.get("windowClause"):
                        found.add("window-function")
                    if node.get("intoClause"):
                        found.add("select-into")
                    for key in ("limitCount", "limitOffset"):
                        if key in node:
                            bound = node[key].get("A_Const", {})
                            if "ival" not in bound:
                                found.add("expression-limit-offset")
                elif kind == "UpdateStmt" and node.get("fromClause"):
                    found.add("update-from")
                elif kind == "DeleteStmt" and node.get("usingClause"):
                    found.add("delete-using")
                elif kind == "InsertStmt":
                    if "selectStmt" not in node:
                        found.add("insert-default-values")
                if kind in {"InsertStmt", "UpdateStmt", "DeleteStmt"} and node.get("withClause"):
                    found.add("with-before-dml")
                if kind == "CommonTableExpr":
                    if node.get("ctematerialized", "CTEMaterializeDefault") != "CTEMaterializeDefault":
                        found.add("cte-materialization")
                    query = node.get("ctequery", {})
                    if any(k in query for k in ("InsertStmt", "UpdateStmt", "DeleteStmt", "MergeStmt")):
                        found.add("data-modifying-cte")
                    if node.get("search_clause") or node.get("cycle_clause"):
                        found.add("cte-search-cycle")
                elif kind in {"RangeFunction", "RangeTableFunc"}:
                    found.add("table-function")
                elif kind == "RowExpr":
                    found.add("row-constructor")
                elif kind == "A_Expr":
                    expr_kind = node.get("kind")
                    if expr_kind in {"AEXPR_OP_ANY", "AEXPR_OP_ALL"}:
                        found.add("quantified-comparison")
                    if expr_kind == "AEXPR_NULLIF":
                        found.add("conditional-expression")
                    if expr_kind == "AEXPR_OP":
                        names = strings(node.get("name", []))
                        if names and names[-1] not in {"+", "-", "*", "/", "=", "<>", "<", "<=", ">", ">="}:
                            found.add("extended-operator")
                elif kind == "SubLink" and node.get("subLinkType") in {"ALL_SUBLINK", "ARRAY_SUBLINK"}:
                    found.add("quantified-or-array-subquery")
                elif kind in {"CollateClause", "GroupingSet"}:
                    found.add("collation-or-grouping-sets")
                elif kind == "BooleanTest":
                    found.add("boolean-is-test")
                elif kind == "SetToDefault":
                    found.add("default-expression")
                walk(node)

    walk(tree)
    top = next(iter(tree.get("stmts", [{}])[0].get("stmt", {})), "empty")
    if top not in {"SelectStmt", "InsertStmt", "UpdateStmt", "DeleteStmt",
                   "CreateStmt", "AlterTableStmt", "DropStmt"}:
        found.add("statement:" + top)
    if top == "DropStmt":
        drop = tree["stmts"][0]["stmt"][top]
        if drop.get("removeType") != "OBJECT_TABLE":
            found.add("non-table-ddl")
    return sorted(found)


def run_sqlean(binary: Path, sql: str, timeout: float) -> dict:
    try:
        proc = subprocess.run([str(binary), "--assurance", "syntax"], input=sql,
                              text=True, encoding="utf-8", capture_output=True,
                              timeout=timeout, check=False)
    except subprocess.TimeoutExpired:
        return {"status": "timeout", "timeout_seconds": timeout}
    except OSError as error:
        return {"status": "infrastructure_error", "diagnostic": str(error)}
    diagnostic = proc.stderr.strip()
    if proc.returncode == 0:
        try:
            report = json.loads(proc.stdout)
        except ValueError:
            report = None
        if report == ACCEPTED_REPORT and not diagnostic:
            return {"status": "accepted"}
    elif proc.returncode == 1 and not proc.stdout and (match := PARSE_ERROR.fullmatch(diagnostic)):
        return {"status": "rejected", "diagnostic": diagnostic,
                "line": int(match[1]), "column": int(match[2]), "message": match[3]}
    return {"status": "infrastructure_error", "returncode": proc.returncode,
            "stdout": proc.stdout, "diagnostic": diagnostic}


def oracle_case(case: dict, parser) -> dict:
    try:
        tree = json.loads(parser.parse_sql_json(case["sql"]))
    except parser.ParseError as error:
        return {**case, "postgres": {"status": "rejected", "diagnostic": str(error)},
                "candidate_features": []}
    stmts = tree.get("stmts", [])
    if len(stmts) != 1:
        return {**case, "postgres": {"status": "extraction_error", "statements": len(stmts)},
                "candidate_features": []}
    tags = set(features(tree))
    # PostgreSQL maps postfix ISNULL/NOTNULL to the same AST as IS [NOT] NULL,
    # so consult its lexer to retain the spelling (without matching strings).
    tokens = {token.name for token in parser.scan(case["sql"])}
    if tokens & {"ISNULL", "NOTNULL"}:
        tags.add("postfix-null-test")
    if "ONLY" in tokens:
        tags.add("only-relation")
    return {**case, "postgres": {"status": "accepted",
                                "statement": next(iter(stmts[0]["stmt"]))},
            "candidate_features": sorted(tags)}


def summarize(results: list[dict]) -> dict:
    eligible = [r for r in results if r["postgres"]["status"] == "accepted"]
    rejected = [r for r in eligible if r["sqlean"]["status"] == "rejected"]
    sources = {}
    for source in sorted({r["source"] for r in results}):
        rows = [r for r in results if r["source"] == source]
        valid = [r for r in rows if r["postgres"]["status"] == "accepted"]
        sources[source] = {
            "records": len(rows), "postgres_accepted": len(valid),
            "sqlean_on_postgres_accepted": dict(sorted(Counter(r["sqlean"]["status"] for r in valid).items())),
            "oracle_excluded": len(rows) - len(valid),
        }
    return {
        "records": len(results),
        "unique_sql": len({r["sql_sha256"] for r in results}),
        "sqlean_on_unique_postgres_accepted": dict(sorted(Counter(
            r["sqlean"]["status"] for r in eligible if r.get("duplicate_of") is None).items())),
        "postgres_accepted": len(eligible),
        "postgres_rejected": sum(r["postgres"]["status"] == "rejected" for r in results),
        "extraction_errors": sum(r["postgres"]["status"] == "extraction_error" for r in results),
        "sqlean_on_postgres_accepted": dict(sorted(Counter(r["sqlean"]["status"] for r in eligible).items())),
        "sqlean_on_oracle_excluded": dict(sorted(Counter(
            r["sqlean"]["status"] for r in results if r["postgres"]["status"] != "accepted").items())),
        "candidate_features_in_rejected_queries": dict(Counter(
            feature for r in rejected for feature in r["candidate_features"]).most_common()),
        "untagged_rejections": sum(not r["candidate_features"] for r in rejected),
        "accepted_interpretation_watchlist": [
            r["id"] for r in eligible if r["sqlean"]["status"] == "accepted"
            and set(r["candidate_features"]) & {
                "sql-value-keyword", "postfix-null-test", "only-relation"}],
        "sources": sources,
    }


def fence(sql: str) -> str:
    longest = max((len(m[0]) for m in re.finditer(r"`+", sql)), default=0)
    ticks = "`" * max(3, longest + 1)
    return f"{ticks}sql\n{sql.rstrip()}\n{ticks}\n"


def failure_catalog(results: list[dict]) -> str:
    out = [
        "# PostgreSQL corpus rejection catalog\n\n",
        "Generated by `scripts/audit_postgresql_corpus.py`. Each entry preserves the ",
        "audited SQL, upstream location, PostgreSQL raw-parser disposition, and ",
        "SQLean diagnostic. Candidate features overlap; they are inspection aids, ",
        "not a proven first cause or a prediction of how many queries one fix unlocks.\n\n",
        "PostgreSQL acceptance is syntax only: no SQL was executed or schema/type ",
        "validity established. Application template transformations are recorded ",
        "in the input fixtures and `results.jsonl`.\n\n",
        "Accepted queries are omitted here; see the overview and interpretation ",
        "probes for accepted SQL that SQLean interprets differently from PostgreSQL.\n\n",
    ]
    for r in results:
        if r["sqlean"]["status"] == "accepted" and r["postgres"]["status"] == "accepted":
            continue
        out.extend([
            f'<a id="q-{sha256(r["id"].encode())[:12]}"></a>\n\n',
            f"## {r['id']}\n\n",
            f"[Upstream source]({r['source_url']}) · `{r['source']}`\n\n",
            f"PostgreSQL: **{r['postgres']['status']}**; SQLean: **{r['sqlean']['status']}**.\n\n",
        ])
        if r["postgres"].get("diagnostic"):
            out.append(f"PostgreSQL diagnostic: {r['postgres']['diagnostic']}\n\n")
        if r["sqlean"].get("diagnostic"):
            out.append(f"SQLean diagnostic: {r['sqlean']['diagnostic']}\n\n")
        if r["candidate_features"]:
            out.append("Candidate features: " + ", ".join(f"`{s}`" for s in r["candidate_features"]) + ".\n\n")
        if r.get("transformations"):
            out.append("Input transformations: " + json.dumps(r["transformations"], ensure_ascii=False) + ".\n\n")
        if r["duplicate_of"]:
            out.append(f"Exact audited SQL duplicates `{r['duplicate_of']}`.\n\n")
        out.append(fence(r["sql"]) + "\n")
    return "".join(out)


def main() -> int:
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument("--corpus", type=Path, nargs="+")
    ap.add_argument("--binary", type=Path, default=ROOT / ".lake/build/bin/sqlean")
    ap.add_argument("--output", type=Path, default=ROOT / ".lake/external-postgresql-audit")
    ap.add_argument("--timeout", type=float, default=5)
    ap.add_argument("--workers", type=int, default=4)
    args = ap.parse_args()
    if args.timeout <= 0 or args.workers < 1:
        ap.error("timeout and workers must be positive")
    try:
        import pglast
        from pglast import parser
    except ImportError:
        ap.error("install the optional scripts/requirements-corpus.txt in a virtual environment")
    if pglast.__version__ != PG_LAST_VERSION or parser.get_postgresql_version() != PG_VERSION:
        ap.error(f"expected pglast {PG_LAST_VERSION} / PostgreSQL {PG_VERSION}, got "
                 f"{pglast.__version__} / {parser.get_postgresql_version()}")
    paths = args.corpus or sorted((ROOT / "fixtures/external_postgresql").glob("*.jsonl"))
    binary = args.binary.resolve()
    cases = load_cases(paths)
    # The oracle is sequential; only independent SQLean child processes overlap.
    prepared = [oracle_case(case, parser) for case in cases]
    with ThreadPoolExecutor(max_workers=args.workers) as pool:
        reports = list(pool.map(lambda r: run_sqlean(binary, r["sql"], args.timeout), prepared))
    results = [{**case, "sqlean": report} for case, report in zip(prepared, reports)]
    summary = summarize(results)
    def git(*argv):
        return subprocess.check_output(["git", *argv], cwd=ROOT, text=True).strip()
    inputs = {str(p.relative_to(ROOT) if p.is_relative_to(ROOT) else p): sha256(p.read_bytes())
              for p in paths}
    proof_sources = sorted((ROOT / "SQLean").rglob("*.lean")) + [ROOT / "Main.lean"]
    evidence = {
        "format_version": 1, "scope": "single-statement syntax acceptance only",
        "sql_executed": False, "git_head": git("rev-parse", "HEAD"),
        "tracked_worktree_changes": git("diff", "--name-only", "HEAD"),
        "python": platform.python_version(), "pglast": pglast.__version__,
        "postgres_parser_version": list(parser.get_postgresql_version()),
        "binary_sha256": sha256(binary.read_bytes()), "inputs": inputs,
        "runner_sha256": sha256(Path(__file__).read_bytes()),
        "lean_sources_sha256": sha256(b"".join(
            str(p.relative_to(ROOT)).encode() + b"\0" + p.read_bytes() + b"\0" for p in proof_sources)),
        "timeout_seconds": args.timeout, "summary": summary,
    }
    args.output.mkdir(parents=True, exist_ok=True)
    result_bytes = "".join(json.dumps(r, ensure_ascii=False, sort_keys=True) + "\n"
                           for r in results).encode()
    (args.output / "results.jsonl").write_bytes(result_bytes)
    evidence["results_sha256"] = sha256(result_bytes)
    (args.output / "audit.json").write_text(json.dumps(evidence, indent=2) + "\n")
    (args.output / "failures.md").write_text(failure_catalog(results), encoding="utf-8")
    print(json.dumps(summary, indent=2))
    # Syntax gaps are the measured outcome; crashes/timeouts/extraction defects
    # must never look like successful completion of an audit.
    return int(any(r["sqlean"]["status"] in {"timeout", "infrastructure_error"}
                   or r["postgres"]["status"] == "extraction_error" for r in results))


if __name__ == "__main__":
    sys.exit(main())
