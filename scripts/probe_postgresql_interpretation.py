#!/usr/bin/env python3
"""Observe synthetic PostgreSQL interpretation witnesses without executing SQL.

These fixed probes are supplementary evidence, excluded from every industrial
corpus denominator. PostgreSQL raw AST shape changes do not, by themselves,
establish semantic inequivalence. The focused observations expose special forms
that syntax acceptance alone cannot certify.
"""
from __future__ import annotations

import argparse
from collections import Counter
from datetime import datetime, timezone
import json
from pathlib import Path
import platform
import subprocess

from audit_postgresql_corpus import PG_LAST_VERSION, PG_VERSION, run_sqlean, sha256

ROOT = Path(__file__).resolve().parents[1]
CASES = [
    ("current_date", "SELECT CURRENT_DATE;", "SQL current-date value function"),
    ("session_value_keywords",
     "SELECT CURRENT_TIMESTAMP, CURRENT_USER, SESSION_USER, CURRENT_CATALOG, CURRENT_SCHEMA;",
     "Special SQL value functions"),
    ("postfix_isnull", "SELECT 1 ISNULL;", "Postfix IS NULL test"),
    ("postfix_notnull", "SELECT NULL NOTNULL;", "Postfix IS NOT NULL test"),
    ("from_only", "SELECT * FROM ONLY users;", "ONLY relation reference"),
    ("update_only", "UPDATE ONLY users SET age = 1 WHERE id = 2;", "ONLY update target"),
    ("delete_only", "DELETE FROM ONLY users WHERE id = 2;", "ONLY delete target"),
    ("comma_from_control",
     "SELECT u.id, o.id FROM users u, orders o WHERE u.id = o.user_id;",
     "Existing comma-FROM coverage control; explicit CROSS JOIN may change raw AST shape"),
]


def ast_observation(tree):
    nodes = []

    def walk(value):
        if isinstance(value, list):
            for item in value:
                walk(item)
        elif isinstance(value, dict):
            for name, child in value.items():
                if name[:1].isupper() and isinstance(child, dict):
                    nodes.append((name, child))
                # PostgreSQL JSON omits the RangeVar wrapper for typed DML
                # relation fields, while FROM-list entries keep that wrapper.
                if name == "relation" and isinstance(child, dict) and "relname" in child:
                    nodes.append(("RangeVar", child))
                walk(child)

    walk(tree)
    statements = tree.get("stmts", [])
    return {
        "statement_count": len(statements),
        "statement": next(iter(statements[0]["stmt"])) if len(statements) == 1 else None,
        "node_kinds": dict(sorted(Counter(kind for kind, _ in nodes).items())),
        "sql_value_functions": [node["op"] for kind, node in nodes if kind == "SQLValueFunction"],
        "null_tests": [node["nulltesttype"] for kind, node in nodes if kind == "NullTest"],
        "relations": [
            {"schema": node.get("schemaname"), "name": node["relname"],
             "inherits": node.get("inh", False), "alias": node.get("alias", {}).get("aliasname")}
            for kind, node in nodes if kind == "RangeVar"
        ],
        "explicit_target_aliases": [
            node["name"] for kind, node in nodes if kind == "ResTarget" and "name" in node
        ],
        "column_references": [
            [field["String"]["sval"] if "String" in field else "*" for field in node["fields"]]
            for kind, node in nodes if kind == "ColumnRef"
        ],
    }


def parse_observation(parser, sql):
    try:
        tree = json.loads(parser.parse_sql_json(sql))
    except parser.ParseError as error:
        return {"status": "rejected", "diagnostic": str(error)}
    result = ast_observation(tree)
    return {"status": "accepted" if result["statement_count"] == 1 else "extraction_error",
            **result}


def render_observation(binary, sql, select, timeout):
    # SELECT uses the checked serializer. The existing --postgres API also
    # renders DML, but supplies no rendering certificate; record that difference.
    options = ["--render-assurance", "postgres"] if select else ["--postgres"]
    try:
        proc = subprocess.run([str(binary), *options], input=sql, text=True,
                              encoding="utf-8", capture_output=True, timeout=timeout, check=False)
    except subprocess.TimeoutExpired:
        return {"status": "timeout", "timeout_seconds": timeout}
    except OSError as error:
        return {"status": "infrastructure_error", "diagnostic": str(error)}
    result = {"interface": options, "returncode": proc.returncode,
              "stdout": proc.stdout, "stderr": proc.stderr}
    if select:
        try:
            report = json.loads(proc.stdout)
        except ValueError:
            return {**result, "status": "infrastructure_error"}
        result["report"] = report
        if (proc.returncode == 0 and not proc.stderr and isinstance(report, dict)
                and report.get("status") == "rendered"
                and report.get("evidence") == "checked-instance"
                and report.get("semanticPreservation") is False
                and isinstance(report.get("sql"), str)):
            return {**result, "status": "rendered", "evidence": "checked-instance", "sql": report["sql"]}
        failure_codes = {"invalid": 1, "unsupported": 3, "inconclusive": 4, "mismatch": 1}
        if (isinstance(report, dict) and report.get("status") in failure_codes
                and proc.returncode == failure_codes[report["status"]] and "sql" not in report):
            return {**result, "status": report["status"]}
        return {**result, "status": "infrastructure_error"}
    if proc.returncode == 0 and not proc.stderr and proc.stdout.strip():
        return {**result, "status": "rendered", "evidence": "unchecked-render",
                "sql": proc.stdout.strip()}
    return {**result, "status": "infrastructure_error"}


def structural_flags(original, rendered):
    """Focused observations, not a general equivalence decision procedure."""
    flags = []
    if original["sql_value_functions"] != rendered["sql_value_functions"]:
        flags.append("sql-value-function-structure-changed")
    if original["null_tests"] != rendered["null_tests"]:
        flags.append("null-test-structure-changed")
    if original["relations"] != rendered["relations"]:
        flags.append("relation-reference-structure-changed")
    return flags


def main():
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument("--binary", type=Path, default=ROOT / ".lake/build/bin/sqlean")
    ap.add_argument("--output", type=Path,
                    default=ROOT / "docs/corpus/postgresql-2026-10-20/interpretation-probes.json")
    ap.add_argument("--timeout", type=float, default=5)
    args = ap.parse_args()
    if args.timeout <= 0:
        ap.error("timeout must be positive")
    try:
        import pglast
        from pglast import parser
    except ImportError:
        ap.error("install optional scripts/requirements-corpus.txt in a virtual environment")
    if pglast.__version__ != PG_LAST_VERSION or parser.get_postgresql_version() != PG_VERSION:
        ap.error(f"expected pglast {PG_LAST_VERSION} / PostgreSQL {PG_VERSION}")
    binary = args.binary.resolve()
    results = []
    failed = False
    for ident, sql, feature in CASES:
        original = parse_observation(parser, sql)
        syntax = run_sqlean(binary, sql, args.timeout)
        row = {"id": ident, "sql": sql, "expected_feature": feature,
               "postgres_input": original, "sqlean_syntax": syntax}
        if original["status"] != "accepted":
            failed = True  # A malformed fixed witness is an audit input error.
        if syntax["status"] in {"timeout", "infrastructure_error"}:
            failed = True
        if original["status"] == "accepted" and syntax["status"] == "accepted":
            rendering = render_observation(binary, sql, original["statement"] == "SelectStmt", args.timeout)
            row["sqlean_render"] = rendering
            if rendering["status"] in {"timeout", "infrastructure_error"}:
                failed = True
            if rendering["status"] == "rendered":
                rendered = parse_observation(parser, rendering["sql"])
                row["postgres_rendered"] = rendered
                if rendered["status"] == "accepted":
                    row["structural_observations"] = structural_flags(original, rendered)
                elif rendered["status"] == "extraction_error":
                    failed = True
        results.append(row)
    evidence = {
        "format_version": 1, "corpus_kind": "supplementary-synthetic-probes",
        "included_in_industrial_denominator": False, "sql_executed": False,
        "scope": "Raw PostgreSQL parse-tree and SQLean CLI-output observations only",
        "interpretation_note": "AST shape equality or difference alone is not a SQL semantics theorem; "
                               "the comma-FROM control intentionally permits explicit CROSS JOIN shape.",
        "observed_utc": datetime.now(timezone.utc).isoformat(),
        "python": platform.python_version(), "pglast": pglast.__version__,
        "postgres_parser_version": list(parser.get_postgresql_version()),
        "binary_sha256": sha256(binary.read_bytes()) if binary.is_file() else None,
        "runner_sha256": sha256(Path(__file__).read_bytes()),
        "syntax_runner_sha256": sha256((ROOT / "scripts/audit_postgresql_corpus.py").read_bytes()),
        "timeout_seconds": args.timeout, "infrastructure_or_input_failure": failed,
        "summary": {"probes": len(results),
                    "sqlean_syntax": dict(Counter(r["sqlean_syntax"]["status"] for r in results)),
                    "focused_structural_changes": sum(bool(r.get("structural_observations")) for r in results)},
        "results": results,
    }
    args.output.parent.mkdir(parents=True, exist_ok=True)
    args.output.write_text(json.dumps(evidence, ensure_ascii=False, indent=2) + "\n", encoding="utf-8")
    print(json.dumps(evidence["summary"], indent=2))
    print(f"Supplementary synthetic evidence: {args.output}")
    return int(failed)


if __name__ == "__main__":
    raise SystemExit(main())
