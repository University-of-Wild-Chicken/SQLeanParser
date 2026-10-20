#!/usr/bin/env python3
"""Check grammar-only CLI evidence and exact source/UTF-8 token spans.

SQL is supplied as inert JSONL input to the Lean grammar executable. No
database connection, shell interpretation, or PostgreSQL execution is used.
The JSON report describes an in-process certificate; it is not a serialized
proof or evidence of catalog/type validity, C action fidelity, or completeness.
"""
from __future__ import annotations

import argparse
from collections import Counter
import hashlib
import json
from pathlib import Path
import subprocess
import tempfile

ROOT = Path(__file__).resolve().parents[1]
FIXTURES = ROOT / "fixtures/postgresql_grammar"
EXE = ROOT / ".lake/build/bin/sqlean_pg_grammar"
COMMIT = "f0595c3d839debdb140903621c1b44a4f4d86256"
COMMON = {
    "profile": "postgresql-16.15-grammar-v0.1",
    "postgresqlCommit": COMMIT,
    "staticValidity": "not-checked",
    "grammarSemanticActions": "not-checked",
}
ACCEPT_KEYS = set(COMMON) | {
    "status", "evidence", "productionIds", "statementFamilies",
    "sourcePreservation", "sql", "tokens",
}
REJECT_KEYS = set(COMMON) | {"status", "evidence", "diagnostic"}


def strict_json(raw):
    def object_pairs(pairs):
        value = {}
        for key, item in pairs:
            if key in value:
                raise ValueError(f"duplicate JSON key: {key}")
            value[key] = item
        return value
    def nonfinite(value):
        raise ValueError(f"nonfinite JSON number: {value}")
    return json.loads(raw, object_pairs_hook=object_pairs, parse_constant=nonfinite)


def require(condition, message):
    if not condition:
        raise AssertionError(message)


def natural(value):
    return type(value) is int and value >= 0


def trivia_only(raw):
    """Recognize only the pinned scanner's whitespace and nested comments."""
    index, size = 0, len(raw)
    while index < size:
        if raw[index] in b" \t\n\r\f":
            index += 1
        elif raw[index:index + 2] == b"--":
            index += 2
            while index < size and raw[index] not in b"\r\n":
                index += 1
        elif raw[index:index + 2] == b"/*":
            index, depth = index + 2, 1
            while index < size and depth:
                if raw[index:index + 2] == b"/*":
                    depth, index = depth + 1, index + 2
                elif raw[index:index + 2] == b"*/":
                    depth, index = depth - 1, index + 2
                else:
                    index += 1
            if depth:
                return False
        else:
            return False
    return True


def inventory():
    data = json.loads((FIXTURES / "inventory.json").read_text())
    return {
        "terminals": {t["name"] for t in data["terminals"]} - {"$end", "error"},
        "families": {f["name"] for f in data["statement_families"]},
        "production_count": len(data["productions"]),
    }


def validate_report(report, sql, expected="grammar-accepted", family=None, kinds=None, domain=None):
    domain = domain or inventory()
    require(isinstance(report, dict), "report must be an object")
    require(report.get("status") == expected, f"unexpected grammar status: {report}")
    for key, value in COMMON.items():
        require(report.get(key) == value, f"wrong grammar boundary field: {key}")
    if expected != "grammar-accepted":
        require(expected in {"grammar-rejected", "inconclusive"}, "unknown expected status")
        require(set(report) == REJECT_KEYS, "rejection must not expose success evidence")
        require(report["evidence"] == "none", "rejection claimed grammar evidence")
        require(isinstance(report["diagnostic"], str) and report["diagnostic"], "missing diagnostic")
        return report
    require(set(report) == ACCEPT_KEYS, "unexpected/missing accepted-report fields")
    require(report["evidence"] == "context-free-derivation", "wrong grammar evidence level")
    require(report["sourcePreservation"] == "exact" and report["sql"] == sql,
            "source bytes changed")
    productions = report["productionIds"]
    require(isinstance(productions, list) and bool(productions), "missing production witnesses")
    require(all(natural(p) and p < domain["production_count"] for p in productions),
            "unknown/noninteger production ID")
    require(len(set(productions)) == len(productions), "production ID list is not distinct")
    families = report["statementFamilies"]
    require(isinstance(families, list) and
            all(isinstance(f, str) and f in domain["families"] for f in families),
            "unknown statement family")
    if family is not None:
        require(families == [family], f"wrong outer statement family: {families}, expected {family}")
    tokens = report["tokens"]
    require(isinstance(tokens, list), "tokens must be a list")
    encoded, previous = sql.encode("utf-8"), 0
    for token in tokens:
        require(isinstance(token, dict) and set(token) == {"kind", "lexeme", "start", "end"},
                "malformed token")
        require(isinstance(token["kind"], str) and token["kind"] in domain["terminals"],
                "unknown terminal kind")
        require(isinstance(token["lexeme"], str) and token["lexeme"], "empty/non-string token spelling")
        start, end = token["start"], token["end"]
        require(natural(start) and natural(end) and previous <= start < end <= len(encoded),
                "overlapping, out-of-range, or empty token byte span")
        require(encoded[start:end] == token["lexeme"].encode("utf-8"), "token byte slice differs")
        require(trivia_only(encoded[previous:start]), "nontrivia source omitted between tokens")
        previous = end
    require(trivia_only(encoded[previous:]), "nontrivia source omitted after tokens")
    if kinds is not None:
        require([t["kind"] for t in tokens] == kinds, "unexpected contextual token kinds")
    return report


def run_batch(cases, binary=EXE, fuel=None, timeout=60):
    args = [str(binary)]
    if fuel is not None:
        args += ["--max-transitions", str(fuel)]
    args += ["--jsonl"]
    request = "".join(json.dumps({"id": c["id"], "sql": c["sql"]}, ensure_ascii=False) + "\n"
                      for c in cases)
    process = subprocess.run(args, input=request, text=True, capture_output=True,
                             cwd=ROOT, timeout=timeout)
    require(not process.stderr, f"unexpected grammar stderr: {process.stderr}")
    lines = process.stdout.splitlines()
    require(len(lines) == len(cases), "JSONL response count differs from request count")
    results, expected_code = [], 0
    domain = inventory()
    for case, line in zip(cases, lines):
        envelope = strict_json(line)
        require(isinstance(envelope, dict) and set(envelope) == {"id", "result"},
                "malformed JSONL envelope")
        require(envelope["id"] == case["id"], "JSONL order/id mismatch")
        expected = "inconclusive" if fuel == 0 else case.get("expected", "grammar-accepted")
        result = validate_report(envelope["result"], case["sql"], expected,
                                 case.get("grammar_family"), case.get("token_kinds"), domain)
        if case.get("diagnostic_contains"):
            require(case["diagnostic_contains"] in result.get("diagnostic", ""),
                    "rejection diagnostic does not match the pinned boundary")
        if expected == "grammar-accepted" and case.get("entry_production") is not None:
            require(case["entry_production"] in result["productionIds"],
                    "expected outer-family entry production was not visited")
        code = {"grammar-accepted": 0, "grammar-rejected": 1, "inconclusive": 4}[expected]
        if not expected_code and code:
            expected_code = code
        results.append(result)
    require(process.returncode == expected_code, "JSONL exit code disagrees with result statuses")
    return results


BOUNDARIES = [
    {"sql": " \n/* outer /* nested */ end */ -- trailing\n", "token_kinds": []},
    {"sql": "/* λ */ SELECT \"é\", U&'d!0061t' UESCAPE '!'; -- Ω\n",
     "token_kinds": ["SELECT", "IDENT", "','", "SCONST", "';'"]},
    {"sql": "SELECT 'first' -- continuation\n 'second';",
     "token_kinds": ["SELECT", "SCONST", "';'"]},
    {"sql": "SELECT E'\\uD83D\\uDE00', $$a ' $1 /* x */$$, B'010'\n'11';",
     "token_kinds": ["SELECT", "SCONST", "','", "SCONST", "','", "BCONST", "';'"]},
    {"sql": "SELECT $001, 0x_FF, 0b_1010, 1_000, .5e+2;",
     "token_kinds": ["SELECT", "PARAM", "','", "ICONST", "','", "ICONST", "','", "ICONST", "','", "FCONST", "';'"]},
    {"sql": "SELECT x NOT IN (1) FROM t ORDER BY x NULLS LAST;",
     "token_kinds": ["SELECT", "IDENT", "NOT_LA", "IN_P", "'('", "ICONST", "')'", "FROM",
                     "IDENT", "ORDER", "BY", "IDENT", "NULLS_LA", "LAST_P", "';'"]},
    {"sql": "SELECT CAST('12:00' AS TIME WITH TIME ZONE);"},
    {"sql": "SELECT * FROM unnest(ARRAY[1,2]) WITH ORDINALITY AS q(x,n);"},
    {"sql": "SELECT CASE WHEN TRUE THEN COALESCE(NULL, 1) ELSE 2 END;"},
    {"sql": "SELECT CHECK FROM t;",
     "token_kinds": ["SELECT", "IDENT", "FROM", "IDENT", "';'"]},
    {"sql": "SELECT U&\"d!0061t\" UESCAPE E'\\x21' FROM t;",
     "token_kinds": ["SELECT", "IDENT", "FROM", "IDENT", "';'"]},
    {"sql": "SELECT 1 <=-2, 1 @- 2;",
     "token_kinds": ["SELECT", "ICONST", "LESS_EQUALS", "'-'", "ICONST", "','",
                     "ICONST", "Op", "ICONST", "';'"]},
    {"sql": "SELECT N'α', X'ff'\n'00';",
     "token_kinds": ["SELECT", "NCHAR", "SCONST", "','", "XCONST", "';'"]},
    {"sql": "SELECT 'a' /*\nblock comments do not continue strings */ 'b';",
     "expected": "grammar-rejected"},
    {"sql": "SELECT U&'x' UESCAPE 'λ';", "expected": "grammar-rejected"},
    {"sql": "SELECT E'\\uD800\\u0041';", "expected": "grammar-rejected"},
    {"sql": "CREATE ASSERTION a CHECK (TRUE);", "grammar_family": "CreateAssertionStmt"},
    {"sql": "CREATE FUNCTION f() RETURNS int LANGUAGE SQL BEGIN ATOMIC SELECT 1; END;",
     "grammar_family": "CreateFunctionStmt"},
    *({"sql": sql, "expected": "grammar-rejected"} for sql in [
        "SELECT FROM;", "CREATE TABLE x (", "SELECT $1a", "SELECT $0_1",
        "SELECT 1__2", "SELECT 0x", "SELECT 1e+", "SELECT E'\\u0000'",
        "SELECT U&'\\D800'", "SELECT U&'x' UESCAPE '0'", "SELECT E'\\xFF'",
        "SELECT \"\"", "SELECT 'unterminated", "/* unterminated",
        "SELECT 1\x00;", "SELECT 1\v;", "SELECT " + "@" * 64 + " 1",
    ]),
]


def protocol_checks(binary=EXE):
    cases = [dict(case, id=f"boundary-{index}") for index, case in enumerate(BOUNDARIES)]
    results = run_batch(cases, binary)
    run_batch([{"id": "zero-budget", "sql": "SELECT 1"}], binary, fuel=0)
    # Exercise the exact same API through stdin, a file, and an argument.
    sql = "/* keep UTF-8 λ */\r\nSELECT 1; -- trailing\r\n"
    with tempfile.TemporaryDirectory(prefix="sqlean-grammar-protocol-") as temporary:
        path = Path(temporary) / "input.sql"
        path.write_text(sql)
        for args, input_sql in [([], sql), (["--file", str(path)], None), ([sql], None)]:
            process = subprocess.run([str(binary)] + args, input=input_sql, text=True,
                                     capture_output=True, timeout=30)
            require(process.returncode == 0 and not process.stderr, "single-source protocol failed")
            validate_report(strict_json(process.stdout), sql)
    requests = ['not-json', '{}', '{"id": 1, "sql": "SELECT 1"}',
                '{"id": "missing", "sql": null}', '{"id":"ok","sql":"SELECT 1"}']
    process = subprocess.run([str(binary), "--jsonl"], input="\n".join(requests) + "\n",
                             text=True, capture_output=True, timeout=30)
    require(process.returncode == 2 and not process.stderr, "invalid-request batch exit code")
    reports = [strict_json(line) for line in process.stdout.splitlines()]
    require(len(reports) == len(requests), "invalid request disrupted JSONL stream")
    for report in reports[:-1]:
        require(set(report) == {"status", "diagnostic"} and report["status"] == "invalid-request"
                and isinstance(report["diagnostic"], str) and report["diagnostic"],
                "malformed invalid-request report")
    require(reports[-1]["id"] == "ok", "valid request after errors was lost")
    validate_report(reports[-1]["result"], "SELECT 1")
    return len(results) + 1 + 3 + len(requests)


def read_cases(path, expected="grammar-accepted"):
    text = path.read_text()
    rows = json.loads(text) if path.suffix == ".json" else [
        strict_json(line) for line in text.splitlines()]
    require(isinstance(rows, list) and bool(rows), f"empty/non-list corpus: {path}")
    seen, result = set(), []
    for row in rows:
        require(isinstance(row, dict) and isinstance(row.get("id"), str) and row["id"],
                f"invalid corpus id: {path}")
        require(isinstance(row.get("sql"), str) and row["sql"], f"missing corpus SQL: {path}")
        require(row["id"] not in seen, f"duplicate corpus id: {path}")
        if "expected_status" in row:
            require(row["expected_status"] == expected, f"fixture status disagrees with category: {path}")
        seen.add(row["id"])
        result.append({**row, "id": path.relative_to(ROOT).as_posix() + ":" + row["id"],
                       "expected": expected, "fixture": path.relative_to(ROOT).as_posix()})
    return result


def load_cases(include_statement_families=True):
    paths = [
        FIXTURES / "synthetic.json",
        *[ROOT / "fixtures/external_postgresql" / (name + ".jsonl")
          for name in ["benchbase", "temporal", "river"]],
        *[ROOT / "fixtures" / factor / "concrete.jsonl"
          for factor in ["functions", "conditional", "pagination", "extended_types", "locking",
                         "join_contract", "using_contract", "natural_contract", "derived_contract",
                         "array_types", "array_constructors"]],
    ]
    if include_statement_families:
        paths.append(ROOT / "fixtures/statement_families/concrete.jsonl")
    cases = [case for path in paths for case in read_cases(path)]
    if include_statement_families:
        cases.extend(read_cases(ROOT / "fixtures/statement_families/negative.jsonl", "grammar-rejected"))
    require(len({case["id"] for case in cases}) == len(cases), "duplicate global corpus id")
    return cases


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--binary", type=Path, default=EXE)
    parser.add_argument("--report-json", type=Path)
    parser.add_argument("--without-statement-corpus", action="store_true",
                        help="development-only run before the pinned statement extraction is generated")
    args = parser.parse_args()
    cases = load_cases(not args.without_statement_corpus)
    checks = protocol_checks(args.binary)
    all_results = []
    for start in range(0, len(cases), 250):
        all_results.extend(run_batch(cases[start:start + 250], args.binary))
    summary = {
        "postgresql_commit": COMMIT, "profile": COMMON["profile"],
        "evidence": "finite CLI source-preservation and context-free grammar regression",
        "static_validity": "not-checked", "semantic_actions": "not-checked",
        "execution": "not-performed", "serialized_proof": False,
        "cases": len(cases), "protocol_checks": checks,
        "distinct_sql": len({c["sql"] for c in cases}),
        "fixtures": dict(sorted(Counter(c["fixture"] for c in cases).items())),
        "statuses": dict(sorted(Counter(r["status"] for r in all_results).items())),
        "observed_production_ids": sorted({p for r in all_results for p in r.get("productionIds", [])}),
        "families": dict(sorted(Counter(f for r in all_results for f in r.get("statementFamilies", [])).items())),
        "binary_sha256": hashlib.sha256(args.binary.read_bytes()).hexdigest(),
        "inputs": [{"path": path, "sha256": hashlib.sha256((ROOT / path).read_bytes()).hexdigest()}
                   for path in sorted({c["fixture"] for c in cases})],
    }
    if args.report_json:
        args.report_json.parent.mkdir(parents=True, exist_ok=True)
        args.report_json.write_text(json.dumps(summary, indent=2) + "\n")
    print(f"PASS: {len(cases)} grammar-only corpus cases, {checks} protocol checks, "
          f"{len(summary['families'])} observed statement families, "
          f"{len(summary['observed_production_ids'])} distinct reduction productions")


if __name__ == "__main__":
    main()
