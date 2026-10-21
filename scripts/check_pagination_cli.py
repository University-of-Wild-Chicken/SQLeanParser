#!/usr/bin/env python3
"""Verify the first corpus-driven increment: expression LIMIT/OFFSET.

50 synthetic SELECTs receive full basic-profile validity and all three checked
renderings. 50 unchanged external SELECTs receive structural rendering evidence;
Tests.PaginationCorpus separately certifies their bounds under explicit test
parameter types, without claiming validity of their application schemas.

Only the synthetic cases execute, in isolated databases. PostgreSQL executes
original and rendered SQL using PREPARE/EXECUTE with separately supplied values.
SQLite executes rendered SQL and every directly portable original. Authored
row slices and explicit runtime error expectations are independent oracles.
"""
from __future__ import annotations

import argparse
import json
from pathlib import Path
import sqlite3
import subprocess

from check_advanced_cli import literal, question_parameters
from check_assurance_cli import assert_report
from check_postgresql_cli import connection, copy_result, marker, parse_results, run, sql_literal
from check_renderer_corpus import parameters, replay as renderer_replay, validate_report

ROOT = Path(__file__).resolve().parents[1]
FIXTURES = ROOT / "fixtures/pagination"
EXE = ROOT / ".lake/build/bin/sqlean"
PG_TYPES = {"int": "INTEGER", "text": "TEXT", "bool": "BOOLEAN"}


def invoke(mode, sql):
    # Some genuine source statements start with -- comments. Stdin preserves
    # their exact bytes and prevents argparse from treating SQL as an option.
    result = subprocess.run([str(EXE), "--render-assurance", mode], input=sql,
                            cwd=ROOT, capture_output=True, text=True, timeout=30)
    return validate_report(result, mode, sql)


def replay(mode, sql):
    return renderer_replay(mode, sql, invoke_fn=invoke)

# Static typing does not promise successful evaluation. These all have basic
# static certificates; the supplied execution values fail in PostgreSQL.
RUNTIME_CASES = [
    ("SELECT id FROM page_rows ORDER BY id LIMIT -1;", "", [], "2201W"),
    ("SELECT id FROM page_rows ORDER BY id LIMIT $1;", "int", [-1], "2201W"),
    ("SELECT id FROM page_rows ORDER BY id LIMIT 2 OFFSET $1;", "int", [-1], "2201X"),
    ("SELECT id FROM page_rows ORDER BY id LIMIT (1 / $1);", "int", [0], "22012"),
    ("SELECT id FROM page_rows ORDER BY id LIMIT CAST($1 AS INTEGER);",
     "text", ["not-an-integer"], "22P02"),
    ("SELECT id FROM page_rows ORDER BY id LIMIT ($1 + 1);",
     "int", [2147483647], "22003"),
]


def load_cases():
    synthetic = json.loads((FIXTURES / "synthetic.json").read_text())
    concrete = [json.loads(line) for line in (FIXTURES / "concrete.jsonl").read_text().splitlines()]
    for name, cases in (("synthetic", synthetic), ("concrete", concrete)):
        assert len(cases) == len({case["id"] for case in cases}) == 50, name
        assert len({case["sql"] for case in cases}) == 50, name
    return synthetic, concrete


def validity(sql, types="", status="valid", tier="contract"):
    args = ["--assurance", tier, "--schema", str(FIXTURES / "schema.json")]
    if types:
        args += ["--param-types", types]
    args += [sql]
    columns = (("id", "int32" if tier == "contract" else "int", False),)
    return assert_report(args, status, tier, columns if status in {"valid", "checked"} else None)


def boundary_checks():
    checks = [
        ("SELECT id FROM page_rows LIMIT id", "", "invalid"),
        ("SELECT id AS n FROM page_rows LIMIT n", "", "invalid"),
        ("SELECT id FROM page_rows LIMIT TRUE", "", "invalid"),
        ("SELECT id FROM page_rows LIMIT $1", "bool", "invalid"),
        ("SELECT id FROM page_rows LIMIT $1", "text", "invalid"),
        ("SELECT id FROM page_rows LIMIT $2", "int", "invalid"),
        ("SELECT id FROM page_rows LIMIT CAST('2' AS TEXT)", "", "invalid"),
        ("SELECT id FROM page_rows LIMIT '2'", "", "unsupported"),
        ("SELECT id FROM page_rows LIMIT CAST(2 AS BIGINT)", "", "valid"),
        ("SELECT id FROM page_rows LIMIT (SELECT 2)", "", "valid"),
        ("SELECT id FROM page_rows LIMIT COUNT(*)", "", "unsupported"),
    ]
    for sql, types, status in checks:
        validity(sql, types, status)
    # Deliberately retain the narrower comma spelling: expression pagination
    # would reverse anonymous lexical slot identity when normalized to OFFSET.
    for sql in ("SELECT 1 LIMIT ?, ?", "SELECT 1 LIMIT $1, 2", "SELECT 1 LIMIT ALL"):
        result = subprocess.run([str(EXE), "--assurance", "syntax", sql], cwd=ROOT,
                                capture_output=True, text=True, timeout=30)
        assert result.returncode != 0, (sql, result.stdout)
    # v0.5 retains OFFSET-first layout explicitly, preserving parameter order.
    validity("SELECT id FROM page_rows OFFSET $1 LIMIT $2", "int,int")
    replay("sqlite", "SELECT 1 LIMIT 1, 2")
    for sql, types, _, _ in RUNTIME_CASES:
        validity(sql, types)
    return len(checks) + 5 + len(RUNTIME_CASES)


def prepare_capture(sql, types, values, *, error=False):
    """Capture actual EXECUTE, never substitute values into the SELECT text."""
    declarations = ", ".join(PG_TYPES[t.removesuffix("?")] for t in types.split(",") if t)
    declaration = f" ({declarations})" if declarations else ""
    execute = "EXECUTE pagination_parameters"
    if values:
        execute += " (" + ", ".join(map(literal, values)) + ")"
    if error:
        body = ("BEGIN EXECUTE " + sql_literal(execute) +
                "; RETURN 'unexpected-success'; EXCEPTION WHEN OTHERS THEN RETURN SQLSTATE; END;")
        function = ("CREATE OR REPLACE FUNCTION pg_temp.pagination_error() RETURNS TEXT "
                    "LANGUAGE plpgsql VOLATILE AS " + sql_literal(body) + ";")
        capture = copy_result("SELECT pg_temp.pagination_error()")
    else:
        body = "BEGIN RETURN QUERY EXECUTE " + sql_literal(execute) + "; END;"
        function = ("CREATE OR REPLACE FUNCTION pg_temp.pagination_rows() RETURNS TABLE (id INTEGER) "
                    "LANGUAGE plpgsql VOLATILE AS " + sql_literal(body) + ";")
        capture = copy_result("SELECT * FROM pg_temp.pagination_rows()")
    # The fixture adapter only changes ? markers, outside quoted data. Inputs
    # here are our synthetic statements, not arbitrary downloaded SQL.
    return [f"PREPARE pagination_parameters{declaration} AS {question_parameters(sql)}",
            function, capture]


def postgres_script(cases, rendered, errors):
    assert len(cases) == len(rendered), "missing rendered pagination case"
    assert len(errors) == len(RUNTIME_CASES), "missing rendered runtime boundary"
    commands = ["\\encoding UTF8", "BEGIN;", "SET LOCAL statement_timeout = '5s';",
                "SET LOCAL standard_conforming_strings = on;",
                "CREATE TEMP TABLE page_rows(id INTEGER NOT NULL);"]
    expected = {}
    for populated in (False, True):
        if populated:
            commands.append("INSERT INTO page_rows VALUES (1),(2),(3),(4),(5),(6);")
        for index, case in enumerate(cases, 1):
            for form, sql in (("source", case["sql"]), ("postgres", rendered[index - 1]["postgres"])):
                capture = prepare_capture(sql, case["parameter_types"], case["parameter_values"])
                key = marker("pagination", index, populated, form)
                commands += capture[:-1] + ["\\echo " + key, capture[-1],
                                           "DEALLOCATE pagination_parameters;"]
                rows = case["expected_rows"] if populated else []
                expected[key] = (1, [[str(cell) for cell in row] for row in rows])
    for index, ((sql, types, values, state), canonical) in enumerate(zip(RUNTIME_CASES, errors), 1):
        for form, source in (("source", sql), ("postgres", canonical)):
            capture = prepare_capture(source, types, values, error=True)
            key = marker("pagination_error", index, True, form)
            commands += capture[:-1] + ["\\echo " + key, capture[-1],
                                       "DEALLOCATE pagination_parameters;"]
            expected[key] = (1, [[state]])
    commands.append("ROLLBACK;")
    return "\n".join(commands), expected


def sqlite_bindings(sql, values):
    """Bind this finite corpus, whose numbered statements use every slot."""
    uses = parameters(sql, "sqlite")
    if not uses:
        assert not values
        return ()
    if uses[0][0] == "anonymous":
        assert all(style == "anonymous" for style, _ in uses)
        assert len(uses) == len(values)
        return tuple(values)
    # Named $2 occurring before $1 must not be bound by occurrence order.
    # SQLite accepts numeric string keys for both $N and emitted ?N markers.
    assert all(style == "numbered" for style, _ in uses)
    assert {slot for _, slot in uses} == set(range(1, len(values) + 1)), "fixture must use every declared slot"
    return {str(slot): value for slot, value in enumerate(values, 1)}


def sqlite_check(cases, rendered):
    assert len(cases) == len(rendered), "missing rendered SQLite case"
    count = 0
    with sqlite3.connect(":memory:") as db:
        db.execute("CREATE TABLE page_rows(id INTEGER NOT NULL)")
        for populated in (False, True):
            if populated:
                db.executemany("INSERT INTO page_rows VALUES (?)", [(n,) for n in range(1, 7)])
            for case, reports in zip(cases, rendered):
                variants = [("sqlite", reports["sqlite"])]
                variants.append(("sqlite_fixture", case["sqlite_sql"]))
                for form, sql in variants:
                    try:
                        cursor = db.execute(sql, sqlite_bindings(sql, case["parameter_values"]))
                        rows = [list(row) for row in cursor.fetchall()]
                    except sqlite3.IntegrityError as error:
                        assert case["sqlite_null_bound"], (case["id"], form, error)
                        assert error.sqlite_errorcode == sqlite3.SQLITE_MISMATCH, error
                    else:
                        assert not case["sqlite_null_bound"], (case["id"], form, "expected NULL-bound error")
                        assert len(cursor.description) == 1
                        assert rows == (case["expected_rows"] if populated else []), (case["id"], form, rows)
                    count += 1
        # Explicit cross-dialect runtime distinction, with separate bindings.
        for sql, values, expected in [
            ("SELECT id FROM page_rows ORDER BY id LIMIT ?", [-1], [[n] for n in range(1, 7)]),
            ("SELECT id FROM page_rows ORDER BY id LIMIT 2 OFFSET ?", [-1], [[1], [2]]),
        ]:
            for source in (sql, replay("sqlite", sql)["sql"]):
                rows = [list(row) for row in db.execute(source, sqlite_bindings(source, values))]
                assert rows == expected, (source, rows)
                count += 1
    return count


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    group = parser.add_mutually_exclusive_group(required=True)
    group.add_argument("--local-bin")
    group.add_argument("--dsn")
    parser.add_argument("--psql")
    args = parser.parse_args()
    synthetic, concrete = load_cases()
    rendered = []
    for case in synthetic:
        validity(case["sql"], case["parameter_types"])
        validity(case["sql"], case["parameter_types"], "checked", "checked")
        rendered.append({mode: replay(mode, case["sqlite_sql"] if mode == "sqlite" else case["sql"])["sql"]
                         for mode in ("identity", "postgres", "sqlite")})
    for case in concrete:
        for mode in ("identity", "postgres"):
            replay(mode, case["sql"])
    boundaries = boundary_checks()
    errors = [replay("postgres", sql)["sql"] for sql, _, _, _ in RUNTIME_CASES]
    sqlite_count = sqlite_check(synthetic, rendered)
    script, expected = postgres_script(synthetic, rendered, errors)
    with connection(args) as psql:
        result = run([*psql, "-X", "-q", "-v", "ON_ERROR_STOP=1"], input=script, timeout=120)
        actual = parse_results(result.stdout)
        assert actual.keys() == expected.keys(), (actual.keys() ^ expected.keys())
        for key, want in expected.items():
            assert actual[key] == want, (key, actual[key], want)
        version = run([*psql, "-X", "-At", "-c", "SHOW server_version;"]).stdout.strip()
    print("PASS: 50 full-validity synthetic SELECTs in 3 rendering profiles; "
          "50 unchanged concrete SELECTs in identity/PostgreSQL profiles; "
          "exact parameter maps and canonical rechecks")
    print(f"PASS: {boundaries} static/grammar boundaries; SQLite {sqlite3.sqlite_version}: "
          f"{sqlite_count} bound executions; PostgreSQL {version}: {len(expected)} real EXECUTE observations")
    print("Scope: full-query static validity for synthetic cases; external query bodies are not "
          "type-certified here. Native results are finite observations, not semantic equivalence proofs.")


if __name__ == "__main__":
    main()
