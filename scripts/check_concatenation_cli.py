#!/usr/bin/env python3
"""Verify scalar concatenation contracts and separate PostgreSQL/SQLite results."""
import argparse
import json
import sqlite3

from check_array_types_cli import describe_script, validate_results, validity
from check_assurance_cli import assert_report, invoke
from check_extended_types_cli import database_script
from check_pagination_cli import ROOT, replay, prepare_capture, sqlite_bindings
from check_postgresql_cli import connection, marker, parse_results, run, sql_literal
from check_renderer_corpus import parameters

FIXTURES = ROOT / "fixtures/concatenation"


def load_cases():
    rows = json.loads((FIXTURES / "synthetic.json").read_text())
    source = [json.loads(line) for line in (FIXTURES / "concrete.jsonl").read_text().splitlines()]
    for population in (rows, source):
        assert len(population) == len({row["id"] for row in population}) == len({row["sql"] for row in population}) == 50
    for row in rows:
        assert len(row["output_columns"]) == 1
        output = row["output_columns"][0]
        assert output["name"] == "v" and output["type"] in {"text", "jsonb", "bytea"}
        assert type(output["nullable"]) is bool
        assert {slot for _, slot in parameters(row["sql"], "postgres")} == set(
            range(1, len(row["parameter_values"]) + 1))
        assert parameters(row["sql"], "postgres") == parameters(row["sqlite_input"], "sqlite")
        if row["sqlite_sql"] is not None:
            assert row["sqlite_supported"]
            assert parameters(row["sql"], "postgres") == parameters(row["sqlite_sql"], "sqlite")
    assert sum(row["sqlite_supported"] for row in rows) == 25
    assert sum(row["sqlite_sql"] is not None for row in rows) == 15
    return rows, source


def operator_script():
    rows = json.loads((FIXTURES / "operator_signatures.json").read_text())
    wanted = {
        ("text", "text", "text", "textcat"),
        ("text", "anynonarray", "text", "textanycat"),
        ("anynonarray", "text", "text", "anytextcat"),
        ("jsonb", "jsonb", "jsonb", "jsonb_concat"),
        ("bytea", "bytea", "bytea", "byteacat"),
    }
    assert len(rows) == 5 and {tuple(row[key] for key in ("left", "right", "output", "function"))
                               for row in rows} == wanted
    assert all(row["operator"] == "||" for row in rows)
    commands, expected = [], []
    for index, row in enumerate(rows):
        left, right, output, function = map(sql_literal, (row["left"], row["right"], row["output"], row["function"]))
        commands.append(
            f"SELECT {index}, EXISTS(SELECT FROM pg_catalog.pg_operator o "
            "JOIN pg_catalog.pg_proc p ON p.oid=o.oprcode "
            "WHERE o.oprnamespace='pg_catalog'::regnamespace AND o.oprname='||' "
            f"AND o.oprleft={left}::regtype AND o.oprright={right}::regtype "
            f"AND o.oprresult={output}::regtype AND p.prorettype={output}::regtype "
            f"AND p.proname={function} AND p.pronamespace='pg_catalog'::regnamespace "
            f"AND p.proargtypes[0]={left}::regtype AND p.proargtypes[1]={right}::regtype "
            "AND p.proisstrict AND NOT p.proretset AND p.pronargs=2 AND p.prokind='f');")
        expected.append(f"{index}|t")
    return "\n".join(commands), expected


def sqlite_render(case):
    if case["sqlite_supported"]:
        return replay("sqlite", case["sqlite_input"])["sql"]
    result = invoke(["--render-assurance", "sqlite"], stdin=case["sqlite_input"])
    report = json.loads(result.stdout)
    code = report["diagnostic"]["code"]
    assert ((result.returncode, report["status"], code) == (1, "invalid", "input.parse") or
            (result.returncode, report["status"]) == (3, "unsupported") and
            code.startswith("coverage.sqlite.")), report
    return None


def sqlite_observations(cases, canonical):
    assert len(cases) == len(canonical), "missing rendered SQLite concatenation"
    count = 0
    with sqlite3.connect(":memory:") as db:
        for case, rendered in zip(cases, canonical):
            assert (rendered is not None) == case["sqlite_supported"]
            if rendered is None:
                continue
            for sql in (case["sqlite_sql"], rendered):
                if sql is None:
                    continue
                cursor = db.execute(sql, sqlite_bindings(sql, case["parameter_values"]))
                assert [column[0] for column in cursor.description] == ["v"], cursor.description
                actual = cursor.fetchall()
                # This intentionally permits INTEGER output for SQLite's
                # different precedence tree; its oracle is independently authored.
                assert actual == [(case["sqlite_value"],)], (case["id"], sql, actual, case["sqlite_value"])
                count += 1
    return count


def runtime_cases():
    examples = [
        ("CAST($1 AS JSONB) || '{}'::JSONB", "text", ["bad json"], "jsonb", "22P02"),
        ("CAST($1 AS BYTEA) || '\\x61'::BYTEA", "text", ["\\xzz"], "bytea", "22023"),
        ("CAST($1 AS INTEGER) || 'x'", "text", ["bad integer"], "text", "22P02"),
        ("CAST($1 AS INTEGER) || 'x'", "text", ["2147483648"], "text", "22003"),
        ("'x' || (1/$1)", "int", [0], "text", "22012"),
    ]
    return [{
        "sql": f"SELECT {expr} AS v;", "parameter_types": types, "parameter_values": values,
        "output_columns": [{"name": "v", "type": type_, "nullable": False}], "sqlstate": state,
    } for expr, types, values, type_, state in examples]


def error_script(cases, canonical):
    assert len(cases) == len(canonical), "missing rendered concatenation runtime case"
    commands, expected = ["BEGIN;"], {}
    for index, (case, rendered) in enumerate(zip(cases, canonical), 1):
        for form, sql in (("source", case["sql"]), ("postgres", rendered)):
            capture = prepare_capture(sql, case["parameter_types"], case["parameter_values"], error=True)
            key = marker("concatenation_error", index, True, form)
            commands += [*capture[:-1], "\\echo " + key, capture[-1], "DEALLOCATE pagination_parameters;"]
            expected[key] = (1, [[case["sqlstate"]]])
    commands.append("ROLLBACK;")
    return "\n".join(commands), expected


def label_cases():
    return [{
        "sql": f"SELECT {expression};", "parameter_types": "", "parameter_values": [],
        "output_columns": [{"name": "?column?", "type": type_, "nullable": False}],
        "postgres_display_type": type_,
    } for expression, type_ in (
        ("'a' || 'b'", "text"), ("'x'::TEXT || 1", "text"), ("1 || 'x'::TEXT", "text"),
        ("'{}'::JSONB || '{}'::JSONB", "jsonb"), (r"'\x61'::BYTEA || '\x62'::BYTEA", "bytea"))]


def boundaries():
    invalid = [
        "SELECT 1 || 2", "SELECT 1.2 || 2.3", "SELECT TRUE || FALSE",
        "SELECT '{}'::JSON || '{}'::JSON", "SELECT '{}'::JSONB || 1",
        "SELECT '\\x61'::BYTEA || 1", "SELECT '{}'::JSONB || '\\x61'::BYTEA",
    ]
    unsupported = [
        "SELECT ARRAY[1] || ARRAY[2]", "SELECT ARRAY[1] || 2", "SELECT 1 || ARRAY[2]",
        "SELECT 'x'::TEXT || ARRAY[1]", "SELECT ROW(1,2) || 'x'::TEXT",
        "SELECT (SELECT 'x') || 'y'",
    ]
    syntax = ["SELECT 'x' | 'y'", "SELECT 'x' ||| 'y'", "SELECT 'x' ||"]
    for status, queries in (("invalid", invalid), ("unsupported", unsupported)):
        for sql in queries:
            assert_report(["--assurance", "contract", sql], status, "contract")
    for sql in syntax:
        result = invoke(["--render-assurance", "identity", sql])
        report = json.loads(result.stdout)
        assert (result.returncode, report["status"], report["diagnostic"]["code"]) == (1, "invalid", "input.parse"), report
    assert_report(["--assurance", "checked", "SELECT 'x' || 'y'"], "rejected", "checked")
    return len(invalid) + len(unsupported) + len(syntax) + 1


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    target = parser.add_mutually_exclusive_group(required=True)
    target.add_argument("--local-bin")
    target.add_argument("--dsn")
    parser.add_argument("--psql")
    args = parser.parse_args()
    rows, source = load_cases()
    postgres, sqlite = [], []
    for row in rows:
        validity(row)
        replay("identity", row["sql"])
        postgres.append(replay("postgres", row["sql"])["sql"])
        sqlite.append(sqlite_render(row))
    for row in source:
        for profile in ("identity", "postgres"):
            replay(profile, row["sql"])
    errors, labels = runtime_cases(), label_cases()
    error_rendered, label_rendered = [], []
    for cases, rendered in ((errors, error_rendered), (labels, label_rendered)):
        for case in cases:
            validity(case)
            rendered.append(replay("postgres", case["sql"])["sql"])
    boundary_count = boundaries()
    sqlite_count = sqlite_observations(rows, sqlite)
    values_sql, values = database_script(rows, postgres)
    metadata_sql, metadata = describe_script(rows + labels, postgres + label_rendered)
    errors_sql, expected_errors = error_script(errors, error_rendered)
    operators_sql, operators = operator_script()
    with connection(args) as psql:
        result = run([*psql, "-X", "-q", "-v", "ON_ERROR_STOP=1"], input=values_sql, timeout=120)
        validate_results(parse_results(result.stdout), values)
        for script, expected in ((metadata_sql, metadata), (operators_sql, operators)):
            result = run([*psql, "-X", "-qAt", "-v", "ON_ERROR_STOP=1"], input=script, timeout=120)
            assert result.stdout.splitlines() == expected, (result.stdout.splitlines(), expected)
        result = run([*psql, "-X", "-q", "-v", "ON_ERROR_STOP=1"], input=errors_sql, timeout=120)
        validate_results(parse_results(result.stdout), expected_errors)
        version = run([*psql, "-X", "-At", "-c", "SHOW server_version;"]).stdout.strip()
    print("PASS: 50 concatenation certificates and 50 unchanged source renderings")
    print(f"PASS: {boundary_count} boundaries; PostgreSQL {version}: {len(values)} value/OID observations")
    print(f"PASS: {len(metadata)} descriptors, {len(expected_errors)} expected errors and {len(operators)} native overloads")
    print(f"PASS: SQLite {sqlite3.sqlite_version}: {sqlite_count} observations and 25 dialect exclusions")
    print("Scope: exact static signatures and separate finite dialect observations; concrete source SQL is never executed.")


if __name__ == "__main__":
    main()
