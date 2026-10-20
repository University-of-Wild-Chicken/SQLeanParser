#!/usr/bin/env python3
"""Verify JSONB containment typing, rendering and finite PostgreSQL observations."""
import argparse
import json

from check_array_types_cli import describe_script, validate_results, validity
from check_assurance_cli import assert_report, invoke
from check_extended_types_cli import database_script
from check_pagination_cli import ROOT, replay, prepare_capture
from check_postgresql_cli import connection, marker, parse_results, run, sql_literal
from check_renderer_corpus import parameters

FIXTURES = ROOT / "fixtures/json_containment"


def load_cases():
    rows = json.loads((FIXTURES / "synthetic.json").read_text())
    source = [json.loads(line) for line in (FIXTURES / "concrete.jsonl").read_text().splitlines()]
    for population in (rows, source):
        assert len(population) == len({row["id"] for row in population}) == len(
            {row["sql"] for row in population}) == 50
    for row in rows:
        assert row["source_kind"] == "synthetic"
        assert len(row["output_columns"]) == 1
        output = row["output_columns"][0]
        assert output["name"] == "v" and output["type"] == "bool"
        assert type(output["nullable"]) is bool
        assert row["postgres_type"] == row["postgres_display_type"] == "boolean"
        assert row["expected_value"] in ("true", "false", None)
        assert row["expected_value"] is not None or output["nullable"]
        assert row["sqlite_supported"] is False
        assert {slot for _, slot in parameters(row["sql"], "postgres")} == set(
            range(1, len(row["parameter_values"]) + 1))
        assert parameters(row["sql"], "postgres") == parameters(row["sqlite_input"], "sqlite")
    assert all(type(row["observed_syntax"]["source_free"]) is bool for row in source)
    assert sum(row["observed_syntax"]["source_free"] for row in source) == 42
    return rows, source


def operator_script():
    rows = json.loads((FIXTURES / "operator_signatures.json").read_text())
    fields = ("operator", "left", "right", "output", "function")
    wanted = {
        ("@>", "jsonb", "jsonb", "boolean", "jsonb_contains"),
        ("<@", "jsonb", "jsonb", "boolean", "jsonb_contained"),
    }
    assert len(rows) == 2 and {tuple(row[key] for key in fields) for row in rows} == wanted
    commands, expected = [], []
    for index, row in enumerate(rows):
        operator, left, right, output, function = map(sql_literal, (row[key] for key in fields))
        commands.append(
            f"SELECT {index}, EXISTS(SELECT FROM pg_catalog.pg_operator o "
            "JOIN pg_catalog.pg_proc p ON p.oid=o.oprcode "
            f"WHERE o.oprnamespace='pg_catalog'::regnamespace AND o.oprname={operator} "
            f"AND o.oprleft={left}::regtype AND o.oprright={right}::regtype "
            f"AND o.oprresult={output}::regtype AND p.prorettype={output}::regtype "
            f"AND p.proname={function} AND p.pronamespace='pg_catalog'::regnamespace "
            f"AND p.proargtypes[0]={left}::regtype AND p.proargtypes[1]={right}::regtype "
            "AND p.proisstrict AND NOT p.proretset AND p.pronargs=2 AND p.prokind='f');")
        expected.append(f"{index}|t")
    return "\n".join(commands), expected


def reject_sqlite(case):
    result = invoke(["--render-assurance", "sqlite"], stdin=case["sqlite_input"])
    report = json.loads(result.stdout)
    assert (result.returncode, report["status"], report["diagnostic"]["code"]) in {
        (1, "invalid", "input.parse"), (3, "unsupported", "coverage.sqlite.containment"),
    }, report


def runtime_cases():
    return [{
        "sql": f"SELECT {expression} AS v;", "parameter_types": "text",
        "parameter_values": [value],
        "output_columns": [{"name": "v", "type": "bool", "nullable": False}],
        "sqlstate": state,
    } for expression, value, state in (
        ("CAST($1 AS JSONB) @> '{}'", "bad json", "22P02"),
        ("'{}' <@ CAST($1 AS JSONB)", "bad json", "22P02"),
        ("CAST($1 AS JSONB) <@ '{}'::JSONB", r'{"a":"\u0000"}', "22P05"),
        ("'{}'::JSONB @> CAST($1 AS JSONB)", r'{"a":"\u0000"}', "22P05"),
    )]


def error_script(cases, canonical):
    assert len(cases) == len(canonical), "missing rendered containment runtime case"
    commands, expected = ["BEGIN;", "SET LOCAL statement_timeout = '5s';",
                          "SET LOCAL standard_conforming_strings = on;"], {}
    for index, (case, rendered) in enumerate(zip(cases, canonical), 1):
        for form, sql in (("source", case["sql"]), ("postgres", rendered)):
            capture = prepare_capture(sql, case["parameter_types"], case["parameter_values"], error=True)
            key = marker("containment_error", index, True, form)
            commands += [*capture[:-1], "\\echo " + key, capture[-1], "DEALLOCATE pagination_parameters;"]
            expected[key] = (1, [[case["sqlstate"]]])
    commands.append("ROLLBACK;")
    return "\n".join(commands), expected


def label_cases():
    return [{
        "sql": f"SELECT {expression};", "parameter_types": "", "parameter_values": [],
        "output_columns": [{"name": "?column?", "type": type_, "nullable": nullable}],
        "postgres_display_type": "boolean" if type_ == "bool" else "text",
    } for expression, type_, nullable in (
        ("'{}'::JSONB @> '{}'", "bool", False),
        ("'{}' <@ '{}'::JSONB", "bool", False),
        ("NULL::JSONB @> '{}'", "bool", True),
        ("'{}'::JSONB <@ NULL", "bool", True),
        ("'{}'::JSONB @> '{}' || 'x'", "text", False),
        ("'{}'::JSONB || '{}'::JSONB @> '{}'", "bool", False),
    )]


def boundaries():
    invalid = [
        f"SELECT {left} {operator} {right}"
        for operator in ("@>", "<@") for left, right in (
            ("'{}'", "'{}'"), ("NULL", "NULL"), ("'{}'::JSON", "'{}'"),
            ("'{}'::TEXT", "'{}'::JSONB"), ("'{}'::JSONB", "1"),
            ("TRUE", "'{}'::JSONB"),
        )
    ]
    valid = [
        "SELECT ARRAY[1] @> ARRAY[1]", "SELECT ARRAY[1] <@ ARRAY[1]",
        "SELECT ARRAY[1] @> '{1}'", "SELECT '{1}' <@ ARRAY[1]",
    ]
    invalid.append("SELECT ARRAY[1] @> ARRAY[1::BIGINT]")
    unsupported = [
        "SELECT (SELECT '{}'::JSONB) @> '{}'", "SELECT unknown_function() <@ '{}'::JSONB",
    ]
    syntax = [
        "SELECT '{}'::JSONB @>", "SELECT <@ '{}'::JSONB",
        "SELECT '{}'::JSONB @>> '{}'", "SELECT '{}'::JSONB @>-1",
        "SELECT '{}'::JSONB ? 'a'", "SELECT '{}'::JSONB @@ '$.a'",
    ]
    for status, queries in (("invalid", invalid), ("unsupported", unsupported), ("valid", valid)):
        for sql in queries:
            assert_report(["--assurance", "contract", sql], status, "contract")
    for sql in syntax:
        result = invoke(["--render-assurance", "identity", sql])
        report = json.loads(result.stdout)
        assert (result.returncode, report["status"], report["diagnostic"]["code"]) == (
            1, "invalid", "input.parse"), report
    assert_report(["--assurance", "checked", "SELECT '{}'::JSONB @> '{}'"], "rejected", "checked")
    return len(invalid) + len(unsupported) + len(valid) + len(syntax) + 1


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    target = parser.add_mutually_exclusive_group(required=True)
    target.add_argument("--local-bin")
    target.add_argument("--dsn")
    parser.add_argument("--psql")
    args = parser.parse_args()
    rows, source = load_cases()
    postgres = []
    for row in rows:
        validity(row)
        replay("identity", row["sql"])
        postgres.append(replay("postgres", row["sql"])["sql"])
        reject_sqlite(row)
    for row in source:
        if row["observed_syntax"]["source_free"]:
            assert_report(["--assurance", "contract", row["sql"]], "valid", "contract",
                          (("?column?", "bool", False),))
        for profile in ("identity", "postgres"):
            replay(profile, row["sql"])
    errors, labels = runtime_cases(), label_cases()
    error_rendered, label_rendered = [], []
    for cases, rendered in ((errors, error_rendered), (labels, label_rendered)):
        for case in cases:
            validity(case)
            rendered.append(replay("postgres", case["sql"])["sql"])
    boundary_count = boundaries()
    values_sql, values = database_script(rows, postgres)
    metadata_sql, metadata = describe_script(rows + labels, postgres + label_rendered)
    errors_sql, expected_errors = error_script(errors, error_rendered)
    operators_sql, operators = operator_script()
    with connection(args) as psql:
        for script, expected in ((values_sql, values), (errors_sql, expected_errors)):
            result = run([*psql, "-X", "-q", "-v", "ON_ERROR_STOP=1"], input=script, timeout=120)
            validate_results(parse_results(result.stdout), expected)
        for script, expected in ((metadata_sql, metadata), (operators_sql, operators)):
            result = run([*psql, "-X", "-qAt", "-v", "ON_ERROR_STOP=1"], input=script, timeout=120)
            assert result.stdout.splitlines() == expected, (result.stdout.splitlines(), expected)
        version = run([*psql, "-X", "-At", "-c", "SHOW server_version;"]).stdout.strip()
    print("PASS: 50 JSONB containment synthetic certificates; 50 source renderings and 42 source certificates")
    print(f"PASS: {boundary_count} boundaries and 50 explicit SQLite dialect exclusions")
    print(f"PASS: PostgreSQL {version}: {len(values)} value/OID observations, {len(metadata)} descriptors")
    print(f"PASS: {len(expected_errors)} expected errors and {len(operators)} native overloads")
    print("Scope: exact JSONB signatures and finite native observations; concrete source SQL is never executed.")


if __name__ == "__main__":
    main()
