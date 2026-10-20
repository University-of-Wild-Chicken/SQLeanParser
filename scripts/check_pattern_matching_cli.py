#!/usr/bin/env python3
"""Verify ILIKE/regex static contracts, rendering, and finite native observations."""
import argparse
import json

from check_array_types_cli import describe_script, validate_results, validity
from check_assurance_cli import assert_report, invoke
from check_extended_types_cli import database_script
from check_pagination_cli import ROOT, replay, prepare_capture
from check_postgresql_cli import connection, marker, parse_results, run, sql_literal
from check_renderer_corpus import parameters


def load_cases():
    synthetic, concrete = [], []
    for factor in ("ilike", "regex"):
        directory = ROOT / "fixtures" / factor
        rows = json.loads((directory / "synthetic.json").read_text())
        source = [json.loads(line) for line in (directory / "concrete.jsonl").read_text().splitlines()]
        for population in (rows, source):
            assert len(population) == len({row["id"] for row in population}) == len(
                {row["sql"] for row in population}) == 50
        for row in rows:
            assert row["source_kind"] == "synthetic"
            assert len(row["output_columns"]) == 1
            output = row["output_columns"][0]
            assert output["name"] == "v" and output["type"] in {"bool", "text"}
            assert type(output["nullable"]) is bool
            native = "boolean" if output["type"] == "bool" else "text"
            assert row["postgres_type"] == row["postgres_display_type"] == native
            assert row["expected_value"] is None or isinstance(row["expected_value"], str)
            assert row["expected_value"] is not None or output["nullable"]
            assert row["sqlite_supported"] is False
            assert {slot for _, slot in parameters(row["sql"], "postgres")} == set(
                range(1, len(row["parameter_values"]) + 1))
            assert parameters(row["sql"], "postgres") == parameters(row["sqlite_input"], "sqlite")
        synthetic.extend(rows)
        concrete.extend(source)
    return synthetic, concrete


def operator_script():
    rows = json.loads((ROOT / "fixtures/pattern_matching/operator_signatures.json").read_text())
    wanted = {
        (operator, left, "text", "boolean", left + function)
        for operator, function in (("~~*", "iclike"), ("~", "regexeq"), ("~*", "icregexeq"),
                                   ("!~", "regexne"), ("!~*", "icregexne"))
        for left in ("text", "bpchar")
    }
    fields = ("operator", "left", "right", "output", "function")
    assert len(rows) == 10 and {tuple(row[key] for key in fields) for row in rows} == wanted
    # Native NOT ILIKE selects !~~*, while our existing AST normalizes it to
    # NOT(ILIKE). These two extra signatures support the finite normalization
    # checks and are not invented members of the ten-entry Lean inventory.
    rows = rows + [
        dict(operator="!~~*", left=left, right="text", output="boolean", function=left + "icnlike")
        for left in ("text", "bpchar")
    ]
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
    actual = result.returncode, report["status"], report["diagnostic"]["code"]
    assert actual in {
        (1, "invalid", "input.parse"),
        (3, "unsupported", "coverage.sqlite.ILIKE"),
        (3, "unsupported", "coverage.sqlite.regex"),
    }, report


def runtime_cases():
    return [{
        "sql": f"SELECT 'abcd' {operator} $1 AS v;", "parameter_types": "text",
        "parameter_values": [pattern],
        "output_columns": [{"name": "v", "type": "bool", "nullable": False}],
        "sqlstate": state,
    } for operator, pattern, state in (
        ("~", "[", "2201B"), ("~*", "(", "2201B"),
        ("!~", "[", "2201B"), ("!~*", "(", "2201B"),
        ("ILIKE", "abc\\", "22025"), ("NOT ILIKE", "abc\\", "22025"),
    )]


def error_script(cases, canonical):
    assert len(cases) == len(canonical), "missing rendered pattern runtime case"
    commands, expected = ["BEGIN;"], {}
    for index, (case, rendered) in enumerate(zip(cases, canonical), 1):
        for form, sql in (("source", case["sql"]), ("postgres", rendered)):
            capture = prepare_capture(sql, case["parameter_types"], case["parameter_values"], error=True)
            key = marker("pattern_error", index, True, form)
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
        ("'abc' ILIKE 'A%'", "bool", False),
        ("'abc' NOT ILIKE 'A%'", "bool", False),
        ("'abc'::CHAR(5) ~ '^abc$'", "bool", False),
        ("'abc' ~* 'ABC'", "bool", False),
        ("'abc' !~ '^z'", "bool", False),
        ("'abc' !~* '^Z'", "bool", False),
        ("NULL ~ '['", "bool", True),
        ("'abc' ~ 'a' || 'bc'", "text", False),
    )]


def boundaries():
    invalid = [
        f"SELECT {left} {operator} {right}"
        for operator in ("ILIKE", "~", "~*", "!~", "!~*")
        for left, right in (
            ("1", "'x'"), ("'x'", "1"), ("TRUE", "'x'"),
            ("'x'::BYTEA", "'x'::BYTEA"), ("'{}'::JSONB", "'x'"),
            ("ARRAY['x']", "'x'"),
        )
    ]
    unsupported = [
        "SELECT (SELECT 'x') ~ 'x'", "SELECT 'x' ILIKE (SELECT 'x')",
        "SELECT ROW('x') ~ 'x'", "SELECT unknown_function() ILIKE 'x'",
    ]
    syntax = [
        "SELECT 'x' ~", "SELECT ~ 'x'", "SELECT 'x' !~*",
        "SELECT 'x' ~** 'y'", "SELECT 'x' !~~ 'y'",
        "SELECT 'x' ILIKE 'y' ESCAPE '#'",
    ]
    for status, queries in (("invalid", invalid), ("unsupported", unsupported)):
        for sql in queries:
            assert_report(["--assurance", "contract", sql], status, "contract")
    for sql in syntax:
        result = invoke(["--render-assurance", "identity", sql])
        report = json.loads(result.stdout)
        assert (result.returncode, report["status"], report["diagnostic"]["code"]) == (
            1, "invalid", "input.parse"), report
    # Coarse expanded typing must not silently erase the exact regex signature.
    assert_report(["--assurance", "checked", "SELECT 'x' ~ 'x'"], "rejected", "checked")
    return len(invalid) + len(unsupported) + len(syntax) + 1


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
        result = run([*psql, "-X", "-q", "-v", "ON_ERROR_STOP=1"], input=values_sql, timeout=120)
        validate_results(parse_results(result.stdout), values)
        for script, expected in ((metadata_sql, metadata), (operators_sql, operators)):
            result = run([*psql, "-X", "-qAt", "-v", "ON_ERROR_STOP=1"], input=script, timeout=120)
            assert result.stdout.splitlines() == expected, (result.stdout.splitlines(), expected)
        result = run([*psql, "-X", "-q", "-v", "ON_ERROR_STOP=1"], input=errors_sql, timeout=120)
        validate_results(parse_results(result.stdout), expected_errors)
        version = run([*psql, "-X", "-At", "-c", "SHOW server_version;"]).stdout.strip()
    print("PASS: 50 ILIKE + 50 regex certificates; 50 unchanged source renderings per factor")
    print(f"PASS: {boundary_count} boundaries and 100 explicit SQLite dialect exclusions")
    print(f"PASS: PostgreSQL {version}: {len(values)} value/OID observations, {len(metadata)} descriptors")
    print(f"PASS: {len(expected_errors)} expected errors and {len(operators)} native overload checks")
    print("Scope: exact static signatures and finite native observations; concrete source SQL is never executed.")


if __name__ == "__main__":
    main()
