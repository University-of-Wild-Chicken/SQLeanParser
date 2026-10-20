#!/usr/bin/env python3
"""Check SUBSTRING contracts, source-order bindings and native observations."""
import argparse
import json

from check_array_types_cli import describe_script, validate_results, validity
from check_assurance_cli import assert_report, invoke
from check_extended_types_cli import database_script
from check_extract_cli import error_script, null_script
from check_pagination_cli import ROOT, replay
from check_postgresql_cli import connection, parse_results, run, sql_literal
from check_renderer_corpus import parameters

FIXTURES = ROOT / "fixtures/substring"
SIGNATURES = {
    (("text", "integer"), "text"), (("text", "integer", "integer"), "text"),
    (("bytea", "integer"), "bytea"), (("bytea", "integer", "integer"), "bytea"),
    (("text", "text"), "text"), (("text", "text", "text"), "text"),
}


def load_cases():
    rows = json.loads((FIXTURES / "synthetic.json").read_text())
    source = [json.loads(line) for line in (FIXTURES / "concrete.jsonl").read_text().splitlines()]
    for population in (rows, source):
        assert len(population) == len({row["id"] for row in population}) == len(
            {row["sql"] for row in population}) == 50
    for row in rows:
        assert row["source_kind"] == "synthetic" and row["sqlite_supported"] is False
        assert len(row["output_columns"]) == 1
        output = row["output_columns"][0]
        assert output["name"] == "v" and type(output["nullable"]) is bool
        assert output["type"] in ("text", "bytea")
        assert output["type"] == row["postgres_type"] == row["postgres_display_type"]
        assert row["expected_value"] is None or isinstance(row["expected_value"], str)
        assert row["expected_value"] is not None or output["nullable"]
        assert {slot for _, slot in parameters(row["sql"], "postgres")} == set(
            range(1, len(row["parameter_values"]) + 1))
        assert parameters(row["sql"], "postgres") == parameters(row["sqlite_input"], "sqlite")
    for row in source:
        assert row["raw_sql"] == row["sql"] and row["transformations"] == []
        assert row["observed_syntax"]["source_free"] is True
        assert row["parameter_types"] is None
    return rows, source


def function_script():
    rows = json.loads((FIXTURES / "function_signatures.json").read_text())
    assert len(rows) == 6
    assert all(row["name"] == "substring" for row in rows)
    assert {(tuple(row["inputs"]), row["output"]) for row in rows} == SIGNATURES
    commands, expected = [], []
    for index, row in enumerate(rows):
        inputs = "ARRAY[" + ",".join(sql_literal(type_) + "::regtype::oid"
                                     for type_ in row["inputs"]) + "]::oid[]"
        commands.append(
            f"SELECT {index}, EXISTS(SELECT FROM pg_catalog.pg_proc p "
            "WHERE p.pronamespace='pg_catalog'::regnamespace AND p.proname='substring' "
            f"AND ARRAY(SELECT unnest(p.proargtypes::oid[]))={inputs} "
            f"AND p.prorettype={sql_literal(row['output'])}::regtype "
            "AND p.provolatile='i' AND p.prokind='f' AND p.proisstrict AND NOT p.proretset);")
        expected.append(f"{index}|t")
    return "\n".join(commands), expected


def null_shortcuts():
    return [{
        "sql": f"SELECT {expr} AS v;", "parameter_types": "", "parameter_values": [],
        "output_columns": [{"name": "v", "type": type_, "nullable": True}],
        "postgres_type": type_, "postgres_display_type": type_, "expected_value": None,
    } for expr, type_ in (
        ("SUBSTRING(NULL::TEXT FROM '[')", "text"),
        ("SUBSTRING(NULL::TEXT SIMILAR '%' ESCAPE 'xx')", "text"),
        ("SUBSTRING(NULL::BYTEA FROM 1 FOR -1)", "bytea"),
        ("SUBSTRING('abcdef' FROM NULL::INTEGER FOR -1)", "text"),
    )]


def runtime_cases():
    return [{
        "sql": f"SELECT {expr} AS v;", "parameter_types": types, "parameter_values": values,
        "output_columns": [{"name": "v", "type": type_, "nullable": nullable}], "sqlstate": state,
    } for expr, types, values, type_, nullable, state in (
        ("SUBSTRING($1 FROM 1 FOR $2)", "text,int", ["abcdef", -1], "text", False, "22011"),
        ("SUBSTRING($1 FROM $2)", "text,text", ["abcdef", "["], "text", True, "2201B"),
        ("SUBSTRING($1 SIMILAR '%' ESCAPE $2)", "text,text", ["abcdef", "xx"], "text", True, "22025"),
        ("SUBSTRING($1 SIMILAR $2 ESCAPE '#')", "text,text", ["abcdef", "["], "text", True, "2201B"),
        ("SUBSTRING($1 FOR $2)", "text,text", ["abcdef", "bad"], "text", False, "22P02"),
        ("SUBSTRING($1 FOR CAST($2 AS BIGINT))", "text,text",
         ["abcdef", "2147483648"], "text", False, "22003"),
        ("SUBSTRING($1 FOR CAST($2 AS JSONB))", "text,text", ["abcdef", "null"], "text", True, "22023"),
        ("SUBSTRING(CAST($1 AS BYTEA) FOR CAST($2 AS JSONB))", "text,text",
         ["abcdef", '"x"'], "bytea", True, "22023"),
    )]


def label_cases():
    return [{
        "sql": f"SELECT {expr};", "parameter_types": "", "parameter_values": [],
        "output_columns": [{"name": name, "type": type_, "nullable": nullable}],
        "postgres_display_type": type_.replace("varchar", "character varying"),
    } for expr, name, type_, nullable in (
        ("SUBSTRING('abcdef' FROM 2)", "substring", "text", False),
        ("SUBSTRING('abcdef' FOR 3 FROM 2)", "substring", "text", False),
        ("SUBSTRING('abcdef' FROM 'bc.')", "substring", "text", True),
        ("substring('abcdef',2,3)", "substring", "text", False),
        ("pg_catalog.substring('abcdef','bc.')", "substring", "text", True),
        ("CAST(SUBSTRING('abcdef' FROM 2) AS VARCHAR(2))", "substring", "varchar(2)", False),
        ("CASE WHEN TRUE THEN 'abc' ELSE SUBSTRING('abcdef' FROM 2) END",
         "substring", "text", False),
        ("COALESCE(SUBSTRING('abcdef' FROM 'xyz'),'fallback')", "coalesce", "text", False),
    )]


def reject_sqlite(case):
    result = invoke(["--render-assurance", "sqlite"], stdin=case["sqlite_input"])
    report = json.loads(result.stdout)
    assert (result.returncode, report["status"], report["diagnostic"]["code"]) in {
        (1, "invalid", "input.parse"),
        (3, "unsupported", "coverage.sqlite.substring"),
        (3, "unsupported", "coverage.sqlite.scalar-function-signatures"),
    }, report


def boundaries():
    invalid = [
        "SELECT SUBSTRING()", "SELECT SUBSTRING('abc')",
        "SELECT SUBSTRING('abc' FROM 1::BIGINT)",
        "SELECT SUBSTRING('abc' FROM 1.2)",
        "SELECT SUBSTRING('abc' FROM TRUE)",
        "SELECT SUBSTRING('abc' FROM 1 FOR '2'::TEXT)",
        "SELECT SUBSTRING('abc'::BYTEA FROM 'x'::TEXT)",
        "SELECT SUBSTRING(1 FROM 2)",
        "SELECT SUBSTRING('abc' FOR DATE '2024-01-01')",
        "SELECT substr('abc','b'::TEXT)",
    ]
    unsupported = [
        "SELECT SUBSTRING((SELECT 'abc') FROM 2)",
        "SELECT SUBSTRING(unknown_function() FROM 2)",
        "SELECT private.substring('abc',2)",
    ]
    for status, queries in (("invalid", invalid), ("unsupported", unsupported)):
        for sql in queries:
            assert_report(["--assurance", "contract", sql], status, "contract")
    syntax = [
        "SELECT SUBSTRING('abc' FROM)", "SELECT SUBSTRING('abc' FOR)",
        "SELECT SUBSTRING('abc' SIMILAR 'b')",
        "SELECT SUBSTRING('abc' SIMILAR '%' ESCAPE)",
        "SELECT SUBSTRING('abc' FROM 1,2)",
        "SELECT SUBSTRING('abc',1 FOR 2)",
        "SELECT SUBSTRING('abc' FROM 1 FOR 2 FROM 3)",
        "SELECT SUBSTRING('abc' FOR 2 FOR 3)",
        "SELECT SUBSTRING('abc' ESCAPE '#')",
        "SELECT SUBSTRING('abc' FROM 1)[1]",
    ]
    for sql in syntax:
        result = invoke(["--render-assurance", "identity", sql])
        report = json.loads(result.stdout)
        assert (result.returncode, report["status"], report["diagnostic"]["code"]) == (
            1, "invalid", "input.parse"), report
    return len(invalid) + len(unsupported) + len(syntax)


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
    # Downloaded queries receive certificates only; execution uses authored cases.
    for row in source:
        assert_report(["--assurance", "contract", row["sql"]], "valid", "contract")
        for profile in ("identity", "postgres"):
            replay(profile, row["sql"])
    errors, labels, shortcuts = runtime_cases(), label_cases(), null_shortcuts()
    error_rendered, label_rendered, shortcut_rendered = [], [], []
    for population, rendered in ((errors, error_rendered), (labels, label_rendered),
                                 (shortcuts, shortcut_rendered)):
        for case in population:
            validity(case)
            rendered.append(replay("postgres", case["sql"])["sql"])
    boundary_count = boundaries()
    values_sql, values = database_script(rows + shortcuts, postgres + shortcut_rendered)
    nulls_sql, nulls = null_script(rows + shortcuts, postgres + shortcut_rendered)
    metadata_sql, metadata = describe_script(rows + shortcuts + labels,
                                            postgres + shortcut_rendered + label_rendered)
    errors_sql, expected_errors = error_script(errors, error_rendered)
    functions_sql, functions = function_script()
    with connection(args) as psql:
        for script, expected in ((values_sql, values), (nulls_sql, nulls), (errors_sql, expected_errors)):
            result = run([*psql, "-X", "-q", "-v", "ON_ERROR_STOP=1"], input=script, timeout=120)
            validate_results(parse_results(result.stdout), expected)
        for script, expected in ((metadata_sql, metadata), (functions_sql, functions)):
            result = run([*psql, "-X", "-qAt", "-v", "ON_ERROR_STOP=1"], input=script, timeout=120)
            assert result.stdout.splitlines() == expected, (result.stdout.splitlines(), expected)
        version = run([*psql, "-X", "-At", "-c", "SHOW server_version;"]).stdout.strip()
    print("PASS: 50 synthetic and 50 unchanged source SUBSTRING certificates/renderings")
    print(f"PASS: {boundary_count} boundaries, 4 NULL short-circuits and 50 SQLite exclusions")
    print(f"PASS: PostgreSQL {version}: {len(values)} values/OIDs, {len(nulls)} SQL-NULL observations, "
          f"{len(metadata)} exact prepared descriptors")
    print(f"PASS: {len(expected_errors)} expected errors and {len(functions)} native declarations")
    print("Scope: finite authored executions; conversions, regex syntax and length errors remain runtime obligations.")


if __name__ == "__main__":
    main()
