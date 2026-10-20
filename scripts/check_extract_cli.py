#!/usr/bin/env python3
"""Verify EXTRACT certificates, rendering and finite native PostgreSQL observations."""
import argparse
import json

from check_advanced_cli import literal, question_parameters
from check_array_types_cli import describe_script, validate_results, validity
from check_assurance_cli import assert_report, invoke
from check_extended_types_cli import database_script
from check_pagination_cli import ROOT, replay, prepare_capture
from check_postgresql_cli import connection, copy_result, marker, parse_results, run, sql_literal
from check_renderer_corpus import parameters

FIXTURES = ROOT / "fixtures/extract"
TEMPORAL = {"date", "time", "time with time zone", "timestamp", "timestamp with time zone", "interval"}


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
        assert output["name"] == "v" and output["type"] == "numeric"
        assert type(output["nullable"]) is bool
        assert row["postgres_type"] == row["postgres_display_type"] == "numeric"
        assert row["expected_value"] is None or isinstance(row["expected_value"], str)
        assert row["expected_value"] is not None or output["nullable"]
        assert {slot for _, slot in parameters(row["sql"], "postgres")} == set(
            range(1, len(row["parameter_values"]) + 1))
        assert parameters(row["sql"], "postgres") == parameters(row["sqlite_input"], "sqlite")
    assert all(row["observed_syntax"]["source_free"] is True for row in source)
    return rows, source


def function_script():
    rows = json.loads((FIXTURES / "function_signatures.json").read_text())
    assert len(rows) == 6
    assert {(row["name"], tuple(row["inputs"]), row["output"]) for row in rows} == {
        ("extract", ("text", temporal), "numeric") for temporal in TEMPORAL}
    commands, expected = [], []
    for index, row in enumerate(rows):
        name, output = sql_literal(row["name"]), sql_literal(row["output"])
        left, right = map(sql_literal, row["inputs"])
        volatility = "'s'" if row["inputs"][1] == "timestamp with time zone" else "'i'"
        commands.append(
            f"SELECT {index}, EXISTS(SELECT FROM pg_catalog.pg_proc p "
            f"WHERE p.pronamespace='pg_catalog'::regnamespace AND p.proname={name} "
            f"AND p.proargtypes[0]={left}::regtype AND p.proargtypes[1]={right}::regtype "
            f"AND p.prorettype={output}::regtype AND p.provolatile={volatility} "
            "AND p.pronargs=2 AND p.prokind='f' AND p.proisstrict AND NOT p.proretset);")
        expected.append(f"{index}|t")
    return "\n".join(commands), expected


def null_shortcuts():
    """Unrecognized fields are runtime obligations, suppressed by a NULL argument."""
    return [{
        "sql": f"SELECT EXTRACT('not a unit' FROM NULL::{temporal}) AS v;",
        "parameter_types": "", "parameter_values": [],
        "output_columns": [{"name": "v", "type": "numeric", "nullable": True}],
        "postgres_type": "numeric", "postgres_display_type": "numeric",
        "expected_value": None,
    } for temporal in sorted(TEMPORAL)]


def null_script(cases, canonical):
    assert len(cases) == len(canonical), "missing rendered EXTRACT NULL observation"
    commands = ["BEGIN;", "SET LOCAL statement_timeout = '5s';",
                "SET LOCAL standard_conforming_strings = on;", "SET LOCAL TIME ZONE 'UTC';"]
    expected = {}
    for index, (case, rendered) in enumerate(zip(cases, canonical), 1):
        types = case["parameter_types"].replace("?", "")
        declaration = f" ({types})" if types else ""
        execute = "EXECUTE extract_null_parameters"
        if case["parameter_values"]:
            execute += " (" + ", ".join(map(literal, case["parameter_values"])) + ")"
        body = "BEGIN RETURN QUERY EXECUTE " + sql_literal(execute) + "; END;"
        for form, sql in (("source", case["sql"]), ("postgres", rendered)):
            source = question_parameters(sql).strip().removesuffix(";")
            key = marker("extract_null", index, True, form)
            commands += [
                f"PREPARE extract_null_parameters{declaration} AS "
                f"SELECT (v IS NULL)::TEXT FROM ({source}) AS observed;",
                "CREATE OR REPLACE FUNCTION pg_temp.extract_null_rows() RETURNS TABLE (sql_null TEXT) "
                "LANGUAGE plpgsql VOLATILE AS " + sql_literal(body) + ";",
                "\\echo " + key, copy_result("SELECT * FROM pg_temp.extract_null_rows()"),
                "DEALLOCATE extract_null_parameters;",
            ]
            expected[key] = (1, [["true" if case["expected_value"] is None else "false"]])
    commands.append("ROLLBACK;")
    return "\n".join(commands), expected


def runtime_cases():
    return [{
        "sql": f"SELECT EXTRACT({field} FROM CAST($1 AS {temporal})) AS v;",
        "parameter_types": "text", "parameter_values": [value],
        "output_columns": [{"name": "v", "type": "numeric", "nullable": nullable}],
        "sqlstate": state,
    } for field, temporal, value, nullable, state in (
        ("foo", "DATE", "2024-02-29", True, "22023"),
        ("''", "TIME", "12:00:00", False, "22023"),
        ("HOUR", "DATE", "2024-02-29", True, "0A000"),
        ("DAY", "TIME", "12:00:00", False, "0A000"),
        ("TIMEZONE", "TIMESTAMP", "2024-02-29 12:00:00", True, "0A000"),
        ("WEEK", "INTERVAL", "1 day", False, "0A000"),
        ("YEAR", "DATE", "not-a-date", True, "22007"),
        ("YEAR", "DATE", "2024-02-30", True, "22008"),
        ("'da''y'", "DATE", "2024-02-29", True, "22023"),
    )]


def error_script(cases, canonical):
    assert len(cases) == len(canonical), "missing rendered EXTRACT runtime case"
    commands, expected = ["BEGIN;", "SET LOCAL statement_timeout = '5s';",
                          "SET LOCAL standard_conforming_strings = on;"], {}
    for index, (case, rendered) in enumerate(zip(cases, canonical), 1):
        for form, sql in (("source", case["sql"]), ("postgres", rendered)):
            capture = prepare_capture(sql, case["parameter_types"], case["parameter_values"], error=True)
            key = marker("extract_error", index, True, form)
            commands += [*capture[:-1], "\\echo " + key, capture[-1], "DEALLOCATE pagination_parameters;"]
            expected[key] = (1, [[case["sqlstate"]]])
    commands.append("ROLLBACK;")
    return "\n".join(commands), expected


def label_cases():
    return [{
        "sql": f"SELECT {expression};", "parameter_types": "", "parameter_values": [],
        "output_columns": [{"name": name, "type": type_, "nullable": nullable}],
        "postgres_display_type": type_,
    } for expression, name, type_, nullable in (
        ("EXTRACT(YEAR FROM DATE '2024-02-29')", "extract", "numeric", True),
        ("CAST(EXTRACT(HOUR FROM TIME '12:34:56') AS TEXT)", "extract", "text", False),
        ("CASE WHEN FALSE THEN 0 ELSE EXTRACT(HOUR FROM TIME '12:00:00') END",
         "extract", "numeric", False),
        ("EXTRACT(YEAR FROM DATE '2024-02-29') + 1", "?column?", "numeric", True),
        ("COALESCE(EXTRACT(SECOND FROM NULL::INTERVAL),0)", "coalesce", "numeric", False),
        ("CAST(EXTRACT(YEAR FROM DATE '2024-02-29') AS NUMERIC(8,2))",
         "extract", "numeric(8,2)", True),
        ("EXTRACT(EPOCH FROM INTERVAL '1 day')", "extract", "numeric", False),
        ("EXTRACT(DAY FROM TIMESTAMP 'infinity')", "extract", "numeric", True),
        ("EXTRACT('TIMEZONE' FROM TIMESTAMP 'infinity')", "extract", "numeric", True),
    )]


def reject_sqlite(case):
    result = invoke(["--render-assurance", "sqlite"], stdin=case["sqlite_input"])
    report = json.loads(result.stdout)
    assert (result.returncode, report["status"], report["diagnostic"]["code"]) in {
        (1, "invalid", "input.parse"), (3, "unsupported", "coverage.sqlite.extract"),
    }, report


def boundaries():
    invalid = [
        f"SELECT EXTRACT(YEAR FROM {expression})" for expression in (
            "1", "1.0", "TRUE", "'2024-01-01'", "NULL", "'2024-01-01'::TEXT",
            "'{}'::JSONB", "ARRAY[1]", "ARRAY[]::DATE[]",
        )
    ]
    unsupported = ["SELECT EXTRACT(YEAR FROM (SELECT DATE '2024-01-01'))",
                   "SELECT EXTRACT(YEAR FROM unknown_function())"]
    valid = ["SELECT EXTRACT(foo FROM DATE '2024-01-01')",
             "SELECT EXTRACT(HOUR FROM DATE '2024-01-01')",
             "SELECT EXTRACT('' FROM NULL::TIME)"]
    for status, queries in (("invalid", invalid), ("unsupported", unsupported), ("valid", valid)):
        for sql in queries:
            assert_report(["--assurance", "contract", sql], status, "contract")
    syntax = ["SELECT EXTRACT()", "SELECT EXTRACT(YEAR DATE '2024-01-01')",
              "SELECT EXTRACT(* FROM DATE '2024-01-01')",
              "SELECT EXTRACT(TIME FROM DATE '2024-01-01')",
              "SELECT EXTRACT(CURRENT_DATE FROM DATE '2024-01-01')",
              "SELECT EXTRACT(123 FROM DATE '2024-01-01')",
              "SELECT EXTRACT(NULL FROM DATE '2024-01-01')",
              "SELECT EXTRACT(YEAR FROM DATE '2024-01-01', 1)"]
    for sql in syntax:
        result = invoke(["--render-assurance", "identity", sql])
        report = json.loads(result.stdout)
        assert (result.returncode, report["status"], report["diagnostic"]["code"]) == (
            1, "invalid", "input.parse"), report
    assert_report(["--assurance", "checked", "SELECT EXTRACT(YEAR FROM DATE '2024-01-01')"],
                  "rejected", "checked")
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
    # These fixed source-free queries are certified and rendered, never executed.
    for row in source:
        assert_report(["--assurance", "contract", row["sql"]], "valid", "contract")
        for profile in ("identity", "postgres"):
            replay(profile, row["sql"])
    errors, labels, shortcuts = runtime_cases(), label_cases(), null_shortcuts()
    error_rendered, label_rendered, shortcut_rendered = [], [], []
    for cases, rendered in ((errors, error_rendered), (labels, label_rendered), (shortcuts, shortcut_rendered)):
        for case in cases:
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
    print("PASS: 50 synthetic and 50 unchanged source EXTRACT certificates/renderings")
    print(f"PASS: {boundary_count} boundaries, 6 NULL short-circuits and 50 SQLite exclusions")
    print(f"PASS: PostgreSQL {version}: {len(values)} values/OIDs, {len(nulls)} SQL-NULL observations, "
          f"{len(metadata)} exact prepared descriptors")
    print(f"PASS: {len(expected_errors)} expected errors and {len(functions)} native declarations")
    print("Scope: finite authored executions; field units and input conversion remain runtime obligations.")


if __name__ == "__main__":
    main()
