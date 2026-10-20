#!/usr/bin/env python3
"""Check array concatenation certificates and finite authored PostgreSQL oracles."""
import argparse
import json

from check_advanced_cli import literal, question_parameters
from check_array_types_cli import describe_script, validate_results, validity
from check_assurance_cli import assert_report, invoke
from check_extended_types_cli import database_script
from check_pagination_cli import ROOT, replay, prepare_capture
from check_postgresql_cli import connection, copy_result, marker, parse_results, run, sql_literal
from check_renderer_corpus import parameters

FIXTURES = ROOT / "fixtures/array_concatenation"


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
        assert output["name"] == "v" and output["type"].endswith("[]")
        assert type(output["nullable"]) is bool and row["sqlite_supported"] is False
        assert row["postgres_display_type"] == (
            "bpchar[]" if row["postgres_type"] == "character[]" else row["postgres_type"])
        assert row["postgres_type"].endswith("[]")
        assert row["expected_value"] is None or isinstance(row["expected_value"], str)
        assert row["expected_value"] is not None or output["nullable"]
        assert {slot for _, slot in parameters(row["sql"], "postgres")} == set(
            range(1, len(row["parameter_values"]) + 1))
        assert parameters(row["sql"], "postgres") == parameters(row["sqlite_input"], "sqlite")
    assert all(row["observed_syntax"]["source_free"] is True for row in source)
    return rows, source


def operator_script():
    rows = json.loads((FIXTURES / "operator_signatures.json").read_text())
    fields = ("operator", "left", "right", "output", "function")
    wanted = {
        ("||", "anycompatiblearray", "anycompatiblearray", "anycompatiblearray", "array_cat"),
        ("||", "anycompatiblearray", "anycompatible", "anycompatiblearray", "array_append"),
        ("||", "anycompatible", "anycompatiblearray", "anycompatiblearray", "array_prepend"),
    }
    assert len(rows) == 3 and {tuple(row[key] for key in fields) for row in rows} == wanted
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
            "AND NOT p.proisstrict AND NOT p.proretset AND p.pronargs=2 AND p.prokind='f');")
        expected.append(f"{index}|t")
    return "\n".join(commands), expected


def null_script(cases, canonical):
    """Observe outer SQL NULL independently of NULL elements or JSON null."""
    assert len(cases) == len(canonical), "missing rendered array NULL observation"
    commands = ["BEGIN;", "SET LOCAL statement_timeout = '5s';",
                "SET LOCAL standard_conforming_strings = on;"]
    expected = {}
    for index, (case, rendered) in enumerate(zip(cases, canonical), 1):
        types = case["parameter_types"].replace("?", "")
        declaration = f" ({types})" if types else ""
        execute = "EXECUTE array_null_parameters"
        if case["parameter_values"]:
            execute += " (" + ", ".join(map(literal, case["parameter_values"])) + ")"
        body = "BEGIN RETURN QUERY EXECUTE " + sql_literal(execute) + "; END;"
        for form, sql in (("source", case["sql"]), ("postgres", rendered)):
            source = question_parameters(sql).strip().removesuffix(";")
            key = marker("array_concat_null", index, True, form)
            commands += [
                f"PREPARE array_null_parameters{declaration} AS "
                f"SELECT (v IS NULL)::TEXT FROM ({source}) AS observed;",
                "CREATE OR REPLACE FUNCTION pg_temp.array_null_rows() RETURNS TABLE (sql_null TEXT) "
                "LANGUAGE plpgsql VOLATILE AS " + sql_literal(body) + ";",
                "\\echo " + key, copy_result("SELECT * FROM pg_temp.array_null_rows()"),
                "DEALLOCATE array_null_parameters;",
            ]
            expected[key] = (1, [["true" if case["expected_value"] is None else "false"]])
    commands.append("ROLLBACK;")
    return "\n".join(commands), expected


def reject_sqlite(case):
    result = invoke(["--render-assurance", "sqlite"], stdin=case["sqlite_input"])
    report = json.loads(result.stdout)
    assert (result.returncode, report["status"], report["diagnostic"]["code"]) in {
        (1, "invalid", "input.parse"),
        (3, "unsupported", "coverage.sqlite.array-type"),
        (3, "unsupported", "coverage.sqlite.array-constructor"),
    }, report


def runtime_cases():
    return [{
        "sql": f"SELECT {expression} AS v;", "parameter_types": types,
        "parameter_values": values,
        "output_columns": [{"name": "v", "type": "integer[]", "nullable": False}],
        "sqlstate": state,
    } for expression, types, values, state in (
        ("ARRAY[[1,2]] || ARRAY[[3]]", "", [], "2202E"),
        ("ARRAY[1] || ARRAY[[[2]]]", "", [], "2202E"),
        ("ARRAY[[1,2]] || 3", "", [], "22000"),
        ("3 || ARRAY[[1,2]]", "", [], "22000"),
        ("'[1:1][0:1]={{1,2}}'::INTEGER[] || '[1:1][1:2]={{3,4}}'::INTEGER[]",
         "", [], "2202E"),
        ("ARRAY[1] || CAST($1 AS INTEGER[])", "text", ["2"], "22P02"),
        ("ARRAY[1] || CAST($1 AS INTEGER)", "text", ["2147483648"], "22003"),
    )]


def error_script(cases, canonical):
    assert len(cases) == len(canonical), "missing rendered array concatenation runtime case"
    commands, expected = ["BEGIN;", "SET LOCAL statement_timeout = '5s';",
                          "SET LOCAL standard_conforming_strings = on;"], {}
    for index, (case, rendered) in enumerate(zip(cases, canonical), 1):
        for form, sql in (("source", case["sql"]), ("postgres", rendered)):
            capture = prepare_capture(sql, case["parameter_types"], case["parameter_values"], error=True)
            key = marker("array_concat_error", index, True, form)
            commands += [*capture[:-1], "\\echo " + key, capture[-1], "DEALLOCATE pagination_parameters;"]
            expected[key] = (1, [[case["sqlstate"]]])
    commands.append("ROLLBACK;")
    return "\n".join(commands), expected


def label_cases():
    return [{
        "sql": f"SELECT {expression};", "parameter_types": "", "parameter_values": [],
        "output_columns": [{"name": "?column?", "type": type_, "nullable": nullable}],
        "postgres_display_type": display,
    } for expression, type_, display, nullable in (
        ("ARRAY[1] || ARRAY[2]", "integer[]", "integer[]", False),
        ("NULL::INTEGER[] || NULL::INTEGER[]", "integer[]", "integer[]", True),
        ("NULL::INTEGER[] || NULL::INTEGER", "integer[]", "integer[]", False),
        ("NULL::INTEGER || NULL::INTEGER[]", "integer[]", "integer[]", False),
        ("ARRAY['a'::CHAR(3)] || 'b'::TEXT", "bpchar[]", "bpchar[]", False),
        ("ARRAY[1.2::NUMERIC(6,2)] || ARRAY[3.4::NUMERIC(6,2)]", "numeric[]", "numeric[]", False),
    )]


def boundaries():
    invalid = [
        "SELECT ARRAY[1] || ARRAY[TRUE]",
        "SELECT ARRAY[1] || 'x'::TEXT",
        "SELECT 'x'::TEXT || ARRAY[1]",
        "SELECT ARRAY['1'::JSON] || ARRAY['1'::JSONB]",
        "SELECT (ARRAY[1] || ARRAY[2]) + 3",
    ]
    unsupported = [
        "SELECT ARRAY[1] || (SELECT ARRAY[2])",
        "SELECT unknown_function() || ARRAY[1]",
        "SELECT DISTINCT ARRAY['1'::JSON] || ARRAY['2'::JSON]",
    ]
    for status, queries in (("invalid", invalid), ("unsupported", unsupported)):
        for sql in queries:
            assert_report(["--assurance", "contract", sql], status, "contract")
    for sql, columns in [
        ("SELECT '{}' || '{}' AS v", (("v", "text", False),)),
        ("SELECT NULL || NULL AS v", (("v", "text", True),)),
        ("SELECT ARRAY[1] || -2 AS v", (("v", "integer[]", False),)),
    ]:
        assert_report(["--assurance", "contract", sql], "valid", "contract", columns)
    result = invoke(["--render-assurance", "identity", "SELECT ARRAY[1]||-2"])
    report = json.loads(result.stdout)
    assert (result.returncode, report["status"], report["diagnostic"]["code"]) == (
        1, "invalid", "input.parse"), report
    for sql in ("SELECT ARRAY[1] || ARRAY[2]", "SELECT ARRAY[1] || 2", "SELECT 1 || ARRAY[2]"):
        assert_report(["--assurance", "checked", sql], "rejected", "checked")
    return len(invalid) + len(unsupported) + 7


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
    # Every source ID is fixed before validation. Source SQL is never executed.
    for row in source:
        assert_report(["--assurance", "contract", row["sql"]], "valid", "contract")
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
    nulls_sql, nulls = null_script(rows, postgres)
    metadata_sql, metadata = describe_script(rows + labels, postgres + label_rendered)
    errors_sql, expected_errors = error_script(errors, error_rendered)
    operators_sql, operators = operator_script()
    with connection(args) as psql:
        for script, expected in ((values_sql, values), (nulls_sql, nulls), (errors_sql, expected_errors)):
            result = run([*psql, "-X", "-q", "-v", "ON_ERROR_STOP=1"], input=script, timeout=120)
            validate_results(parse_results(result.stdout), expected)
        for script, expected in ((metadata_sql, metadata), (operators_sql, operators)):
            result = run([*psql, "-X", "-qAt", "-v", "ON_ERROR_STOP=1"], input=script, timeout=120)
            assert result.stdout.splitlines() == expected, (result.stdout.splitlines(), expected)
        version = run([*psql, "-X", "-At", "-c", "SHOW server_version;"]).stdout.strip()
    print("PASS: 50 synthetic and 50 unchanged-source array concatenation certificates/renderings")
    print(f"PASS: {boundary_count} boundaries and 50 explicit SQLite array exclusions")
    print(f"PASS: PostgreSQL {version}: {len(values)} values/OIDs, {len(nulls)} SQL-NULL observations, "
          f"{len(metadata)} exact prepared descriptors")
    print(f"PASS: {len(expected_errors)} runtime errors and {len(operators)} non-strict generic overloads")
    print("Scope: finite authored executions; source SQL is never executed; runtime shape/error freedom is not proved.")


if __name__ == "__main__":
    main()
