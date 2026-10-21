#!/usr/bin/env python3
"""Verify JSON extraction contracts, native signatures, values and SQL NULLs."""
import argparse
import json

from check_advanced_cli import literal, question_parameters
from check_array_types_cli import describe_script, validate_results, validity
from check_assurance_cli import assert_report, invoke
from check_extended_types_cli import database_script
from check_pagination_cli import ROOT, replay, prepare_capture
from check_postgresql_cli import connection, copy_result, marker, parse_results, run, sql_literal
from check_renderer_corpus import parameters

FIXTURES = ROOT / "fixtures/json_extraction"


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
        assert output["name"] == "v" and output["type"] in {"json", "jsonb", "text"}
        assert output["nullable"] is True
        assert row["postgres_type"] == row["postgres_display_type"] == output["type"]
        assert type(row["expected_sql_null"]) is bool
        assert row["expected_sql_null"] == (row["expected_value"] is None)
        assert row["expected_value"] is None or isinstance(row["expected_value"], str)
        assert row["sqlite_supported"] is False
        assert {slot for _, slot in parameters(row["sql"], "postgres")} == set(
            range(1, len(row["parameter_values"]) + 1))
        assert parameters(row["sql"], "postgres") == parameters(row["sqlite_input"], "sqlite")
    return rows, source


def operator_script():
    rows = json.loads((FIXTURES / "operator_signatures.json").read_text())
    fields = ("operator", "left", "right", "output", "function")
    wanted = set()
    for operator, suffix in (("->", ""), ("->>", "_text"), ("#>", ""), ("#>>", "_text")):
        for base in ("json", "jsonb"):
            for key in (("text", "integer") if operator.startswith("-") else ("text[]",)):
                function = ("_object_field" if key == "text" else
                            "_array_element" if key == "integer" else "_extract_path")
                wanted.add((operator, base, key, "text" if suffix else base, base + function + suffix))
    assert len(rows) == 12 and {tuple(row[key] for key in fields) for row in rows} == wanted
    commands, expected = [], []
    for index, row in enumerate(rows):
        operator, left, right, output, function = map(sql_literal, (row[key] for key in fields))
        # Path procedures have variadic TEXT elements but the operator's second
        # declared argument remains one TEXT[] value.
        variadic = "'text'::regtype" if row["right"] == "text[]" else "0"
        commands.append(
            f"SELECT {index}, EXISTS(SELECT FROM pg_catalog.pg_operator o "
            "JOIN pg_catalog.pg_proc p ON p.oid=o.oprcode "
            f"WHERE o.oprnamespace='pg_catalog'::regnamespace AND o.oprname={operator} "
            f"AND o.oprleft={left}::regtype AND o.oprright={right}::regtype "
            f"AND o.oprresult={output}::regtype AND p.prorettype={output}::regtype "
            f"AND p.proname={function} AND p.pronamespace='pg_catalog'::regnamespace "
            f"AND p.proargtypes[0]={left}::regtype AND p.proargtypes[1]={right}::regtype "
            f"AND p.provariadic={variadic} "
            "AND p.proisstrict AND NOT p.proretset AND p.pronargs=2 AND p.prokind='f');")
        expected.append(f"{index}|t")
    return "\n".join(commands), expected


def null_script(cases, canonical):
    """Observe SQL NULL separately from JSON null and its serialized text."""
    assert len(cases) == len(canonical), "missing rendered JSON NULL observation"
    commands = ["BEGIN;", "SET LOCAL statement_timeout = '5s';",
                "SET LOCAL standard_conforming_strings = on;"]
    expected = {}
    for index, (case, rendered) in enumerate(zip(cases, canonical), 1):
        types = case["parameter_types"].replace("?", "")
        declaration = f" ({types})" if types else ""
        execute = "EXECUTE json_null_parameters"
        if case["parameter_values"]:
            execute += " (" + ", ".join(map(literal, case["parameter_values"])) + ")"
        body = "BEGIN RETURN QUERY EXECUTE " + sql_literal(execute) + "; END;"
        for form, sql in (("source", case["sql"]), ("postgres", rendered)):
            source = question_parameters(sql).strip().removesuffix(";")
            key = marker("json_null", index, True, form)
            commands += [
                f"PREPARE json_null_parameters{declaration} AS "
                f"SELECT (v IS NULL)::TEXT FROM ({source}) AS observed;",
                "CREATE OR REPLACE FUNCTION pg_temp.json_null_rows() RETURNS TABLE (sql_null TEXT) "
                "LANGUAGE plpgsql VOLATILE AS " + sql_literal(body) + ";",
                "\\echo " + key, copy_result("SELECT * FROM pg_temp.json_null_rows()"),
                "DEALLOCATE json_null_parameters;",
            ]
            expected[key] = (1, [["true" if case["expected_sql_null"] else "false"]])
    commands.append("ROLLBACK;")
    return "\n".join(commands), expected


def reject_sqlite(case):
    result = invoke(["--render-assurance", "sqlite"], stdin=case["sqlite_input"])
    report = json.loads(result.stdout)
    assert (result.returncode, report["status"], report["diagnostic"]["code"]) in {
        (1, "invalid", "input.parse"), (3, "unsupported", "coverage.sqlite.json-extraction"),
    }, report


def runtime_cases():
    return [{
        "sql": f"SELECT {expression} AS v;", "parameter_types": "text",
        "parameter_values": [value],
        "output_columns": [{"name": "v", "type": output, "nullable": True}],
        "sqlstate": state,
    } for expression, value, output, state in (
        ("CAST($1 AS JSON) -> 'a'", "bad json", "json", "22P02"),
        ("CAST($1 AS JSONB) -> 'a'", "bad json", "jsonb", "22P02"),
        ("CAST($1 AS JSONB) ->> 'a'", r'{"a":"\u0000"}', "text", "22P05"),
        ("""'{"a":1}'::JSON #> CAST($1 AS TEXT[])""", "bad array", "json", "22P02"),
        ("'[1]'::JSONB -> CAST($1 AS INTEGER)", "2147483648", "jsonb", "22003"),
    )]


def error_script(cases, canonical):
    assert len(cases) == len(canonical), "missing rendered JSON runtime case"
    commands, expected = ["BEGIN;", "SET LOCAL statement_timeout = '5s';"], {}
    for index, (case, rendered) in enumerate(zip(cases, canonical), 1):
        for form, sql in (("source", case["sql"]), ("postgres", rendered)):
            capture = prepare_capture(sql, case["parameter_types"], case["parameter_values"], error=True)
            key = marker("json_extraction_error", index, True, form)
            commands += [*capture[:-1], "\\echo " + key, capture[-1], "DEALLOCATE pagination_parameters;"]
            expected[key] = (1, [[case["sqlstate"]]])
    commands.append("ROLLBACK;")
    return "\n".join(commands), expected


def label_cases():
    return [{
        "sql": f"SELECT {expression};", "parameter_types": "", "parameter_values": [],
        "output_columns": [{"name": name, "type": type_, "nullable": True}],
        "postgres_display_type": type_,
    } for expression, name, type_ in (
        ("'{}'::JSON -> 'a'", "?column?", "json"),
        ("'{}'::JSONB -> 'a'", "?column?", "jsonb"),
        ("'{}'::JSON ->> 'a'", "?column?", "text"),
        ("'{}'::JSONB ->> 'a'", "?column?", "text"),
        ("'{}'::JSON #> '{}'", "?column?", "json"),
        ("'{}'::JSONB #> '{}'", "?column?", "jsonb"),
        ("'{}'::JSON #>> '{}'", "?column?", "text"),
        ("'{}'::JSONB #>> '{}'", "?column?", "text"),
        ("CAST(('{}'::JSON -> 'a') AS TEXT)", "text", "text"),
    )]


def boundaries():
    invalid = [
        "SELECT '{}' -> 'a'", "SELECT NULL -> 1", "SELECT NULL #> '{a}'",
        "SELECT NULL ->> NULL", "SELECT NULL #>> NULL",
        "SELECT '{}'::TEXT -> 'a'", "SELECT 1 -> 'a'",
        "SELECT '{}'::JSON -> 1::BIGINT", "SELECT '{}'::JSON -> 1::NUMERIC",
        "SELECT '{}'::JSONB -> 1::REAL", "SELECT '{}'::JSONB -> TRUE",
        "SELECT '{}'::JSON #> ARRAY[1]", "SELECT '{}'::JSONB #>> '{a}'::TEXT",
        "SELECT '{}'::JSON #> ARRAY['1'::JSON]", "SELECT '{}'::JSONB -> ARRAY['a']",
    ]
    unsupported = [
        "SELECT unknown_function() #> '{a}'",
    ]
    promoted = [
        ("SELECT (SELECT '{}'::JSON) -> 'a'", (('?column?', 'json', True),)),
        ("SELECT '{}'::JSONB ->> (SELECT 'a')", (('?column?', 'text', True),)),
    ]
    for sql, columns in promoted:
        assert_report(["--assurance", "contract", sql], "valid", "contract", columns)
    valid = ["SELECT '{}'::JSONB ? 'a'"]
    syntax = [
        "SELECT '{}'::JSON ->", "SELECT '{}'::JSON #>", "SELECT -> 'a'",
        "SELECT '{}'::JSON ->>> 'a'", "SELECT '{}'::JSON #>-1",
        "SELECT '{}'::JSONB @@ '$.a'",
    ]
    for status, queries in (("invalid", invalid), ("unsupported", unsupported), ("valid", valid)):
        for sql in queries:
            assert_report(["--assurance", "contract", sql], status, "contract")
    for sql in syntax:
        result = invoke(["--render-assurance", "identity", sql])
        report = json.loads(result.stdout)
        assert (result.returncode, report["status"], report["diagnostic"]["code"]) == (
            1, "invalid", "input.parse"), report
    assert_report(["--assurance", "checked", "SELECT '{}'::JSON -> 'a'"], "rejected", "checked")
    return len(invalid) + len(unsupported) + len(valid) + len(syntax) + 1 + len(promoted)


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
        # This fixed population has explicit JSON casts and no FROM relations
        # or parameter assumptions. Its Lean corpus test fixes exact outputs.
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
    null_sql, nulls = null_script(rows, postgres)
    metadata_sql, metadata = describe_script(rows + labels, postgres + label_rendered)
    errors_sql, expected_errors = error_script(errors, error_rendered)
    operators_sql, operators = operator_script()
    with connection(args) as psql:
        for script, expected in ((values_sql, values), (null_sql, nulls), (errors_sql, expected_errors)):
            result = run([*psql, "-X", "-q", "-v", "ON_ERROR_STOP=1"], input=script, timeout=120)
            validate_results(parse_results(result.stdout), expected)
        for script, expected in ((metadata_sql, metadata), (operators_sql, operators)):
            result = run([*psql, "-X", "-qAt", "-v", "ON_ERROR_STOP=1"], input=script, timeout=120)
            assert result.stdout.splitlines() == expected, (result.stdout.splitlines(), expected)
        version = run([*psql, "-X", "-At", "-c", "SHOW server_version;"]).stdout.strip()
    print("PASS: 50 synthetic and 50 unchanged JSON extraction source certificates and renderings")
    print(f"PASS: {boundary_count} boundaries and 50 explicit SQLite dialect exclusions")
    print(f"PASS: PostgreSQL {version}: {len(values)} value/OID and {len(nulls)} SQL NULL observations")
    print(f"PASS: {len(metadata)} descriptors, {len(expected_errors)} expected errors and {len(operators)} native overloads")
    print("Scope: exact static signatures and finite native observations; concrete source SQL is never executed.")


if __name__ == "__main__":
    main()
