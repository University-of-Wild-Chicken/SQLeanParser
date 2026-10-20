#!/usr/bin/env python3
"""Verify array predicate contracts and finite authored PostgreSQL observations."""
import argparse
import json

from check_array_types_cli import describe_script, validate_results, validity
from check_assurance_cli import assert_report, invoke
from check_extended_types_cli import database_script
from check_pagination_cli import ROOT, replay, prepare_capture
from check_postgresql_cli import connection, marker, parse_results, run, sql_literal
from check_renderer_corpus import parameters

FACTORS = ("array_containment", "array_overlap")
SOURCE_FREE_COUNTS = {"array_containment": 6, "array_overlap": 5}
FIXTURES = ROOT / "fixtures"
ELEMENTS = {
    "smallint", "integer", "bigint", "numeric", "real", "double precision",
    "text", "varchar", "bpchar", "boolean", "date", "time", "time with time zone",
    "timestamp", "timestamp with time zone", "interval", "uuid", "jsonb", "bytea",
}


def load_cases():
    authored, sources = [], []
    for factor in FACTORS:
        rows = json.loads((FIXTURES / factor / "synthetic.json").read_text())
        source = [json.loads(line) for line in
                  (FIXTURES / factor / "concrete.jsonl").read_text().splitlines()]
        for population in (rows, source):
            assert len(population) == len({row["id"] for row in population}) == len(
                {row["sql"] for row in population}) == 50
        for row in rows:
            assert row["source_kind"] == "synthetic" and row["sqlite_supported"] is False
            assert len(row["output_columns"]) == 1
            output = row["output_columns"][0]
            assert output["name"] == "v" and output["type"] == "bool"
            assert type(output["nullable"]) is bool
            assert row["postgres_type"] == row["postgres_display_type"] == "boolean"
            assert row["expected_value"] in ("true", "false", None)
            assert row["expected_value"] is not None or output["nullable"]
            assert {slot for _, slot in parameters(row["sql"], "postgres")} == set(
                range(1, len(row["parameter_values"]) + 1))
            assert parameters(row["sql"], "postgres") == parameters(row["sqlite_input"], "sqlite")
        assert all(type(row["observed_syntax"]["source_free"]) is bool for row in source)
        assert sum(row["observed_syntax"]["source_free"] for row in source) == SOURCE_FREE_COUNTS[factor], (
            f"changed fixed source-free population for {factor}")
        authored.extend(rows)
        sources.extend(source)
    return authored, sources


def operator_script():
    predicates = json.loads((FIXTURES / "array_containment/operator_signatures.json").read_text())
    equality = json.loads((FIXTURES / "array_containment/element_equality_signatures.json").read_text())
    fields = ("operator", "left", "right", "output", "function")
    wanted = {
        ("@>", "anyarray", "anyarray", "boolean", "arraycontains"),
        ("<@", "anyarray", "anyarray", "boolean", "arraycontained"),
        ("&&", "anyarray", "anyarray", "boolean", "arrayoverlap"),
    }
    assert len(predicates) == 3 and {tuple(row[key] for key in fields) for row in predicates} == wanted
    assert len(equality) == len({row["element"] for row in equality}) == 19
    assert {row["element"] for row in equality} == ELEMENTS
    for row in equality:
        assert row["operator"] == "=" and row["output"] == "boolean"
        assert row["left"] == row["right"] == ("text" if row["element"] == "varchar" else row["element"])
    commands, expected = [], []
    for index, row in enumerate(predicates + equality):
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
    # VARCHAR array equality uses the TEXT implementation through a binary cast.
    commands.append(
        "SELECT 22, EXISTS(SELECT FROM pg_catalog.pg_cast WHERE castsource='varchar'::regtype "
        "AND casttarget='text'::regtype AND castcontext='i' AND castmethod='b');")
    expected.append("22|t")
    return "\n".join(commands), expected


def reject_sqlite(case):
    result = invoke(["--render-assurance", "sqlite"], stdin=case["sqlite_input"])
    report = json.loads(result.stdout)
    assert (result.returncode, report["status"], report["diagnostic"]["code"]) in {
        (1, "invalid", "input.parse"),
        (3, "unsupported", "coverage.sqlite.containment"),
        (3, "unsupported", "coverage.sqlite.overlap"),
    }, report


def runtime_cases():
    return [{
        "sql": f"SELECT CAST($1 AS INTEGER[]) {operator} ARRAY[1] AS v;",
        "parameter_types": "text", "parameter_values": [value],
        "output_columns": [{"name": "v", "type": "bool", "nullable": False}],
        "sqlstate": state,
    } for operator in ("@>", "<@", "&&") for value, state in
        (("not an array", "22P02"), ("{2147483648}", "22003"))]


def equality_gap_cases():
    """Authored JSON[] runtime gaps are rendered but explicitly not certified."""
    return [{
        "sql": f"SELECT CAST($1 AS JSON[]) {operator} ARRAY[]::JSON[] AS v;",
        "parameter_types": "text", "parameter_values": ["{}"],
        "sqlstate": "42883",
    } for operator in ("@>", "<@", "&&")]


def error_script(cases, canonical):
    assert len(cases) == len(canonical), "missing rendered array predicate runtime case"
    commands, expected = ["BEGIN;", "SET LOCAL statement_timeout = '5s';",
                          "SET LOCAL standard_conforming_strings = on;"], {}
    for index, (case, rendered) in enumerate(zip(cases, canonical), 1):
        for form, sql in (("source", case["sql"]), ("postgres", rendered)):
            capture = prepare_capture(sql, case["parameter_types"], case["parameter_values"], error=True)
            key = marker("array_predicate_error", index, True, form)
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
        ("ARRAY[1] @> ARRAY[1]", "bool", False),
        ("ARRAY[1] <@ ARRAY[1]", "bool", False),
        ("ARRAY[1] && ARRAY[1]", "bool", False),
        ("NULL::INTEGER[] @> ARRAY[1]", "bool", True),
        ("ARRAY[1] && NULL", "bool", True),
        ("ARRAY[1] @> ARRAY[1] || 'x'", "text", False),
        ("ARRAY[1] && ARRAY[1] || 'x'", "text", False),
        ("ARRAY[1] || ARRAY[2] && ARRAY[2]", "bool", False),
        ("NOT ARRAY[1] && ARRAY[1]", "bool", False),
    )]


def boundaries():
    invalid = [
        f"SELECT {left} {operator} {right}" for operator in ("@>", "<@", "&&") for left, right in (
            ("ARRAY[1]", "ARRAY[1::BIGINT]"), ("ARRAY['x'::VARCHAR]", "ARRAY['x'::TEXT]"),
            ("ARRAY[1]", "1"), ("ARRAY[1]", "'{1}'::TEXT"),
            ("ARRAY['1'::JSON]", "ARRAY['1'::JSONB]"),
        )
    ] + ["SELECT '{}' && '{}'", "SELECT NULL && NULL", "SELECT '{}'::JSONB && '{}'::JSONB"]
    unsupported = [
        f"SELECT {left} {operator} {right}" for operator in ("@>", "<@", "&&") for left, right in (
            ("ARRAY[]::JSON[]", "ARRAY[]::JSON[]"), ("NULL::JSON[]", "'{}'"),
            ("ARRAY[1]", "(SELECT ARRAY[1])"), ("unknown_function()", "ARRAY[1]"),
        )
    ]
    valid = ["SELECT ARRAY[1] && '{1}'", "SELECT '{1}' && ARRAY[1]",
             "SELECT ARRAY[1] && NULL", "SELECT NULL && ARRAY[1]"]
    for status, queries in (("invalid", invalid), ("unsupported", unsupported), ("valid", valid)):
        for sql in queries:
            assert_report(["--assurance", "contract", sql], status, "contract")
    syntax = ["SELECT ARRAY[1]&&-1", "SELECT ARRAY[1] &&", "SELECT && ARRAY[1]",
              "SELECT ARRAY[1] &&& ARRAY[1]"]
    for sql in syntax:
        result = invoke(["--render-assurance", "identity", sql])
        report = json.loads(result.stdout)
        assert (result.returncode, report["status"], report["diagnostic"]["code"]) == (
            1, "invalid", "input.parse"), report
    for operator in ("@>", "<@", "&&"):
        assert_report(["--assurance", "checked", f"SELECT ARRAY[1] {operator} ARRAY[1]"],
                      "rejected", "checked")
    return len(invalid) + len(unsupported) + len(valid) + len(syntax) + 3


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
    # Source SQL is parsed/certified against fixed populations, never executed.
    certified_source = 0
    for row in source:
        if row["observed_syntax"]["source_free"]:
            assert_report(["--assurance", "contract", row["sql"]], "valid", "contract")
            certified_source += 1
        for profile in ("identity", "postgres"):
            replay(profile, row["sql"])
    errors, labels, gaps = runtime_cases(), label_cases(), equality_gap_cases()
    error_rendered, label_rendered = [], []
    for cases, rendered in ((errors, error_rendered), (labels, label_rendered)):
        for case in cases:
            validity(case)
            rendered.append(replay("postgres", case["sql"])["sql"])
    for case in gaps:
        assert_report(["--assurance", "contract", "--param-types", case["parameter_types"], case["sql"]],
                      "unsupported", "contract")
        error_rendered.append(replay("postgres", case["sql"])["sql"])
    boundary_count = boundaries()
    values_sql, values = database_script(rows, postgres)
    metadata_sql, metadata = describe_script(rows + labels, postgres + label_rendered)
    errors_sql, expected_errors = error_script(errors + gaps, error_rendered)
    operators_sql, operators = operator_script()
    with connection(args) as psql:
        for script, expected in ((values_sql, values), (errors_sql, expected_errors)):
            result = run([*psql, "-X", "-q", "-v", "ON_ERROR_STOP=1"], input=script, timeout=120)
            validate_results(parse_results(result.stdout), expected)
        for script, expected in ((metadata_sql, metadata), (operators_sql, operators)):
            result = run([*psql, "-X", "-qAt", "-v", "ON_ERROR_STOP=1"], input=script, timeout=120)
            assert result.stdout.splitlines() == expected, (result.stdout.splitlines(), expected)
        version = run([*psql, "-X", "-At", "-c", "SHOW server_version;"]).stdout.strip()
    print("PASS: 50 synthetic and 50 unchanged source renderings per array predicate factor")
    print(f"PASS: 100 authored and {certified_source} fixed source full-query certificates")
    print(f"PASS: {boundary_count} boundaries and 100 explicit SQLite exclusions")
    print(f"PASS: PostgreSQL {version}: {len(values)} value/OID observations, {len(metadata)} descriptors")
    print(f"PASS: {len(expected_errors)} runtime errors, 3 predicates, 19 element mappings and VARCHAR coercion")
    print("Scope: finite authored executions; source SQL is never executed; JSON[] equality remains Unsupported.")


if __name__ == "__main__":
    main()
