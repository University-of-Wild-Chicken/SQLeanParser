#!/usr/bin/env python3
"""Check quantified array contracts, scalar operator inventory and native results."""
import argparse
import json

from check_array_types_cli import describe_script, reject_sqlite, validate_results, validity
from check_assurance_cli import assert_report, invoke
from check_extended_types_cli import database_script
from check_pagination_cli import ROOT, replay, prepare_capture
from check_postgresql_cli import connection, marker, parse_results, run, sql_literal
from check_renderer_corpus import parameters

FIXTURES = ROOT / "fixtures/array_quantified"


def load_cases():
    rows = json.loads((FIXTURES / "synthetic.json").read_text())
    concrete = [json.loads(line) for line in (FIXTURES / "concrete.jsonl").read_text().splitlines()]
    for population in (rows, concrete):
        assert len(population) == len({row["id"] for row in population}) == len({row["sql"] for row in population}) == 50
    for row in rows:
        assert row["output_columns"] == [{"name": "v", "type": "bool", "nullable": True}]
        assert {index for _, index in parameters(row["sql"], "postgres")} == set(
            range(1, len(row["parameter_values"]) + 1))
        assert parameters(row["sql"], "postgres") == parameters(row["sqlite_sql"], "sqlite")
    return rows, concrete


def operator_script():
    signatures = json.loads((FIXTURES / "operator_signatures.json").read_text())
    triples = {(s["operator"], s["left"], s["right"]) for s in signatures}
    assert len(signatures) == len(triples) == 192, "missing or duplicate scalar comparison signature"
    assert {op for op, _, _ in triples} == {"=", "<>", "<", "<=", ">", ">="}
    commands, expected = [], []
    for i, signature in enumerate(signatures):
        operator, left, right = map(sql_literal, (signature["operator"], signature["left"], signature["right"]))
        commands.append(
            f"SELECT {i}, EXISTS(SELECT FROM pg_catalog.pg_operator o "
            "JOIN pg_catalog.pg_proc p ON p.oid=o.oprcode "
            "WHERE o.oprnamespace='pg_catalog'::regnamespace "
            f"AND o.oprname={operator} AND o.oprleft={left}::regtype AND o.oprright={right}::regtype "
            "AND o.oprresult='boolean'::regtype AND p.prorettype='boolean'::regtype "
            "AND p.proisstrict AND NOT p.proretset AND p.pronargs=2 AND p.prokind='f');")
        expected.append(f"{i}|t")
    return "\n".join(commands), expected


def runtime_cases():
    examples = [
        ("1 = ANY(CAST($1 AS INTEGER[]))", "text", ["bad array"], "22P02"),
        ("CAST($1 AS INTEGER) = SOME(ARRAY[1,2])", "text", ["bad integer"], "22P02"),
        ("1/$1 > ALL(ARRAY[1,2])", "int", [0], "22012"),
        ("1 = ANY(ARRAY[[1],[2,3]])", "", [], "2202E"),
        ("1 = SOME(ARRAY['null'::JSONB]::INTEGER[])", "", [], "22023"),
    ]
    return [{
        "sql": f"SELECT {expr} AS v;", "parameter_types": types, "parameter_values": values,
        "output_columns": [{"name": "v", "type": "bool", "nullable": True}], "sqlstate": state,
    } for expr, types, values, state in examples]


def error_script(cases, canonical):
    assert len(cases) == len(canonical), "missing rendered quantified runtime case"
    commands, expected = ["BEGIN;"], {}
    for i, (case, rendered) in enumerate(zip(cases, canonical), 1):
        for form, sql in (("source", case["sql"]), ("postgres", rendered)):
            capture = prepare_capture(sql, case["parameter_types"], case["parameter_values"], error=True)
            key = marker("quantified_error", i, True, form)
            commands += [*capture[:-1], "\\echo " + key, capture[-1], "DEALLOCATE pagination_parameters;"]
            expected[key] = (1, [[case["sqlstate"]]])
    commands.append("ROLLBACK;")
    return "\n".join(commands), expected


def label_cases():
    return [{
        "sql": f"SELECT 1 = {quantifier}(ARRAY[1,2]);", "parameter_types": "", "parameter_values": [],
        "output_columns": [{"name": "?column?", "type": "bool", "nullable": True}],
        "postgres_display_type": "boolean",
    } for quantifier in ("ANY", "SOME", "ALL")]


def boundaries():
    invalid = [
        "SELECT 1 = ANY(1)", "SELECT 1 = SOME(NULL::INTEGER)",
        "SELECT 1 = ALL('{1,2}'::TEXT)", "SELECT 1 = ANY(ARRAY['1'::TEXT])",
        "SELECT ARRAY[1] = ANY(NULL)", "SELECT ARRAY[1] = ANY(ARRAY[ARRAY[1]])",
        "SELECT JSON '{}' = ANY(ARRAY[JSON '{}'])", "SELECT TRUE < ALL(ARRAY[1])",
        "SELECT 1 = ANY(ARRAY[])", "SELECT DATE '2024-01-01' = ANY(ARRAY[1])",
    ]
    for sql in invalid:
        assert_report(["--assurance", "contract", sql], "invalid", "contract")
    unsupported = "SELECT 1 = ANY(CAST((SELECT ARRAY[1]) AS INTEGER[]))"
    assert_report(["--assurance", "contract", unsupported], "unsupported", "contract")
    # Parenthesized SELECT still selects the subquery production in PostgreSQL;
    # the typed array form must not silently reinterpret it.
    syntax = [
        "SELECT 1 = ANY(SELECT ARRAY[1])", "SELECT 1 = ANY((SELECT ARRAY[1]))",
        "SELECT 1 = ANY(((SELECT ARRAY[1])))",
    ]
    for sql in syntax:
        result = invoke(["--render-assurance", "identity", sql])
        report = json.loads(result.stdout)
        assert result.returncode == 1 and report["status"] == "invalid", report
        assert report["diagnostic"]["code"] == "input.parse", report
    assert_report(["--assurance", "checked", "SELECT 1 = ANY(ARRAY[1])"], "rejected", "checked")
    return len(invalid) + len(syntax) + 2


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    target = parser.add_mutually_exclusive_group(required=True)
    target.add_argument("--local-bin")
    target.add_argument("--dsn")
    parser.add_argument("--psql")
    args = parser.parse_args()
    rows, source = load_cases()
    canonical = []
    for row in rows:
        validity(row)
        replay("identity", row["sql"])
        canonical.append(replay("postgres", row["sql"])["sql"])
        reject_sqlite(row)
    for row in source:
        for profile in ("identity", "postgres"):
            replay(profile, row["sql"])
    errors, labels = runtime_cases(), label_cases()
    error_canonical, label_canonical = [], []
    for cases, rendered in ((errors, error_canonical), (labels, label_canonical)):
        for case in cases:
            validity(case)
            rendered.append(replay("postgres", case["sql"])["sql"])
    count = boundaries()
    values_sql, values = database_script(rows, canonical)
    metadata_sql, metadata = describe_script(rows + labels, canonical + label_canonical)
    errors_sql, expected_errors = error_script(errors, error_canonical)
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
    print("PASS: 50 quantified array certificates, 50 unchanged source renderings and 50 SQLite rejections")
    print(f"PASS: {count} boundaries; PostgreSQL {version}: {len(values)} value/OID observations")
    print(f"PASS: {len(metadata)} descriptors, {len(expected_errors)} expected errors and {len(operators)} scalar operators")
    print("Scope: static operator resolution and finite native observations; source corpus SQL is never executed.")


if __name__ == "__main__":
    main()
