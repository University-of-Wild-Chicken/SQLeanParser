#!/usr/bin/env python3
"""Verify row comparisons, native B-tree operators and separate dialect oracles."""
import argparse
import json
import sqlite3

from check_array_types_cli import describe_script, validate_results, validity
from check_assurance_cli import assert_report, invoke
from check_extended_types_cli import database_script
from check_pagination_cli import ROOT, replay, prepare_capture, sqlite_bindings
from check_postgresql_cli import connection, marker, parse_results, run, sql_literal
from check_renderer_corpus import parameters

FIXTURES = ROOT / "fixtures/row_comparisons"
SIGNATURES = ROOT / "fixtures/array_quantified/operator_signatures.json"


def load_cases():
    rows = json.loads((FIXTURES / "synthetic.json").read_text())
    concrete = [json.loads(line) for line in (FIXTURES / "concrete.jsonl").read_text().splitlines()]
    for population in (rows, concrete):
        assert len(population) == len({row["id"] for row in population}) == len({row["sql"] for row in population}) == 50
    for row in rows:
        assert row["output_columns"] == [{"name": "v", "type": "bool", "nullable": True}]
        assert {index for _, index in parameters(row["sql"], "postgres")} == set(
            range(1, len(row["parameter_values"]) + 1))
        assert parameters(row["sql"], "postgres") == parameters(row["sqlite_input"], "sqlite")
        if row["sqlite_sql"] is not None:
            assert row["sqlite_supported"]
            assert parameters(row["sql"], "postgres") == parameters(row["sqlite_sql"], "sqlite")
    assert sum(row["sqlite_supported"] for row in rows) == 38
    assert sum(row["sqlite_sql"] is not None for row in rows) == 28
    return rows, concrete


def operator_script():
    """Reuse the declared scalar inventory; independently inspect native catalog."""
    signatures = json.loads(SIGNATURES.read_text())
    triples = {(row["operator"], row["left"], row["right"]) for row in signatures}
    assert len(signatures) == len(triples) == 192
    strategy = {"<": 1, "<=": 2, "=": 3, ">=": 4, ">": 5, "<>": 3}
    assert {op for op, _, _ in triples} == strategy.keys()
    signatures += [{"operator": op, "left": "anyarray", "right": "anyarray"} for op in strategy]
    commands, expected = [], []
    for index, signature in enumerate(signatures):
        op = signature["operator"]
        operator, left, right = map(sql_literal, (op, signature["left"], signature["right"]))
        # PostgreSQL <> is supported through the negator of B-tree equality.
        btree_operator = "o.oprnegate" if op == "<>" else "o.oid"
        commands.append(
            f"SELECT {index}, EXISTS(SELECT FROM pg_catalog.pg_operator o "
            "JOIN pg_catalog.pg_proc p ON p.oid=o.oprcode "
            "WHERE o.oprnamespace='pg_catalog'::regnamespace "
            f"AND o.oprname={operator} AND o.oprleft={left}::regtype AND o.oprright={right}::regtype "
            "AND o.oprresult='boolean'::regtype AND p.prorettype='boolean'::regtype "
            "AND p.proisstrict AND NOT p.proretset AND p.pronargs=2 AND p.prokind='f' "
            "AND EXISTS(SELECT FROM pg_catalog.pg_amop a "
            "JOIN pg_catalog.pg_opfamily f ON f.oid=a.amopfamily "
            "JOIN pg_catalog.pg_am am ON am.oid=f.opfmethod "
            "WHERE am.amname='btree' AND f.opfnamespace='pg_catalog'::regnamespace "
            f"AND a.amopstrategy={strategy[op]} AND a.amopopr={btree_operator} "
            "AND a.amoppurpose='s' AND a.amoplefttype=o.oprleft AND a.amoprighttype=o.oprright));")
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
    """Check independent SQLite expectations, including known dialect differences."""
    assert len(cases) == len(canonical), "missing rendered SQLite row comparison"
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
                assert [col[0] for col in cursor.description] == ["v"], (case["id"], cursor.description)
                actual = cursor.fetchall()
                assert actual == [(case["sqlite_value"],)], (case["id"], sql, actual, case["sqlite_value"])
                count += 1
    return count


def runtime_cases():
    examples = [
        ("ROW(CAST($1 AS INTEGER),1) = ROW(1,1)", "text", ["bad integer"], "22P02"),
        ("ROW(1/$1,1) < ROW(2,2)", "int", [0], "22012"),
        ("ROW(CAST($1 AS INTEGER),1) = ROW(1,1)", "text", ["2147483648"], "22003"),
        ("ROW(ARRAY[[1],[2,3]],1) = ROW(ARRAY[[1]],1)", "", [], "2202E"),
        ("ROW(ARRAY['null'::JSONB]::INTEGER[],1) > ROW(ARRAY[1],1)", "", [], "22023"),
    ]
    return [{
        "sql": f"SELECT {expression} AS v;", "parameter_types": types, "parameter_values": values,
        "output_columns": [{"name": "v", "type": "bool", "nullable": True}], "sqlstate": state,
    } for expression, types, values, state in examples]


def error_script(cases, canonical):
    assert len(cases) == len(canonical), "missing rendered row comparison runtime case"
    commands, expected = ["BEGIN;"], {}
    for index, (case, rendered) in enumerate(zip(cases, canonical), 1):
        for form, sql in (("source", case["sql"]), ("postgres", rendered)):
            capture = prepare_capture(sql, case["parameter_types"], case["parameter_values"], error=True)
            key = marker("row_error", index, True, form)
            commands += [*capture[:-1], "\\echo " + key, capture[-1], "DEALLOCATE pagination_parameters;"]
            expected[key] = (1, [[case["sqlstate"]]])
    commands.append("ROLLBACK;")
    return "\n".join(commands), expected


def label_cases():
    return [{
        "sql": f"SELECT ROW(1,2) {operator} ROW(1,3);",
        "parameter_types": "", "parameter_values": [],
        "output_columns": [{"name": "?column?", "type": "bool", "nullable": True}],
        "postgres_display_type": "boolean",
    } for operator in ("=", "<>", "<", "<=", ">", ">=")]


def boundaries():
    invalid = [
        "SELECT ROW() = ROW()", "SELECT ROW() < ROW()",
        "SELECT ROW(1) = ROW(1,2)", "SELECT (1,2) > ROW(1)",
        "SELECT ('1'::TEXT,2) = (1,2)", "SELECT (TRUE,1) < (1,2)",
        "SELECT ('{}'::JSON,1) = ('{}'::JSON,1)",
        "SELECT (ARRAY[1],1) = (ARRAY[1::BIGINT],1)",
        "SELECT ROW(1,2) + ROW(3,4)",
    ]
    unsupported = [
        "SELECT ROW(1,2)", "SELECT (ROW(1,NULL),2) = (ROW(1,NULL),2)",
        "SELECT (NULL::JSON[],1) = (NULL::JSON[],1)",
        "SELECT ROW(1,2) IS NULL", "SELECT ROW(1,2) IN (ROW(1,2))",
        "SELECT ROW(1,2) = NULL",
    ]
    syntax = [
        "SELECT ()", "SELECT (1,)", "SELECT ROW(1,)",
        "SELECT (1,2)[1]", "SELECT ROW(1,2)[1]",
    ]
    for status, queries in (("invalid", invalid), ("unsupported", unsupported)):
        for sql in queries:
            assert_report(["--assurance", "contract", sql], status, "contract")
    for sql in syntax:
        result = invoke(["--render-assurance", "identity", sql])
        report = json.loads(result.stdout)
        assert result.returncode == 1 and report["status"] == "invalid", report
        assert report["diagnostic"]["code"] == "input.parse", report
    assert_report(["--assurance", "checked", "SELECT (1,2) < (1,3)"], "rejected", "checked")
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
    print("PASS: 50 row comparison certificates and 50 unchanged source renderings")
    print(f"PASS: {boundary_count} boundaries; PostgreSQL {version}: {len(values)} value/OID observations")
    print(f"PASS: {len(metadata)} descriptors, {len(expected_errors)} expected errors and {len(operators)} B-tree operators")
    print(f"PASS: SQLite {sqlite3.sqlite_version}: {sqlite_count} source/rendered observations and 12 dialect exclusions")
    print("Scope: finite observations with separate dialect oracles; concrete source SQL is never executed.")


if __name__ == "__main__":
    main()
