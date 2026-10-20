#!/usr/bin/env python3
"""Verify USING/NATURAL certificates and bounded four-population execution."""
from __future__ import annotations
import argparse
import json
from pathlib import Path
import sqlite3

from check_advanced_cli import literal, question_parameters
from check_assurance_cli import assert_report
from check_join_contract_cli import bag, sqlite_bindings, validate_native
from check_locking_cli import copy_cell
from check_pagination_cli import replay
from check_postgresql_cli import connection, copy_result, marker, parse_results, run, sql_identifier, sql_literal
from check_renderer_corpus import parameters
from generate_merged_join_examples import TABLES, population

ROOT = Path(__file__).resolve().parents[1]
CATALOG = ROOT / "fixtures/merged_join_contract/schema.json"
FACTORS = ("using_contract", "natural_contract")
STATES = ("empty", "left_only", "right_only", "both")
SQL_TYPES = {"int": "INTEGER", "bigint": "BIGINT", "text": "TEXT"}
OUTPUT_TYPES = {"int32": "INTEGER", "int64": "BIGINT", "text": "TEXT", "bool": "BOOLEAN"}


def load_cases():
    cases, concrete = [], []
    for factor in FACTORS:
        directory = ROOT / "fixtures" / factor
        synthetic = json.loads((directory / "synthetic.json").read_text())
        sources = [json.loads(line) for line in (directory / "concrete.jsonl").read_text().splitlines()]
        for rows in (synthetic, sources):
            assert len(rows) == len({row["id"] for row in rows}) == len({row["sql"] for row in rows}) == 50
        for case in synthetic:
            assert case["catalogFile"] == "fixtures/merged_join_contract/schema.json"
            assert set(case["expected_rows_by_state"]) == set(STATES)
            assert set(case["sqlite_expected_rows_by_state"]) == set(STATES)
            assert len(case["sqlite_canonical_output_names"]) == len(case["sqlite_output_names"])
            assert case["expected_rows"] == case["expected_rows_by_state"]["both"]
            for rows in case["expected_rows_by_state"].values():
                assert all(len(row) == len(case["output_columns"]) for row in rows)
            for rows in case["sqlite_expected_rows_by_state"].values():
                assert all(len(row) == len(case["sqlite_output_names"]) for row in rows)
            uses = parameters(case["sql"], "postgres")
            assert uses == parameters(case["sqlite_sql"], "sqlite")
            assert {index for _, index in uses} == set(range(1, len(case["parameter_values"]) + 1))
        cases += synthetic
        concrete += sources
    return cases, concrete


def validity(case):
    args = ["--assurance", "contract", "--schema", str(CATALOG)]
    if case["parameter_types"]:
        args += ["--param-types", case["parameter_types"]]
    columns = tuple((c["name"], "bigint" if c["type"] == "int64" else c["type"], c["nullable"])
                    for c in case["output_columns"])
    return assert_report([*args, case["sql"]], "valid", "contract", columns)


def boundaries():
    invalid = [
        "SELECT * FROM left_rows l JOIN right_rows r USING (absent)",
        "SELECT * FROM left_rows l JOIN right_rows r USING (id, id)",
        "SELECT * FROM left_rows l CROSS JOIN right_rows r NATURAL JOIN extras e",
        "SELECT * FROM left_rows l JOIN right_rows l USING (id)",
        "SELECT left_rows.id FROM left_rows l JOIN right_rows r USING (id)",
        "SELECT l.id FROM left_rows l FULL JOIN right_rows r USING (id) FOR UPDATE OF l",
        "SELECT * FROM left_rows l LEFT JOIN right_rows r USING (id) FOR UPDATE OF r",
        "SELECT * FROM left_rows l FULL JOIN right_rows r USING (id) FOR UPDATE",
    ]
    valid = [
        "SELECT * FROM (SELECT id FROM left_rows) l JOIN right_rows r USING (id)",
        "SELECT * FROM left_rows l NATURAL JOIN (SELECT id FROM right_rows) r",
    ]
    for status, queries in (("invalid", invalid), ("valid", valid)):
        for sql in queries:
            assert_report(["--assurance", "contract", "--schema", str(CATALOG), sql], status, "contract")
    return len(invalid) + len(valid)


def table_statements():
    return ["CREATE TEMP TABLE " + sql_identifier(name) + " (" +
            ", ".join(sql_identifier(field) + " " + SQL_TYPES[type_] +
                      ("" if nullable else " NOT NULL") for field, type_, nullable in columns) + ");"
            for name, columns in TABLES.items()]


def prepare_capture(case, sql):
    types = ", ".join(SQL_TYPES[type_.removesuffix("?")] for type_ in case["parameter_types"].split(",") if type_)
    declaration = f" ({types})" if types else ""
    execute = "EXECUTE merged_parameters"
    if case["parameter_values"]:
        execute += " (" + ", ".join(map(literal, case["parameter_values"])) + ")"
    # Positional output names permit real SQL's duplicate projected labels.
    # PostgreSQL enforces each RETURN QUERY scalar type; SQLite independently
    # checks the original projected labels as well as the typed-AST certificate.
    signature = ", ".join(f"c{index} {OUTPUT_TYPES[col['type']]}"
                          for index, col in enumerate(case["output_columns"]))
    body = "BEGIN RETURN QUERY EXECUTE " + sql_literal(execute) + "; END;"
    function = ("CREATE OR REPLACE FUNCTION pg_temp.merged_rows() RETURNS TABLE (" + signature +
                ") LANGUAGE plpgsql VOLATILE AS " + sql_literal(body) + ";")
    return [f"PREPARE merged_parameters{declaration} AS {question_parameters(sql).strip().removesuffix(';')};",
            function, copy_result("SELECT * FROM pg_temp.merged_rows()")]


def postgres_script(cases, canonical):
    assert len(cases) == len(canonical), "missing canonical merged JOIN query"
    commands = ["\\encoding UTF8", "BEGIN;", "SET LOCAL statement_timeout = '5s';",
                "SET LOCAL standard_conforming_strings = on;", *table_statements()]
    expected = {}
    for state in STATES:
        commands += ["TRUNCATE " + ", ".join(map(sql_identifier, TABLES)) + ";"]
        for name, rows in population(state).items():
            if rows:
                commands.append("INSERT INTO " + sql_identifier(name) + " VALUES " +
                                ", ".join("(" + ", ".join(map(literal, row)) + ")" for row in rows) + ";")
        for index, (case, rendered) in enumerate(zip(cases, canonical), 1):
            for form, sql in (("source", case["sql"]), ("postgres", rendered)):
                key = marker("merged_" + state, index, state != "empty", form)
                capture = prepare_capture(case, sql)
                commands += ["SAVEPOINT merged_case;", *capture[:-1], "\\echo " + key, capture[-1],
                             "DEALLOCATE merged_parameters;", "ROLLBACK TO SAVEPOINT merged_case;",
                             "RELEASE SAVEPOINT merged_case;"]
                expected[key] = (len(case["output_columns"]),
                                 [[copy_cell(v) for v in row] for row in case["expected_rows_by_state"][state]])
    commands.append("ROLLBACK;")
    return "\n".join(commands), expected


def sqlite_observations(cases, canonical):
    assert len(cases) == len(canonical), "missing SQLite merged JOIN query"
    assert sqlite3.sqlite_version_info >= (3, 39, 0), "SQLite 3.39+ required"
    count = 0
    with sqlite3.connect(":memory:") as database:
        for command in table_statements():
            database.execute(command)
        for state in STATES:
            for name, rows in population(state).items():
                database.execute(f'DELETE FROM "{name}"')
                slots = ", ".join("?" for _ in TABLES[name])
                database.executemany(f'INSERT INTO "{name}" VALUES ({slots})', rows)
            for case, rendered in zip(cases, canonical):
                for form, sql in (("source", case["sqlite_sql"]), ("sqlite", rendered)):
                    cursor = database.execute(sql, sqlite_bindings(sql, case["parameter_values"]))
                    names = case["sqlite_output_names" if form == "source" else "sqlite_canonical_output_names"]
                    assert [col[0] for col in cursor.description] == names, (
                        case["id"], state, form, [c[0] for c in cursor.description], names)
                    rows = cursor.fetchall()
                    assert bag(rows) == bag(case["sqlite_expected_rows_by_state"][state]), (case["id"], state, form, rows)
                    count += 1
    return count


TYPE_PAIRS = [
    ("integer", "bigint", "bigint"),
    ("real", "integer", "real"),
    ("numeric(4,2)", "numeric(4,2)", "numeric(4,2)"),
    ("numeric(4,2)", "numeric(5,2)", "numeric"),
    ("character varying(4)", "character varying(4)", "character varying(4)"),
    ("character varying(4)", "character varying(7)", "character varying"),
    ("character(4)", "character(4)", "character(4)"),
    ("timestamp(2)", "timestamp(3)", "timestamp without time zone"),
]


def type_script():
    statements, expected = ["BEGIN;"], []
    for index, (left, right, merged) in enumerate(TYPE_PAIRS):
        statements += [
            "CREATE TEMP TABLE type_left(k " + left + ");",
            "CREATE TEMP TABLE type_right(k " + right + ");",
            "CREATE TEMP VIEW type_merged AS SELECT k AS merged, l.k AS original_left, r.k AS original_right "
            "FROM type_left l FULL JOIN type_right r USING(k);",
            "SELECT format_type(atttypid, atttypmod) FROM pg_attribute "
            "WHERE attrelid='pg_temp.type_merged'::regclass AND attnum>0 ORDER BY attnum;",
            "DROP VIEW type_merged; DROP TABLE type_left, type_right;",
        ]
        # format_type expands timestamp's implicit timezone spelling.
        expected.extend([merged, left.replace("timestamp(2)", "timestamp(2) without time zone"),
                         right.replace("timestamp(3)", "timestamp(3) without time zone")])
    statements.append("ROLLBACK;")
    return "\n".join(statements), expected


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    target = parser.add_mutually_exclusive_group(required=True)
    target.add_argument("--local-bin")
    target.add_argument("--dsn")
    parser.add_argument("--psql")
    args = parser.parse_args()
    cases, concrete = load_cases()
    postgres, sqlite = [], []
    for case in cases:
        validity(case)
        replay("identity", case["sql"])
        postgres.append(replay("postgres", case["sql"])["sql"])
        sqlite.append(replay("sqlite", case["sqlite_sql"])["sql"])
    for case in concrete:
        for mode in ("identity", "postgres"):
            replay(mode, case["sql"])
    boundary_count = boundaries()
    sqlite_count = sqlite_observations(cases, sqlite)
    script, expected = postgres_script(cases, postgres)
    with connection(args) as psql:
        result = run([*psql, "-X", "-q", "-v", "ON_ERROR_STOP=1"], input=script, timeout=120)
        validate_native(parse_results(result.stdout), expected)
        probe, types = type_script()
        result = run([*psql, "-X", "-qAt", "-v", "ON_ERROR_STOP=1"], input=probe)
        assert result.stdout.splitlines() == types, (result.stdout, types)
        version = run([*psql, "-X", "-At", "-c", "SHOW server_version;"]).stdout.strip()
    print("PASS: each of USING and NATURAL has 50 complete synthetic certificates and 50 unchanged source renderings")
    print(f"PASS: {boundary_count} boundaries; PostgreSQL {version}: {len(expected)} bound row observations and {len(TYPE_PAIRS)} type/typmod triples")
    print(f"PASS: SQLite {sqlite3.sqlite_version}: {sqlite_count} bound row/label observations across four populations")
    print("SQLite wildcard ordering/merged-key values use separate authored expectations; PostgreSQL output schemas are not assumed equivalent.")
    print("Scope: fixed static rules and finite execution observations; concrete source SQL is never executed.")


if __name__ == "__main__":
    main()
