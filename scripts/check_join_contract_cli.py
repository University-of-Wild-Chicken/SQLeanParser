#!/usr/bin/env python3
"""Independent JOIN validity plus finite PostgreSQL and SQLite observations."""
from __future__ import annotations

import argparse
from collections import Counter
import json
from pathlib import Path
import sqlite3

from check_assurance_cli import assert_report
from check_locking_cli import copy_cell, prepare_capture
from check_pagination_cli import replay
from check_postgresql_cli import connection, marker, parse_results, run, sql_identifier
from check_renderer_corpus import parameters
from generate_join_contract_examples import DATA, KINDS, TABLES
from check_advanced_cli import literal

ROOT = Path(__file__).resolve().parents[1]
FIXTURES = ROOT / "fixtures/join_contract"
SQL_TYPES = {"int": "INTEGER", "text": "TEXT"}


def load_cases():
    synthetic = json.loads((FIXTURES / "synthetic.json").read_text())
    concrete = [json.loads(line) for line in (FIXTURES / "concrete.jsonl").read_text().splitlines()]
    for population in (synthetic, concrete):
        assert len(population) == len({row["id"] for row in population}) == 50
        assert len({row["sql"] for row in population}) == 50
    assert Counter(row["join_kind"] for row in synthetic) == {kind.lower(): 10 for kind in KINDS}
    for case in synthetic:
        assert case["catalogFile"] == "fixtures/join_contract/schema.json"
        assert parameters(case["sql"], "postgres") == parameters(case["sqlite_sql"], "sqlite")
        indexes = {index for _, index in parameters(case["sql"], "postgres")}
        assert indexes == set(range(1, len(case["parameter_values"]) + 1))
        assert len(case["parameter_types"].split(",")) == len(indexes) if indexes else not case["parameter_types"]
        assert all(len(row) == len(case["output_columns"]) for row in case["expected_rows"])
    return synthetic, concrete


def validity(case):
    args = ["--assurance", "contract", "--schema", str(FIXTURES / "schema.json")]
    if case["parameter_types"]:
        args += ["--param-types", case["parameter_types"]]
    columns = tuple((col["name"], col["type"], col["nullable"]) for col in case["output_columns"])
    return assert_report([*args, case["sql"]], "valid", "contract", columns)


def boundaries():
    invalid = [
        "SELECT id FROM users u JOIN orders o ON u.id = o.user_id",
        "SELECT users.id FROM users u JOIN orders o ON u.id = o.user_id",
        "SELECT u.id FROM users u JOIN orders u ON TRUE",
        "SELECT u.id FROM users u JOIN orders o ON 1",
        "SELECT u.id FROM users u JOIN orders o ON u.name = o.amount",
        "SELECT u.id FROM users u JOIN orders o ON CAST('true' AS TEXT)",
        "SELECT u.id AS x FROM users u JOIN orders o ON x = o.user_id",
        "SELECT u.id FROM users u JOIN orders o ON r.id = o.user_id LEFT JOIN regions r ON u.id = r.id",
        "SELECT u.id FROM users u LEFT JOIN orders o ON u.id = o.user_id FOR UPDATE",
        "SELECT u.id FROM users u LEFT JOIN orders o ON u.id = o.user_id FOR UPDATE OF o",
        "SELECT u.id FROM users u RIGHT JOIN orders o ON u.id = o.user_id FOR SHARE OF u",
        "SELECT u.id FROM users u FULL JOIN orders o ON u.id = o.user_id FOR KEY SHARE OF o",
    ]
    valid = [
        "SELECT * FROM users JOIN orders USING (id)",
        "SELECT * FROM users NATURAL JOIN orders",
        "SELECT * FROM users u JOIN (SELECT id FROM orders) o ON u.id = o.id",
    ]
    unsupported = [
        "SELECT u.id FROM users u JOIN orders o ON 'true'",
        "SELECT u.id FROM users u JOIN orders o ON u.id = o.user_id WHERE 'true'",
    ]
    for status, queries in (("invalid", invalid), ("unsupported", unsupported), ("valid", valid)):
        for sql in queries:
            assert_report(["--assurance", "contract", "--schema", str(FIXTURES / "schema.json"), sql],
                          status, "contract")
    return len(invalid) + len(unsupported) + len(valid)


def table_statements(temporary=False):
    return [
        "CREATE " + ("TEMP " if temporary else "") + "TABLE " + sql_identifier(name) + " (" +
        ", ".join(sql_identifier(field) + " " + SQL_TYPES[kind] + " NOT NULL"
                  for field, kind in fields) + ");"
        for name, fields in TABLES.items()
    ]


def insert_statements():
    return [
        "INSERT INTO " + sql_identifier(name) + " VALUES " +
        ", ".join("(" + ", ".join(map(literal, row)) + ")" for row in rows) + ";"
        for name, rows in DATA.items()
    ]


def bag(rows):
    return Counter(tuple(row) for row in rows)


def postgres_script(cases, canonical):
    assert len(cases) == len(canonical), "missing canonical JOIN case"
    commands = ["\\encoding UTF8", "BEGIN;", "SET LOCAL statement_timeout = '5s';",
                "SET LOCAL standard_conforming_strings = on;", *table_statements(True)]
    expected = {}
    for populated in (False, True):
        if populated:
            commands += insert_statements()
        for index, (case, rendered) in enumerate(zip(cases, canonical), 1):
            for form, sql in (("source", case["sql"]), ("postgres", rendered)):
                capture = prepare_capture(sql, case["parameter_types"], case["parameter_values"],
                                          case["output_columns"])
                key = marker("join_contract", index, populated, form)
                commands += ["SAVEPOINT join_case;", *capture[:-1], "\\echo " + key, capture[-1],
                             "DEALLOCATE locking_parameters;", "ROLLBACK TO SAVEPOINT join_case;",
                             "RELEASE SAVEPOINT join_case;"]
                rows = case["expected_rows"] if populated else []
                expected[key] = (len(case["output_columns"]), [[copy_cell(v) for v in row] for row in rows])
    commands.append("ROLLBACK;")
    return "\n".join(commands), expected


def validate_native(actual, expected):
    assert actual.keys() == expected.keys(), actual.keys() ^ expected.keys()
    for key, (arity, wanted) in expected.items():
        actual_arity, rows = actual[key]
        assert actual_arity == arity and bag(rows) == bag(wanted), (key, actual[key], expected[key])
    return len(expected)


def sqlite_bindings(sql, values):
    uses = parameters(sql, "sqlite")
    if uses and all(kind == "numbered" for kind, _ in uses):
        return {str(index): value for index, value in enumerate(values, 1)}
    return values


def sqlite_observations(cases, canonical):
    assert len(cases) == len(canonical), "missing SQLite JOIN case"
    assert sqlite3.sqlite_version_info >= (3, 39, 0), "SQLite 3.39+ required for RIGHT/FULL JOIN"
    observed = 0
    with sqlite3.connect(":memory:") as database:
        for command in table_statements():
            database.execute(command)
        for populated in (False, True):
            if populated:
                for name, rows in DATA.items():
                    slots = ", ".join("?" for _ in TABLES[name])
                    database.executemany(f'INSERT INTO "{name}" VALUES ({slots})', rows)
            for case, rendered in zip(cases, canonical):
                for form, sql in (("source", case["sqlite_sql"]), ("sqlite", rendered)):
                    cursor = database.execute(sql, sqlite_bindings(sql, case["parameter_values"]))
                    assert [col[0] for col in cursor.description] == [col["name"] for col in case["output_columns"]]
                    rows = cursor.fetchall()
                    expected = case["expected_rows"] if populated else []
                    assert bag(rows) == bag(expected), (case["id"], populated, form, rows, expected)
                    observed += 1
    return observed


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
        actual = parse_results(result.stdout)
        validate_native(actual, expected)
        version = run([*psql, "-X", "-At", "-c", "SHOW server_version;"]).stdout.strip()
    print("PASS: 50 JOIN full-query certificates and 50 unchanged source rendering examples")
    print(f"PASS: {boundary_count} validity boundaries; PostgreSQL {version}: {len(expected)} separately bound row observations")
    print(f"PASS: SQLite {sqlite3.sqlite_version}: {sqlite_count} bound source/canonical row and label observations")
    print("Scope: independent static JOIN rules and finite database observations; concrete source SQL is never executed.")


if __name__ == "__main__":
    main()
