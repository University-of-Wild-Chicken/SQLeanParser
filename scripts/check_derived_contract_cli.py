#!/usr/bin/env python3
"""Check independent derived-source contracts and finite native observations."""
import argparse
import json
from pathlib import Path
import sqlite3
import subprocess

from check_advanced_cli import literal
from check_assurance_cli import assert_report
from check_join_contract_cli import bag, sqlite_bindings, validate_native
from check_locking_cli import copy_cell
from check_merged_join_cli import prepare_capture
from check_pagination_cli import EXE, replay
from check_postgresql_cli import connection, marker, parse_results, run, sql_identifier
from check_renderer_corpus import parameters
from generate_derived_contract_examples import STATES, TABLES, population

ROOT = Path(__file__).resolve().parents[1]
FIXTURES = ROOT / "fixtures/derived_contract"
SQL_TYPES = {"int": "INTEGER", "text": "TEXT"}


def load_cases():
    cases = json.loads((FIXTURES / "synthetic.json").read_text())
    concrete = [json.loads(line) for line in (FIXTURES / "concrete.jsonl").read_text().splitlines()]
    for rows in (cases, concrete):
        assert len(rows) == len({row["id"] for row in rows}) == len({row["sql"] for row in rows}) == 50
    assert sum(case["sqlite_supported"] for case in cases) == 40
    for case in cases:
        assert case["catalogFile"] == "fixtures/derived_contract/schema.json"
        assert set(case["expected_rows_by_state"]) == set(STATES)
        assert case["expected_rows"] == case["expected_rows_by_state"]["both"]
        assert all(len(row) == len(case["output_columns"])
                   for rows in case["expected_rows_by_state"].values() for row in rows)
        uses = parameters(case["sql"], "postgres")
        assert uses == parameters(case["sqlite_sql"], "sqlite")
        assert {index for _, index in uses} == set(range(1, len(case["parameter_values"]) + 1))
    return cases, concrete


def validity(case):
    args = ["--assurance", "contract", "--schema", str(FIXTURES / "schema.json")]
    if case["parameter_types"]:
        args += ["--param-types", case["parameter_types"]]
    columns = tuple((c["name"], c["type"], c["nullable"]) for c in case["output_columns"])
    return assert_report([*args, case["sql"]], "valid", "contract", columns)


def boundaries():
    invalid = [
        "SELECT items.id FROM (SELECT id FROM items) d",
        "SELECT d.id FROM (SELECT id, id FROM items) d",
        "SELECT * FROM (SELECT id FROM items) d(a, b)",
        "SELECT * FROM items i CROSS JOIN (SELECT i.id) d",
        "SELECT * FROM (SELECT absent FROM items) d",
        "SELECT * FROM items d CROSS JOIN (SELECT 1 AS id) d",
        "SELECT * FROM (SELECT id FROM items) d WHERE d.id",
        "SELECT * FROM (SELECT id FROM items) d ORDER BY items.id",
    ]
    unsupported = [
        # A missing qualified scalar field can denote function-on-whole-row
        # notation; its function environment is outside this contract.
        "SELECT d.absent FROM (SELECT id FROM items) d",
        "SELECT * FROM items i CROSS JOIN LATERAL (SELECT i.id) d",
        "SELECT * FROM (SELECT COUNT(*) AS n FROM items) d",
        "SELECT * FROM (SELECT id FROM items) d FOR UPDATE",
        "SELECT * FROM (SELECT id FROM items) d FOR UPDATE OF d",
    ]
    valid = [
        "SELECT * FROM (SELECT id, id FROM items) d",
        "SELECT d.* FROM (SELECT id, score FROM items) d(x, x)",
        "SELECT i.id FROM items i CROSS JOIN (SELECT id FROM labels) d FOR UPDATE OF i",
        "SELECT * FROM (SELECT id FROM items FOR UPDATE) d",
    ]
    for status, queries in (("invalid", invalid), ("unsupported", unsupported), ("valid", valid)):
        for sql in queries:
            assert_report(["--assurance", "contract", "--schema", str(FIXTURES / "schema.json"), sql],
                          status, "contract")
    # Set-operation contracts now apply inside derived sources. Both declared
    # inputs expose a nonnullable INTEGER id, which retains no collation.
    report = assert_report(
        ["--assurance", "contract", "--schema", str(FIXTURES / "schema.json"),
         "SELECT * FROM (SELECT id FROM items UNION SELECT id FROM labels) d"],
        "valid", "contract", (("id", "int32", False),))
    assert report.get("outputCollations") == [None], report
    return len(invalid) + len(unsupported) + len(valid) + 1


def reject_sqlite(case):
    # Source-column alias lists have no SQLite rendering rule. No AST rewrite
    # silently turns them into aliases in a different query.
    result = subprocess.run([str(EXE), "--render-assurance", "sqlite"], input=case["sql"],
                            cwd=ROOT, capture_output=True, text=True, timeout=30)
    if result.stdout:
        report = json.loads(result.stdout)
        assert result.returncode == 3 and report["status"] == "unsupported", report
        assert "relation-column-aliases" in str(report), report
    else:
        assert result.returncode == 1 and "column" in result.stderr.lower(), result.stderr


def table_statements():
    return ["CREATE TEMP TABLE " + sql_identifier(name) + " (" +
            ", ".join(sql_identifier(field) + " " + SQL_TYPES[type_] +
                      ("" if nullable else " NOT NULL") for field, type_, nullable in columns) + ");"
            for name, columns in TABLES.items()]


def postgres_script(cases, canonical):
    assert len(cases) == len(canonical), "missing canonical derived-source query"
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
                key = marker("derived_" + state, index, state != "empty", form)
                capture = prepare_capture(case, sql)
                commands += ["SAVEPOINT derived_case;", *capture[:-1], "\\echo " + key, capture[-1],
                             "DEALLOCATE merged_parameters;", "ROLLBACK TO SAVEPOINT derived_case;",
                             "RELEASE SAVEPOINT derived_case;"]
                expected[key] = (len(case["output_columns"]),
                                 [[copy_cell(v) for v in row] for row in case["expected_rows_by_state"][state]])
    commands.append("ROLLBACK;")
    return "\n".join(commands), expected


def sqlite_observations(cases, canonical):
    assert len(cases) == len(canonical), "missing SQLite derived-source query"
    assert all(case["sqlite_supported"] for case in cases), "unsupported SQLite case was executed"
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
                    names = [column["name"] for column in case["output_columns"]]
                    assert [c[0] for c in cursor.description] == names, (case["id"], state, form)
                    rows = cursor.fetchall()
                    assert bag(rows) == bag(case["expected_rows_by_state"][state]), (case["id"], state, form, rows)
                    count += 1
    return count


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    target = parser.add_mutually_exclusive_group(required=True)
    target.add_argument("--local-bin")
    target.add_argument("--dsn")
    parser.add_argument("--psql")
    args = parser.parse_args()
    cases, concrete = load_cases()
    postgres, sqlite_cases, sqlite = [], [], []
    for case in cases:
        validity(case)
        replay("identity", case["sql"])
        postgres.append(replay("postgres", case["sql"])["sql"])
        if case["sqlite_supported"]:
            sqlite_cases.append(case)
            sqlite.append(replay("sqlite", case["sqlite_sql"])["sql"])
        else:
            reject_sqlite(case)
    for case in concrete:
        for mode in ("identity", "postgres"):
            replay(mode, case["sql"])
    boundary_count = boundaries()
    sqlite_count = sqlite_observations(sqlite_cases, sqlite)
    script, expected = postgres_script(cases, postgres)
    with connection(args) as psql:
        result = run([*psql, "-X", "-q", "-v", "ON_ERROR_STOP=1"], input=script, timeout=120)
        validate_native(parse_results(result.stdout), expected)
        version = run([*psql, "-X", "-At", "-c", "SHOW server_version;"]).stdout.strip()
    print("PASS: 50 derived-source complete synthetic certificates and 50 unchanged source renderings")
    print(f"PASS: {boundary_count} boundaries; PostgreSQL {version}: {len(expected)} bound positional type/row observations")
    print(f"PASS: SQLite {sqlite3.sqlite_version}: {sqlite_count} bound row/label observations; 10 explicit alias-list rejections")
    print("Scope: independent static rules and four finite populations; concrete source SQL is never executed.")


if __name__ == "__main__":
    main()
