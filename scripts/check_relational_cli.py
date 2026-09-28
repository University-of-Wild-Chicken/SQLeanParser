#!/usr/bin/env python3
"""Certify the 200 relational examples and independently check them with SQLite.

Run `lake build` first. Uses only Python's standard library. Both source and
canonical SELECTs are compiled with EXPLAIN, then compared on a small seeded,
in-memory database covering missing matches, duplicate values, and empty input.
These checks test interoperability and rendering; they do not prove execution
semantics or equivalence on arbitrary databases.
"""

from __future__ import annotations

import json
from pathlib import Path
import sqlite3
import subprocess


ROOT = Path(__file__).resolve().parents[1]
EXE = ROOT / ".lake/build/bin/sqlean"
SCHEMA = ROOT / "fixtures/relational/schema.json"


def run(args: list[str], code: int = 0, contains: str = "") -> str:
    result = subprocess.run([str(EXE), *args], text=True, capture_output=True, cwd=ROOT, check=False)
    assert result.returncode == code, (args, result.returncode, result.stdout, result.stderr)
    assert contains in result.stdout + result.stderr, (args, contains, result.stdout, result.stderr)
    return result.stdout


def quote_identifier(name: str) -> str:
    return '"' + name.replace('"', '""') + '"'


def create_database(schema: dict, populated: bool) -> sqlite3.Connection:
    db = sqlite3.connect(":memory:")
    sql_types = {"int": "INTEGER", "text": "TEXT", "bool": "BOOLEAN"}
    for table in schema["tables"]:
        columns = ", ".join(
            f'{quote_identifier(column["name"])} {sql_types[column["type"]]} NOT NULL'
            for column in table["columns"]
        )
        db.execute(f'CREATE TABLE {quote_identifier(table["name"])} ({columns})')
    if populated:
        seed = {
            "users": [(1, 24, "Alice", "Paris"), (2, 17, "Bob", "Paris"), (3, 38, "Carol", "Rome"),
                      (4, 71, "Dora", "Rome"), (5, 33, "O'Brien", ""), (6, 40, "Fran", "Paris")],
            "orders": [(101, 1, 120, "paid"), (102, 1, 50, "paid"), (103, 2, 50, "pending"),
                       (104, 3, 220, "paid"), (105, 999, 10, "cancelled"), (106, 1, 0, "pending")],
            "departments": [(1, "Engineering"), (2, "Sales"), (3, "Vacant")],
            "employees": [(1, 1, 99, "Ann", 100), (2, 1, 1, "Ben", 80),
                          (3, 2, 1, "Cara", 90), (4, 77, 99, "Dale", 70)],
            "flags": [(1, True, "Enabled"), (2, False, "Disabled"), (3, True, "Preview")],
        }
        for name, rows in seed.items():
            placeholders = ", ".join("?" for _ in rows[0])
            db.executemany(f'INSERT INTO {quote_identifier(name)} VALUES ({placeholders})', rows)
    return db


def main() -> None:
    if not EXE.is_file():
        raise SystemExit("Build the CLI first: lake build")
    if sqlite3.sqlite_version_info < (3, 39, 0):
        raise SystemExit("SQLite 3.39 or newer is required for RIGHT and FULL joins")
    schema = json.loads(SCHEMA.read_text())
    databases = [create_database(schema, populated) for populated in (False, True)]
    total = 0
    for category in ("joins", "grouping", "subqueries", "ctes"):
        sources = (ROOT / f"fixtures/relational/{category}.sql").read_text().splitlines()
        assert len(sources) == len(set(sources)) == 50, category
        for index, source in enumerate(sources, 1):
            try:
                output = run(["--schema", str(SCHEMA), source], contains="Valid query.")
                canonical = output.splitlines()[-1]
                for db in databases:
                    db.execute("EXPLAIN " + source).fetchall()
                    db.execute("EXPLAIN " + canonical).fetchall()
                    original_result = db.execute(source)
                    original_arity = len(original_result.description)
                    original_rows = original_result.fetchall()
                    canonical_result = db.execute(canonical)
                    assert len(canonical_result.description) == original_arity
                    assert canonical_result.fetchall() == original_rows, (source, canonical)
            except Exception as error:
                raise AssertionError(f"{category} example {index}: {source}") from error
            total += 1
    for db in databases:
        db.close()

    negative = [
        ("SELECT id FROM users u JOIN orders o ON u.id = o.user_id", "validation error"),
        ("SELECT u.id FROM users u JOIN orders o ON u.id + o.user_id", "validation error"),
        ("SELECT u.id FROM users u JOIN orders o", "parse error"),
        ("SELECT u.id FROM users u CROSS JOIN orders o ON u.id = o.user_id", "parse error"),
        ("SELECT u.id FROM users u JOIN orders u ON u.id = u.user_id", "validation error"),
        ("SELECT u.id FROM users u JOIN orders o USING (id)", "parse error"),
        ("SELECT city, name, COUNT(*) FROM users GROUP BY city", "validation error"),
        ("SELECT SUM(name) FROM users", "validation error"),
        ("SELECT SUM(COUNT(*)) FROM users", "validation error"),
        ("SELECT COUNT(*) FROM users WHERE COUNT(*) > 0", "validation error"),
        ("SELECT city FROM users GROUP BY COUNT(*)", "validation error"),
        ("SELECT COUNT(*) FROM users HAVING name = 'Alice'", "validation error"),
        ("SELECT x.id FROM (SELECT id FROM users)", "parse error"),
        ("SELECT x.missing FROM (SELECT id FROM users) AS x", "validation error"),
        ("SELECT x.id FROM (SELECT u.id FROM users) AS x", "validation error"),
        ("WITH x AS (SELECT id FROM users) SELECT missing FROM x", "validation error"),
        ("WITH x AS (SELECT id FROM y), y AS (SELECT id FROM users) SELECT id FROM x", "validation error"),
        ("WITH x AS (SELECT id FROM x) SELECT id FROM x", "validation error"),
        ("WITH x(a, b) AS (SELECT id FROM users) SELECT a FROM x", "validation error"),
        ("WITH x AS (SELECT id FROM users), x AS (SELECT id FROM orders) SELECT id FROM x", "validation error"),
    ]
    for source, message in negative:
        run(["--schema", str(SCHEMA), source], 1, message)
    print(f"PASS: {total} relational examples certified by the CLI and compiled by SQLite (source + canonical)")
    print(f"PASS: source and canonical results agree on empty and populated databases ({total * 2} comparisons)")
    print(f"PASS: {len(negative)} relational CLI rejection cases")


if __name__ == "__main__":
    main()
