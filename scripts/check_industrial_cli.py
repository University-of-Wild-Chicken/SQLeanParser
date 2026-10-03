#!/usr/bin/env python3
"""Certify 150 industrial SQL examples and compare execution with SQLite.

The source and canonical SQL must have identical result rows on empty and seeded
in-memory databases. Independent result oracles check bounded arithmetic,
hierarchy depth, a cyclic graph using UNION deduplication, and parts quantities.
A SQLite VM-instruction budget protects every execution against runaway recursion.
These finite checks do not establish execution equivalence on arbitrary inputs.
"""

from __future__ import annotations

import json
from pathlib import Path
import sqlite3
import subprocess

from check_relational_cli import create_database

ROOT = Path(__file__).resolve().parents[1]
EXE = ROOT / ".lake/build/bin/sqlean"
FIXTURE_DIR = ROOT / "fixtures/industrial"
SCHEMA = FIXTURE_DIR / "schema.json"


def run(source: str, code: int = 0) -> str:
    result = subprocess.run([str(EXE), "--schema", str(SCHEMA), source], text=True,
                            capture_output=True, cwd=ROOT, check=False, timeout=10)
    assert result.returncode == code, (source, result.returncode, result.stdout, result.stderr)
    assert ("Valid query." if code == 0 else "error") in result.stdout + result.stderr
    return result.stdout


def execute(db: sqlite3.Connection, sql: str) -> tuple[int, list[tuple]]:
    callbacks = 0

    def progress() -> bool:
        nonlocal callbacks
        callbacks += 1
        return callbacks >= 500

    db.set_progress_handler(progress, 1000)
    try:
        cursor = db.execute(sql)
        return len(cursor.description or []), cursor.fetchall()
    finally:
        db.set_progress_handler(None, 0)


def industrial_database(schema: dict, populated: bool) -> sqlite3.Connection:
    db = create_database(schema, populated)
    if populated:
        db.executemany("INSERT INTO employees VALUES (?, ?, ?, ?, ?)",
                       [(5, 1, 2, "Evan", 60), (6, 2, 3, "Fran", 65)])
        # The 1 -> 2 -> 3 -> 1 cycle must terminate by UNION deduplication.
        db.executemany("INSERT INTO edges VALUES (?, ?)",
                       [(1, 2), (2, 3), (3, 1), (3, 4), (2, 4), (8, 9)])
        # Component 5 is reached through two distinct acyclic assembly paths.
        db.executemany("INSERT INTO parts VALUES (?, ?, ?)",
                       [(1, 2, 2), (1, 3, 3), (2, 4, 4), (2, 5, 1), (3, 5, 2)])
    return db


def main() -> None:
    if not EXE.is_file():
        raise SystemExit("Build the CLI first: lake build")
    schema = json.loads(SCHEMA.read_text())
    databases = [industrial_database(schema, populated) for populated in (False, True)]
    rows_by_case: dict[tuple[str, int, bool], list[tuple]] = {}
    total = 0
    for category in ("recursive_ctes", "unions", "source_free"):
        sources = (FIXTURE_DIR / f"{category}.sql").read_text().splitlines()
        assert len(sources) == len(set(sources)) == 50, category
        for index, source in enumerate(sources, 1):
            try:
                canonical = run(source).splitlines()[-1]
                for populated, db in zip((False, True), databases):
                    execute(db, "EXPLAIN " + source)
                    execute(db, "EXPLAIN " + canonical)
                    original_arity, original_rows = execute(db, source)
                    canonical_arity, canonical_rows = execute(db, canonical)
                    assert original_arity == canonical_arity
                    assert original_rows == canonical_rows, (source, canonical)
                    rows_by_case[category, index, populated] = original_rows
            except Exception as error:
                raise AssertionError(f"{category} example {index}: {source}") from error
            total += 1

    # Independent expected values; these catch common branch/rendering mistakes
    # that merely comparing the source with the canonical spelling could miss.
    oracles = [
        ("recursive_ctes", 1, False, [(n,) for n in range(1, 11)]),
        ("recursive_ctes", 2, True, [(n,) for n in range(0, 9, 2)]),
        ("recursive_ctes", 6, False,
         [(0, 0, 1), (1, 1, 1), (2, 1, 2), (3, 2, 3), (4, 3, 5), (5, 5, 8),
          (6, 8, 13), (7, 13, 21), (8, 21, 34), (9, 34, 55), (10, 55, 89)]),
        ("recursive_ctes", 7, True, [(1, 1), (2, 2), (3, 6), (4, 24), (5, 120), (6, 720)]),
        ("recursive_ctes", 15, True, [(42,)]),
        ("recursive_ctes", 17, True, [(1,), (0,)]),
        ("recursive_ctes", 18, True, [(1,), (-1,)]),
        ("recursive_ctes", 30, True, [(0, 2), (1, 2), (2, 2)]),
        ("recursive_ctes", 31, True, [(2,)]),
        ("recursive_ctes", 31, False, [(None,)]),
        ("recursive_ctes", 36, True, [(1,), (2,), (3,), (4,)]),
        ("recursive_ctes", 37, False, [(1,)]),
        ("recursive_ctes", 40, True, [(404,)]),
        ("recursive_ctes", 43, True, [(2, 2), (3, 3), (4, 8), (5, 8)]),
        ("recursive_ctes", 44, True, [(5,)]),
        ("recursive_ctes", 47, True, [(2,), (4,), (6,), (8,), (10,)]),
        ("unions", 9, False, [(1,), (2,)]),
        ("unions", 10, False, [(1,), (1,)]),
        ("unions", 11, False, [(1,), (2,), (3,)]),
        ("unions", 45, False, [(8,)]),
        ("source_free", 15, False, [(14,)]),
        ("source_free", 16, True, [(20,)]),
        ("source_free", 36, True, []),
        ("source_free", 43, False, [(1,)]),
        ("source_free", 49, True, [(0,)]),
    ]
    for category, index, populated, expected in oracles:
        actual = rows_by_case[category, index, populated]
        assert actual == expected, (category, index, populated, actual, expected)

    negative = [
        "SELECT 1 UNION SELECT 'text'",
        "SELECT 1, 2 UNION ALL SELECT 3",
        "SELECT SUM(amount) FROM orders UNION ALL SELECT amount FROM orders",
        "SELECT AVG(amount) FROM orders UNION SELECT SUM(amount) FROM orders",
        "SELECT 1 AS n UNION SELECT 2 ORDER BY missing",
        "SELECT id FROM users UNION SELECT id FROM employees ORDER BY users.id",
        "SELECT 1 AS n UNION SELECT 2 ORDER BY n + 1",
        "SELECT 1 UNION SELECT 2 ORDER BY 2",
        "SELECT 1 ORDER BY 1 UNION SELECT 2",
        "SELECT 1 UNION ALL",
        "SELECT *",
        "SELECT missing",
        "SELECT users.id",
        "SELECT 1 WHERE 3",
        "SELECT 1 OFFSET 2",
        "WITH RECURSIVE x(n) AS (SELECT 1 UNION ALL SELECT n + 1 FROM x WHERE n < 3) SELECT missing FROM x",
        "WITH RECURSIVE x(n) AS (SELECT 1 UNION ALL SELECT 'text' FROM x) SELECT n FROM x",
        "WITH RECURSIVE x(n) AS (SELECT 1 UNION ALL SELECT n, n + 1 FROM x) SELECT n FROM x",
        "WITH RECURSIVE x(n) AS (SELECT n FROM x UNION ALL SELECT n + 1 FROM x) SELECT n FROM x",
        "WITH RECURSIVE x(n) AS (SELECT 1 UNION ALL SELECT a.n FROM x a JOIN x b ON a.n = b.n) SELECT n FROM x",
        "WITH RECURSIVE x(n) AS (SELECT 1 UNION ALL SELECT COUNT(*) FROM x) SELECT n FROM x",
        "WITH RECURSIVE x(n) AS (SELECT 1 UNION ALL SELECT DISTINCT n FROM x) SELECT n FROM x",
        "WITH RECURSIVE x(n) AS (SELECT 1 UNION ALL SELECT n FROM x GROUP BY n) SELECT n FROM x",
        "WITH RECURSIVE x(n) AS (SELECT 1 UNION ALL SELECT n FROM x ORDER BY n) SELECT n FROM x",
        "WITH RECURSIVE x(n) AS (SELECT 1 UNION ALL SELECT n FROM x LIMIT 2) SELECT n FROM x",
        "WITH RECURSIVE x(n) AS (SELECT 1 UNION ALL SELECT q.n FROM (SELECT n FROM x) q) SELECT n FROM x",
        "WITH RECURSIVE x(n) AS (SELECT 1 UNION ALL SELECT x.n FROM x LEFT JOIN users u ON u.id = x.n) SELECT n FROM x",
        "WITH RECURSIVE x(n) AS (SELECT n FROM y), y(n) AS (SELECT n FROM x) SELECT n FROM x",
        "WITH RECURSIVE x(a, b) AS (SELECT 1 UNION ALL SELECT a + 1 FROM x WHERE a < 2) SELECT a FROM x",
        "WITH x(n) AS (SELECT 1 UNION ALL SELECT n + 1 FROM x WHERE n < 3) SELECT n FROM x",
    ]
    for source in negative:
        run(source, code=1)

    # Verify the execution guard itself interrupts an unbounded, otherwise
    # syntactically valid recursive statement, then leaves the connection usable.
    try:
        execute(databases[0], "WITH RECURSIVE forever(n) AS (SELECT 1 UNION ALL SELECT n + 1 FROM forever) SELECT n FROM forever")
    except sqlite3.OperationalError as error:
        assert "interrupted" in str(error), error
    else:
        raise AssertionError("SQLite instruction budget did not interrupt unbounded recursion")
    assert execute(databases[0], "SELECT 1")[1] == [(1,)]
    for db in databases:
        db.close()
    print(f"PASS: {total} industrial examples certified and SQLite-compiled (source + canonical)")
    print(f"PASS: {total * 2} execution comparisons on empty and populated databases")
    print(f"PASS: {len(oracles)} independent result oracles, {len(negative)} rejection cases, and recursion-budget guard")


if __name__ == "__main__":
    main()
