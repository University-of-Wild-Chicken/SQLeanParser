#!/usr/bin/env python3
"""Check the compiled CLI and independently compile each CRUD example with SQLite.

Run `lake build` first. Uses Python's standard library and an in-memory database;
EXPLAIN compiles statements without executing their writes. This is an additional
syntax interoperability check, not a proof of SQL execution semantics.
"""

from __future__ import annotations

import json
from pathlib import Path
import sqlite3
import subprocess
import tempfile


ROOT = Path(__file__).resolve().parents[1]
EXE = ROOT / ".lake/build/bin/sqlean"
SCHEMA = ROOT / "fixtures/crud/schema.json"


def run(args: list[str], code: int = 0, contains: str = "", stdin: str | None = None) -> str:
    result = subprocess.run(
        [str(EXE), *args], input=stdin, text=True, capture_output=True, cwd=ROOT, check=False
    )
    assert result.returncode == code, (args, result.returncode, result.stdout, result.stderr)
    assert contains in result.stdout + result.stderr, (args, contains, result.stdout, result.stderr)
    return result.stdout


def quote_identifier(name: str) -> str:
    return '"' + name.replace('"', '""') + '"'


def main() -> None:
    if not EXE.is_file():
        raise SystemExit("Build the CLI first: lake build")
    schema = json.loads(SCHEMA.read_text())
    db = sqlite3.connect(":memory:")
    sql_types = {"int": "INTEGER", "text": "TEXT", "bool": "BOOLEAN"}
    for table in schema["tables"]:
        columns = ", ".join(
            f'{quote_identifier(column["name"])} {sql_types[column["type"]]} NOT NULL'
            for column in table["columns"]
        )
        db.execute(f'CREATE TABLE {quote_identifier(table["name"])} ({columns})')

    total = 0
    for category in ("select", "insert", "update", "delete"):
        sources = (ROOT / f"fixtures/crud/{category}.sql").read_text().splitlines()
        assert len(sources) == len(set(sources)) == 50, category
        for index, source in enumerate(sources, 1):
            try:
                output = run(["--schema", str(SCHEMA), source])
                canonical = output.splitlines()[-1]
                db.execute("EXPLAIN " + source).fetchall()
                db.execute("EXPLAIN " + canonical).fetchall()
            except Exception as error:
                raise AssertionError(f"{category} example {index}: {source}") from error
            total += 1
    db.close()

    negative = [
        ("INSERT INTO users VALUES (1)", "validation error"),
        ("INSERT INTO users (id, age, name, city) VALUES (1, 20, 'A', 'B'), (2, 30)", "validation error"),
        ("INSERT INTO users (id, age, name, city) VALUES (1, age, 'A', 'B')", "validation error"),
        ("UPDATE users SET age = 'old'", "validation error"),
        ("UPDATE users SET age = 1, age = 2", "validation error"),
        ("UPDATE missing SET age = 1", "validation error"),
        ("DELETE FROM users WHERE age", "validation error"),
        ("DELETE FROM users WHERE missing = 1", "validation error"),
        ("SELECT id FROM users ORDER BY 0", "validation error"),
        ("SELECT id FROM users ORDER BY 2", "validation error"),
        ("SELECT DISTINCT id FROM users ORDER BY name", "validation error"),
        ("SELECT id FROM users OFFSET 2", "parse error"),
        ("UPDATE users SET age = 1; DELETE FROM users", "parse error"),
        ("DELETE FROM users RETURNING id", "parse error"),
    ]
    for source, message in negative:
        run(["--schema", str(SCHEMA), source], 1, message)
    run(["--ast", "UPDATE users SET age = age + 1"], contains="SQLean.Statement.update")
    run(["--help"], contains="SELECT, INSERT, UPDATE, or DELETE")
    run(["--unknown"], 2, "unknown option")
    run([], stdin="DELETE FROM users\nWHERE id = 1;", contains='DELETE FROM "users"')
    with tempfile.TemporaryDirectory() as directory:
        query_path = Path(directory) / "query.sql"
        query_path.write_text("INSERT INTO flags VALUES (1, TRUE, 'example');\n")
        run(["--file", str(query_path), "--schema", str(SCHEMA)], contains="Valid INSERT statement.")
    print(f"PASS: {total} CRUD examples certified by the CLI and compiled by SQLite (source + canonical)")
    print(f"PASS: {len(negative) + 5} CLI rejection, AST, help, stdin, and file cases")


if __name__ == "__main__":
    main()
