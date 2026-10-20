#!/usr/bin/env python3
"""Check locking validity, serialization, native rows and bounded contention.

Only authored synthetic statements execute, in a private PostgreSQL cluster.
The 50 unchanged public sources receive rendering checks only. Two-session
observations are finite tests, not a theorem about concurrency or lock timing.
"""
from __future__ import annotations

import argparse
import json
import os
from pathlib import Path
import selectors
import subprocess
import time
import uuid

from check_advanced_cli import literal, question_parameters
from check_assurance_cli import assert_report
from check_dialect_cli import render as dialect_render
from check_pagination_cli import replay
from check_postgresql_cli import (
    connection, copy_result, marker, parse_results, run, sql_identifier, sql_literal,
)
from check_renderer_corpus import parameters
from generate_locking_examples import USERS

ROOT = Path(__file__).resolve().parents[1]
FIXTURES = ROOT / "fixtures/locking"
PG_PARAMETERS = {"int": "INTEGER", "text": "TEXT", "bool": "BOOLEAN"}
PG_COLUMNS = {"int32": "INTEGER", "text": "TEXT", "bool": "BOOLEAN"}
CONTENTION_QUERIES = {
    "nowait": "SELECT id FROM users ORDER BY id FOR UPDATE NOWAIT;",
    "skip": "SELECT id FROM users ORDER BY id FOR UPDATE SKIP LOCKED;",
}


def load_cases():
    synthetic = json.loads((FIXTURES / "synthetic.json").read_text())
    concrete = [json.loads(line) for line in (FIXTURES / "concrete.jsonl").read_text().splitlines()]
    for cases in (synthetic, concrete):
        assert len(cases) == len({row["id"] for row in cases}) == len({row["sql"] for row in cases}) == 50
    for case in synthetic:
        assert case["catalogFile"] == "fixtures/schema.json"
        assert parameters(case["sql"], "postgres") == parameters(case["sqlite_sql"], "sqlite")
        slots = {index for _, index in parameters(case["sql"], "postgres")}
        assert slots == set(range(1, len(case["parameter_values"]) + 1))
        if slots:
            assert len(case["parameter_types"].split(",")) == len(slots)
        else:
            assert case["parameter_types"] == ""
        assert all(len(row) == len(case["output_columns"]) for row in case["expected_rows"])
    return synthetic, concrete


def validity(case):
    args = ["--assurance", "contract", "--schema", str(ROOT / case["catalogFile"])]
    if case["parameter_types"]:
        args += ["--param-types", case["parameter_types"]]
    columns = tuple((col["name"], col["type"], col["nullable"]) for col in case["output_columns"])
    return assert_report([*args, case["sql"]], "valid", "contract", columns)


def sqlite_rejection(case):
    report = dialect_render("sqlite", case["sqlite_sql"], "invalid")
    assert report["diagnostic"]["code"] == "input.parse", report
    expected = ("SQLite OFFSET requires LIMIT first" if case["shape"] == "numbered-offset-first"
                else "SQLite does not support row-locking clauses")
    assert expected in report["diagnostic"]["message"], report
    assert report["evidence"] == "none", report
    assert not ({"sql", "parameterMap", "theorems"} & report.keys()), report
    return report


def prepare_capture(sql, types, values, columns, *, error=False):
    declarations = ", ".join(PG_PARAMETERS[t.removesuffix("?")] for t in types.split(",") if t)
    declaration = f" ({declarations})" if declarations else ""
    execute = "EXECUTE locking_parameters"
    if values:
        execute += " (" + ", ".join(map(literal, values)) + ")"
    if error:
        body = ("BEGIN EXECUTE " + sql_literal(execute) +
                "; RETURN 'unexpected-success'; EXCEPTION WHEN OTHERS THEN RETURN SQLSTATE; END;")
        function = ("CREATE OR REPLACE FUNCTION pg_temp.locking_error() RETURNS TEXT "
                    "LANGUAGE plpgsql VOLATILE AS " + sql_literal(body) + ";")
        capture = copy_result("SELECT pg_temp.locking_error()")
    else:
        signature = ", ".join(f'{sql_identifier(col["name"])} {PG_COLUMNS[col["type"]]}'
                              for col in columns)
        body = "BEGIN RETURN QUERY EXECUTE " + sql_literal(execute) + "; END;"
        function = ("CREATE OR REPLACE FUNCTION pg_temp.locking_rows() RETURNS TABLE (" +
                    signature + ") LANGUAGE plpgsql VOLATILE AS " + sql_literal(body) + ";")
        capture = copy_result("SELECT * FROM pg_temp.locking_rows()")
    source = question_parameters(sql).strip().removesuffix(";")
    return [f"PREPARE locking_parameters{declaration} AS {source};", function, capture]


def users_table(temporary=False):
    return ("CREATE " + ("TEMP " if temporary else "") +
            "TABLE users(id INTEGER NOT NULL, age INTEGER NOT NULL, "
            "name TEXT NOT NULL, city TEXT NOT NULL);")


def users_insert():
    return "INSERT INTO users VALUES " + ", ".join(
        "(" + ", ".join(map(literal, row)) + ")" for row in USERS) + ";"


def copy_cell(value):
    if value is None:
        return None
    if isinstance(value, bool):
        return "t" if value else "f"
    return str(value)


def postgres_script(cases, rendered):
    assert len(cases) == len(rendered), "missing rendered locking case"
    commands = ["\\encoding UTF8", "BEGIN;", "SET LOCAL statement_timeout = '5s';",
                "SET LOCAL standard_conforming_strings = on;", users_table(temporary=True)]
    expected = {}
    for populated in (False, True):
        if populated:
            commands.append(users_insert())
        for index, (case, canonical) in enumerate(zip(cases, rendered), 1):
            for form, sql in (("source", case["sql"]), ("postgres", canonical)):
                capture = prepare_capture(sql, case["parameter_types"], case["parameter_values"],
                                          case["output_columns"])
                key = marker("locking", index, populated, form)
                commands += ["SAVEPOINT locking_case;", *capture[:-1],
                             "\\echo " + key, capture[-1], "DEALLOCATE locking_parameters;",
                             "ROLLBACK TO SAVEPOINT locking_case;", "RELEASE SAVEPOINT locking_case;"]
                rows = case["expected_rows"] if populated else []
                expected[key] = (len(case["output_columns"]),
                                 [[copy_cell(value) for value in row] for row in rows])
    commands.append("ROLLBACK;")
    return "\n".join(commands), expected


class PersistentPsql:
    """A bounded marker handshake with a transaction-owning psql process."""
    def __init__(self, psql):
        self.process = subprocess.Popen(
            [*psql, "-X", "-q", "-A", "-t", "-v", "ON_ERROR_STOP=1"],
            stdin=subprocess.PIPE, stdout=subprocess.PIPE, stderr=subprocess.STDOUT, bufsize=0)
        self.buffer = b""
        self.sequence = 0

    def command(self, sql, timeout=10):
        self.sequence += 1
        sentinel = f"__SQLEAN_LOCK_SYNC_{self.sequence}__"
        assert self.process.stdin is not None and self.process.stdout is not None
        self.process.stdin.write((sql + "\n\\echo " + sentinel + "\n").encode())
        self.process.stdin.flush()
        deadline, lines = time.monotonic() + timeout, []
        with selectors.DefaultSelector() as selector:
            selector.register(self.process.stdout, selectors.EVENT_READ)
            while True:
                while b"\n" in self.buffer:
                    raw, self.buffer = self.buffer.split(b"\n", 1)
                    line = raw.decode("utf-8").rstrip("\r")
                    if line == sentinel:
                        return lines
                    if line:
                        lines.append(line)
                remaining = deadline - time.monotonic()
                if remaining <= 0 or not selector.select(remaining):
                    raise AssertionError(("psql handshake timed out", lines))
                chunk = os.read(self.process.stdout.fileno(), 65536)
                if not chunk:
                    raise AssertionError(("psql exited before handshake", self.process.poll(), lines))
                self.buffer += chunk

    def close(self):
        if self.process.stdin and not self.process.stdin.closed:
            try:
                self.process.stdin.write(b"ROLLBACK;\n\\quit\n")
                self.process.stdin.flush()
            except BrokenPipeError:
                pass
            self.process.stdin.close()
        try:
            self.process.wait(timeout=5)
        except subprocess.TimeoutExpired:
            self.process.terminate()
            try:
                self.process.wait(timeout=5)
            except subprocess.TimeoutExpired:
                self.process.kill()
                self.process.wait(timeout=5)
        if self.process.stdout:
            self.process.stdout.close()


def contention_script(namespace, sql, *, error=False):
    columns = [{"name": "id", "type": "int32", "nullable": False}]
    capture = prepare_capture(sql, "", [], columns, error=error)
    key = marker("locking_contention", 1, True, "error" if error else "rows")
    # A missing NOWAIT would be cancelled with 57014, not pass as 55P03.
    commands = ["BEGIN;", "SET LOCAL statement_timeout = '2s';", "SET LOCAL lock_timeout = 0;",
                f"SET LOCAL search_path = {sql_identifier(namespace)}, pg_catalog;",
                *capture[:-1], "\\echo " + key, capture[-1],
                "DEALLOCATE locking_parameters;", "ROLLBACK;"]
    return "\n".join(commands), key


def contention_observations(psql, rendered):
    assert set(rendered) == set(CONTENTION_QUERIES), "missing rendered contention query"
    namespace = "sqlean_lock_" + uuid.uuid4().hex
    setup = (f"CREATE SCHEMA {sql_identifier(namespace)}; "
             f"SET search_path = {sql_identifier(namespace)}, pg_catalog; " +
             users_table() + users_insert())
    run([*psql, "-X", "-q", "-v", "ON_ERROR_STOP=1"], input=setup)
    owner = PersistentPsql(psql)
    count = 0

    def observe(sql, expected, error=False):
        script, key = contention_script(namespace, sql, error=error)
        output = run([*psql, "-X", "-q", "-v", "ON_ERROR_STOP=1"], input=script, timeout=10).stdout
        actual = parse_results(output)
        assert actual == {key: (1, expected)}, (sql, actual, expected)

    try:
        locked = owner.command("BEGIN; SET LOCAL statement_timeout = '5s'; "
                               f"SET LOCAL search_path = {sql_identifier(namespace)}, pg_catalog; "
                               "SELECT id FROM users WHERE id = 1 FOR UPDATE;")
        assert locked == ["1"], ("owner did not establish the expected lock", locked)
        for mode, sql in CONTENTION_QUERIES.items():
            for query in (sql, rendered[mode]):
                wanted = [["55P03"]] if mode == "nowait" else [[str(row[0])] for row in USERS[1:]]
                observe(query, wanted, error=mode == "nowait")
                count += 1
        assert owner.command("ROLLBACK;") == []
        for mode, sql in CONTENTION_QUERIES.items():
            for query in (sql, rendered[mode]):
                observe(query, [[str(row[0])] for row in USERS])
                count += 1
    finally:
        owner.close()
        run([*psql, "-X", "-q", "-v", "ON_ERROR_STOP=1"],
            input=f"DROP SCHEMA {sql_identifier(namespace)} CASCADE;", timeout=10)
    return count


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--local-bin", required=True,
                        help="PostgreSQL binaries; all native checks use a private cluster")
    args = parser.parse_args()
    synthetic, concrete = load_cases()
    rendered = []
    for case in synthetic:
        validity(case)
        replay("identity", case["sql"])
        rendered.append(replay("postgres", case["sql"])["sql"])
        sqlite_rejection(case)
    for case in concrete:
        replay("identity", case["sql"])
        replay("postgres", case["sql"])
    concurrent = {name: replay("postgres", sql)["sql"] for name, sql in CONTENTION_QUERIES.items()}
    script, expected = postgres_script(synthetic, rendered)
    with connection(args) as psql:
        output = run([*psql, "-X", "-q", "-v", "ON_ERROR_STOP=1"], input=script, timeout=120).stdout
        actual = parse_results(output)
        assert actual == expected, (actual.keys() ^ expected.keys(),
                                    [(key, actual.get(key), value) for key, value in expected.items()
                                     if actual.get(key) != value][:3])
        contention = contention_observations(psql, concurrent)
        version = run([*psql, "-X", "-At", "-c", "SHOW server_version;"]).stdout.strip()
    print("PASS: 50 locking validity certificates, 50 unchanged concrete sources, "
          "identity/PostgreSQL canonical checks, and 50 explicit SQLite parse rejections "
          "(38 row locking; 12 OFFSET-before-LIMIT)")
    print(f"PASS: PostgreSQL {version}: {len(expected)} PREPARE/EXECUTE typed-row observations, "
          f"{contention} controlled contention/release observations")
    print("Scope: finite synthetic executions; no application execution, concurrency theorem, "
          "lock-acquisition guarantee or general semantic equivalence claim.")


if __name__ == "__main__":
    main()
