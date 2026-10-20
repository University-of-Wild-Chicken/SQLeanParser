#!/usr/bin/env python3
"""Authored set-tree regressions, with separate PostgreSQL and SQLite evidence.

The optional raw-AST oracle is pinned pglast v7.21 / PostgreSQL 17.7, restricted
to mutually accepted syntax. PostgreSQL 16 accepts four documented wrapper
forms which the current typed parser excludes; two also differ from PG17's
raw parser. Neither parser acceptance nor roundtrip establishes SQL validity.
Only the fixed authored SQLite cases and optional native PostgreSQL anchors
execute. No downloaded source corpus is read or executed.
"""
from __future__ import annotations

import argparse
import hashlib
import itertools
import json
from pathlib import Path
import sqlite3
import subprocess

from check_pagination_cli import EXE, ROOT, replay
from check_postgresql_cli import connection, run, sql_literal
from check_renderer_corpus import parameters

FIXTURE = ROOT / "fixtures/set_operations/structure.json"
DIGEST = "0940c418bfc365db1f3c40106d4cbb709c26d11ffed40e8a77d23f97936b7eaa"
PORTABLE = ("UNION", "UNION ALL", "INTERSECT", "EXCEPT")
SQLITE_EXCLUSIONS = (
    ("SELECT 1 INTERSECT ALL SELECT 2", "invalid", "input.parse"),
    ("SELECT 1 EXCEPT ALL SELECT 2", "invalid", "input.parse"),
    ("SELECT 1 UNION (SELECT 2 UNION SELECT 3)", "invalid", "input.parse"),
    ("SELECT 1 UNION ALL (SELECT 2 LIMIT 1)", "invalid", "input.parse"),
    ("(SELECT 1 LIMIT 1) UNION ALL SELECT 2", "unsupported", "coverage.sqlite.operand-local-clauses"),
)
ANCHORS = (
    ("SELECT 1 AS v UNION SELECT 2 AS v INTERSECT SELECT 2 AS v", [1, 2], [2]),
    ("SELECT 1 AS v EXCEPT SELECT 2 AS v INTERSECT SELECT 2 AS v", [1], []),
)


def load_cases():
    data = json.loads(FIXTURE.read_text())
    assert hashlib.sha256(json.dumps(data, sort_keys=True, separators=(",", ":")).encode()).hexdigest() == DIGEST
    rows, gaps = data["postgres_raw_ast"], data["postgres16_wrapper_gaps"]
    assert len(rows) == len({r["id"] for r in rows}) == len({r["sql"] for r in rows}) == 126
    assert len(gaps) == len({r["sql"] for r in gaps}) == 4
    assert all(r["source_kind"] == "synthetic" for r in rows + gaps)
    assert all(r["postgres16_sqlstate"] == "00000" for r in gaps)
    assert [r["pglast17_accepts"] for r in gaps] == [True, True, False, False]
    return rows, gaps


def rejected(sql, mode, status, code):
    result = subprocess.run([str(EXE), "--render-assurance", mode], input=sql,
                            cwd=ROOT, text=True, capture_output=True, timeout=30)
    assert not result.stderr.strip(), result.stderr
    report = json.loads(result.stdout)
    assert result.returncode == {"invalid": 1, "unsupported": 3}[status], report
    assert report.get("status") == status and report.get("mode") == mode, report
    assert report.get("diagnostic", {}).get("code") == code, report
    assert report.get("evidence") == "none", report
    assert not ({"sql", "parameterMap", "theorems"} & report.keys()), report


def postgres_renderings(rows, gaps):
    canonical = []
    for row in rows:
        replay("identity", row["sql"])
        rendered = replay("postgres", row["sql"])["sql"]
        assert parameters(rendered, "postgres") == [
            ("numbered", index) for _, index in parameters(row["sql"], "postgres")]
        canonical.append(rendered)
    for row in gaps:
        rejected(row["sql"], "postgres", "invalid", "input.parse")
    return canonical


def apply_set(operator, left, right):
    """Independent small integer bag model; no database outputs enter it."""
    if operator == "UNION ALL":
        return left + right
    if operator == "UNION":
        return sorted(set(left) | set(right))
    if operator == "INTERSECT":
        return sorted(set(left) & set(right))
    assert operator == "EXCEPT"
    return sorted(set(left) - set(right))


def sqlite_cases():
    return [
        (f"SELECT 1 AS v {first} SELECT 2 AS v {second} SELECT 2 AS v",
         sorted(apply_set(second, apply_set(first, [1], [2]), [2])))
        for first, second in itertools.product(PORTABLE, repeat=2)]


def sqlite_observation(database, sql):
    remaining = 100
    def budget():
        nonlocal remaining
        remaining -= 1
        return remaining <= 0
    database.set_progress_handler(budget, 1000)
    try:
        cursor = database.execute(sql)
        names = tuple(c[0] for c in cursor.description)
        rows = cursor.fetchall()
    finally:
        database.set_progress_handler(None, 0)
    assert names == ("v",), (sql, names)
    assert all(len(row) == 1 and type(row[0]) is int for row in rows), (sql, rows)
    return sorted(row[0] for row in rows)


def check_sqlite():
    assert sqlite3.sqlite_version_info >= (3, 39, 0), "the SQLite profile requires 3.39+"
    with sqlite3.connect(":memory:") as database:
        for source, expected in sqlite_cases():
            canonical = replay("sqlite", source)["sql"]
            for sql in (source, canonical):
                assert sqlite_observation(database, sql) == expected, (source, sql, expected)
        for source, pg_expected, sqlite_expected in ANCHORS:
            assert pg_expected != sqlite_expected
            assert sqlite_observation(database, source) == sqlite_expected
    for sql, status, code in SQLITE_EXCLUSIONS:
        rejected(sql, "sqlite", status, code)
    return 32, len(SQLITE_EXCLUSIONS)


def clean_pg_tree(value):
    if isinstance(value, dict):
        result = {k: clean_pg_tree(v) for k, v in value.items()
                  if k not in {"location", "stmt_location", "stmt_len", "version"}}
        # Canonical output spells the default ascending direction explicitly.
        if result.get("sortby_dir") == "SORTBY_DEFAULT":
            result["sortby_dir"] = "SORTBY_ASC"
        return result
    if isinstance(value, list):
        return [clean_pg_tree(v) for v in value]
    return value


def check_postgres_ast(rows, canonical, gaps):
    import pglast
    from pglast import parser
    assert pglast.__version__ == "v7.21" and pglast.get_postgresql_version() == (17, 7)
    assert len(rows) == len(canonical), "missing canonical raw-AST witness"
    for row, rendered in zip(rows, canonical):
        source = clean_pg_tree(json.loads(parser.parse_sql_json(row["sql"])))
        target = clean_pg_tree(json.loads(parser.parse_sql_json(rendered)))
        assert source == target, (row["id"], row["sql"], rendered)
    for row in gaps:
        try:
            parser.parse_sql_json(row["sql"])
            accepts = True
        except parser.ParseError:
            accepts = False
        assert accepts is row["pglast17_accepts"], row
    return len(rows), len(gaps)


def native_script(gaps, canonical_anchors):
    assert len(gaps) == 4 and len(canonical_anchors) == len(ANCHORS)
    commands = [
        "BEGIN;", "SET LOCAL statement_timeout = '5s';",
        "CREATE FUNCTION pg_temp.set_analysis(q TEXT) RETURNS TEXT LANGUAGE plpgsql AS $$ "
        "BEGIN EXECUTE 'PREPARE set_probe AS ' || q; DEALLOCATE set_probe; RETURN '00000'; "
        "EXCEPTION WHEN OTHERS THEN RETURN SQLSTATE; END $$;",
    ]
    for row in gaps:
        commands.append("SELECT pg_temp.set_analysis(" + sql_literal(row["sql"]) + ");")
    for (source, _, _), canonical in zip(ANCHORS, canonical_anchors):
        for sql in (source, canonical):
            commands.append("SELECT COALESCE(json_agg(v ORDER BY v), '[]'::json) FROM (" +
                            sql.strip().removesuffix(";") + ") AS observed;")
    commands.append("ROLLBACK;")
    return "\n".join(commands)


def validate_native(stdout, gaps):
    observed = stdout.splitlines()
    assert len(observed) == len(gaps) + 2 * len(ANCHORS), observed
    assert observed[:len(gaps)] == [r["postgres16_sqlstate"] for r in gaps], observed
    expected = [values for _, values, _ in ANCHORS for _ in range(2)]
    actual = [json.loads(line) for line in observed[len(gaps):]]
    assert all(isinstance(row, list) and all(type(v) is int for v in row) for row in actual), actual
    assert actual == expected, (actual, expected)


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--postgres-ast", action="store_true")
    target = parser.add_mutually_exclusive_group()
    target.add_argument("--local-bin")
    target.add_argument("--dsn")
    parser.add_argument("--psql")
    args = parser.parse_args()
    rows, gaps = load_cases()
    canonical = postgres_renderings(rows, gaps)
    observations, exclusions = check_sqlite()
    print(f"PASS: {len(rows)} authored PostgreSQL tree roundtrips; {len(gaps)} explicit typed-parser wrapper gaps")
    print(f"PASS: SQLite {sqlite3.sqlite_version}: {observations} source/canonical observations; {exclusions} exclusions")
    if args.postgres_ast:
        count, boundaries = check_postgres_ast(rows, canonical, gaps)
        print(f"PASS: optional pglast v7.21 / PG17.7: {count} raw-AST pairs; {boundaries} separately classified wrappers")
    if args.local_bin or args.dsn:
        canonical_anchors = [replay("postgres", source)["sql"] for source, _, _ in ANCHORS]
        with connection(args) as psql:
            version = int(run([*psql, "-X", "-qAt", "-c", "SHOW server_version_num;"]).stdout.strip())
            assert 160000 <= version < 170000, "these wrapper observations target PostgreSQL 16"
            result = run([*psql, "-X", "-qAt", "-v", "ON_ERROR_STOP=1"],
                         input=native_script(gaps, canonical_anchors), timeout=30)
            validate_native(result.stdout, gaps)
        print("PASS: native PostgreSQL 16: 4 accepted wrapper gaps; 4 dialect-specific source/canonical value observations")
    print("Scope: finite authored structure and target-native observations; no cross-dialect semantic equivalence claim.")


if __name__ == "__main__":
    main()
