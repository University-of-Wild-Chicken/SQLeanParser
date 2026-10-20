#!/usr/bin/env python3
"""Check the new dialect profiles against fixed, independent result expectations.

Always runs 150 SQLite examples. --local-bin/--dsn additionally runs 50 PostgreSQL
NUMERIC-scale examples. Source and rendered SQL are both checked, using actual
parameter binding rather than text substitution. These are finite observations,
not a claim that SQLite and PostgreSQL have interchangeable semantics.
"""

from __future__ import annotations

import argparse
from collections import Counter
import json
from pathlib import Path
import sqlite3
import subprocess

from check_postgresql_cli import connection, copy_result, csv_record, marker, parse_results, run, sql_literal


ROOT = Path(__file__).resolve().parents[1]
EXE = ROOT / ".lake/build/bin/sqlean"
FIXTURES = ROOT / "fixtures/dialects"
SQLITE_ROWS = [(1, "a"), (2, "b"), (2, "b"), (3, None), (4, "d"), (5, "e"), (6, "f"), (7, "g")]
PROFILES = {"sqlite": "sqlite-3.39-select-render-v0.1", "postgres": "postgresql-16-select-render-v0.1"}
EXIT_CODES = {"rendered": 0, "invalid": 1, "unsupported": 3, "inconclusive": 4, "mismatch": 1}


def render(mode, sql, status="rendered"):
    result = subprocess.run(
        [str(EXE), "--render-assurance", mode, sql], text=True, capture_output=True,
        cwd=ROOT, timeout=30, check=False,
    )
    report = json.loads(result.stdout)
    assert result.returncode == EXIT_CODES[status] and report.get("status") == status, (sql, result, report)
    assert report.get("profile") == PROFILES[mode] and report.get("mode") == mode, report
    assert report.get("semanticPreservation") is False, report
    assert report.get("assurance") == "checked-roundtrip", report
    if status == "rendered":
        assert report["sql"].endswith(";") and isinstance(report["parameterMap"], list), report
        entries = report["parameterMap"]
        keys = [(entry["source"]["style"], entry["source"]["index"]) for entry in entries]
        assert len(keys) == len(set(keys)), ("duplicate logical binding", entries)
        assert len({entry["target"] for entry in entries}) == len(entries), ("parameter collision", entries)
        assert all(entry["target"] == entry["source"]["index"] for entry in entries), entries
        if mode == "sqlite":
            for entry in entries:
                assert f'?{entry["target"]}' in report["sql"], report
    else:
        assert "sql" not in report and "parameterMap" not in report, report
        assert report.get("diagnostic", {}).get("code"), report
    return report


def load_cases():
    metadata = json.loads((FIXTURES / "cases.json").read_text())
    assert set(metadata) == {
        "sqlite_numbered_parameters", "sqlite_compound_queries", "sqlite_limit_comma",
        "postgres_numeric_scale",
    }
    for category, cases in metadata.items():
        sources = (FIXTURES / f"{category}.sql").read_text().splitlines()
        assert len(sources) == len(set(sources)) == len(cases) == 50, category
        assert sources == [case["sql"] for case in cases], category
    return metadata


def compare(case, labels, rows):
    assert labels == case["columns"], (case["sql"], labels, case["columns"])
    expected = [tuple(row) for row in case["rows"]]
    actual = [tuple(row) for row in rows]
    if case["comparison"] == "bag":
        assert Counter(actual) == Counter(expected), (case["sql"], actual, expected)
    else:
        assert actual == expected, (case["sql"], actual, expected)


def sqlite_checks(metadata):
    if sqlite3.sqlite_version_info < (3, 39, 0):
        raise SystemExit("SQLite 3.39 or newer is required for the sqlite profile")
    db = sqlite3.connect(":memory:")
    if hasattr(db, "getlimit"):
        assert db.getlimit(sqlite3.SQLITE_LIMIT_VARIABLE_NUMBER) >= 32766
    db.execute("CREATE TABLE dialect_rows(id INTEGER, label TEXT)")
    db.executemany("INSERT INTO dialect_rows VALUES (?, ?)", SQLITE_ROWS)
    count = 0
    try:
        for category, cases in metadata.items():
            if not category.startswith("sqlite_"):
                continue
            for case in cases:
                report = render("sqlite", case["sql"])
                canonical = render("sqlite", report["sql"])
                assert canonical["sql"] == report["sql"], case
                for sql in (case["sql"], report["sql"]):
                    cursor = db.execute(sql, case["parameters"])
                    compare(case, [column[0] for column in cursor.description], cursor.fetchall())
                    count += 1
        # Bare anonymous occurrences are translated to explicit SQLite slots.
        source = "WITH c(x) AS (SELECT ?) SELECT ? AS first, x AS second, '?' AS quoted FROM c"
        report = render("sqlite", source)
        assert report["parameterMap"] == [
            {"source": {"style": "anonymous", "index": 1}, "target": 1},
            {"source": {"style": "anonymous", "index": 2}, "target": 2},
        ], report
        for sql in (source, report["sql"]):
            assert db.execute(sql, [11, 22]).fetchall() == [(22, 11, "?")]
            count += 1
        # Cross-engine differences are not "fixed" by changing the query.
        assert db.execute("SELECT 1 UNION SELECT 2 INTERSECT SELECT 2").fetchall() == [(2,)]
        assert db.execute("SELECT ?2, ?1, ?2", [11, 22]).fetchall() == [(22, 11, 22)]
        count += 2
        maximum = "SELECT ?32766 AS last_slot"
        values = [None] * 32765 + [42]
        for sql in (maximum, render("sqlite", maximum)["sql"]):
            assert db.execute(sql, values).fetchall() == [(42,)]
            count += 1
        # Comma and explicit JOIN associate together from the left in SQLite.
        # The empty t distinguishes that tree from PostgreSQL's binding rule.
        db.executescript("CREATE TABLE t(a INTEGER); CREATE TABLE u(b INTEGER); "
                         "CREATE TABLE v(c INTEGER); INSERT INTO u VALUES(1); INSERT INTO v VALUES(7);")
        for keyword in ("RIGHT", "FULL", "LEFT"):
            left_expected = [] if keyword == "LEFT" else [(7,)]
            for source, expected in [
                (f"SELECT v.c FROM t, u {keyword} JOIN v ON TRUE", left_expected),
                (f"SELECT v.c FROM t, (u {keyword} JOIN v ON TRUE)", []),
                (f"SELECT v.c FROM (t, u) {keyword} JOIN v ON TRUE", left_expected),
            ]:
                for sql in (source, render("sqlite", source)["sql"]):
                    actual = db.execute(sql).fetchall()
                    assert actual == expected, (source, sql, actual, expected)
                    count += 1
        # SQLite retains source identifier spelling in output labels; keyword
        # recognition remains case-insensitive across CTEs and expressions.
        for source, labels, expected in [
            ("SeLeCt 1 AS MixedCase", ["MixedCase"], [(1,)]),
            ("WiTh Camel(ColName) AS (sElEcT 1) SeLeCt ColName FROM Camel", ["ColName"], [(1,)]),
            ("SELECT X.* FROM T AS X", ["a"], []),
            ("SELECT CAST(1 AS NuMeRiC(2,4)) AS CastValue, "
             "SuM(1) FILTER (WHERE TrUe) AS Total, 1 NoT In (2) AS Outside",
             ["CastValue", "Total", "Outside"], [(1, 1, 1)]),
        ]:
            for sql in (source, render("sqlite", source)["sql"]):
                cursor = db.execute(sql)
                actual_labels = [column[0] for column in cursor.description]
                actual = cursor.fetchall()
                assert actual_labels == labels and actual == expected, (source, sql, actual_labels, actual)
                count += 1
        # SQLite does not nest block comments. The second apparent opening is
        # comment text, so the following addition and parameter remain active.
        for source, values, expected in [
            ("SELECT 1 /* /* */ + 2 -- */", [], [(3,)]),
            ("SELECT ?1 /* /* */ + ?2 -- */", [11, 22], [(33,)]),
        ]:
            report = render("sqlite", source)
            if values:
                assert report["parameterMap"] == [
                    {"source": {"style": "numbered", "index": 1}, "target": 1},
                    {"source": {"style": "numbered", "index": 2}, "target": 2},
                ], report
            for sql in (source, report["sql"]):
                actual = db.execute(sql, values).fetchall()
                assert actual == expected, (source, sql, actual, expected)
                count += 1
        # These deliberately record SQLite's native behavior. They are not
        # PostgreSQL expectations or an independent AST semantics definition.
        db.execute('CREATE TABLE dialect_booleans("true" INTEGER, "false" INTEGER)')
        db.execute("INSERT INTO dialect_booleans VALUES(19,23)")
        for source, expected in [
            ("SELECT TRUE AS truth, FALSE AS falsehood FROM dialect_booleans", [(19, 23)]),
            ("SELECT 1 / 0 AS quotient", [(None,)]),
            ("SELECT CAST('bad' AS INTEGER) AS value", [(0,)]),
        ]:
            for sql in (source, render("sqlite", source)["sql"]):
                assert db.execute(sql).fetchall() == expected, (source, sql, expected)
                count += 1
    finally:
        db.close()
    return count


def restrictions():
    unsupported = [
        "SELECT 'a' ILIKE 'A'",
        "SELECT DISTINCT ON (id) id FROM t",
        "SELECT * FROM LATERAL (SELECT 1) q",
        "SELECT * FROM t AS a(renamed)",
        "SELECT * FROM (SELECT 1) q(renamed)",
        "(SELECT 1 LIMIT 1) UNION SELECT 2",
        "(WITH c(n) AS (SELECT 1) SELECT n FROM c) UNION SELECT 2",
        "SELECT ?32767",
    ]
    invalid = [
        "SELECT $1", "SELECT ?0", "SELECT ?, ?1", "SELECT ?1, ?",
        "SELECT 1 LIMIT 1,", "SELECT 1 LIMIT ,1", "SELECT 1 LIMIT 1,2 OFFSET 3",
        "SELECT 1 INTERSECT ALL SELECT 1", "SELECT 1 EXCEPT ALL SELECT 1",
        "SELECT 1 OFFSET 1", "SELECT 1 UNION (SELECT 2 UNION SELECT 3)",
        "SELECT 1 EXCEPT (SELECT 2 EXCEPT SELECT 3)", "SELECT 1 UNION (SELECT 2 ORDER BY 1)",
        "WITH c(n) AS (SELECT 1 EXCEPT ALL SELECT 2) SELECT n FROM c",
    ]
    for sql in unsupported:
        render("sqlite", sql, "unsupported")
    for sql in invalid:
        render("sqlite", sql, "invalid")
    render("sqlite", "SELECT ?32766")
    return len(unsupported) + len(invalid) + 1


def literal(value):
    return "NULL" if value is None else sql_literal(value)


def postgres_checks(args, cases):
    commands = [
        "\\encoding UTF8", "BEGIN;", "SET LOCAL statement_timeout = '5s';",
        "SET LOCAL standard_conforming_strings = on;",
        "SET LOCAL search_path = pg_temp, pg_catalog;",
    ]
    expected = {}
    for index, case in enumerate(cases, 1):
        canonical = render("postgres", case["sql"])
        assert render("postgres", canonical["sql"])["sql"] == canonical["sql"]
        for form, sql in (("source", case["sql"]), ("canonical", canonical["sql"])):
            key = marker("dialect_numeric", index, False, form)
            expected[key] = case
            if case["parameters"]:
                # Execute an actual prepared query; bind values through EXECUTE,
                # never substitute parameter markers in the query text.
                execute = f"EXECUTE dialect_numeric ({', '.join(map(literal, case['parameters']))})"
                body = "BEGIN RETURN QUERY EXECUTE " + sql_literal(execute) + "; END;"
                commands.extend([
                    f"PREPARE dialect_numeric (NUMERIC, NUMERIC) AS {sql}",
                    "CREATE OR REPLACE FUNCTION pg_temp.dialect_execute() "
                    f"RETURNS TABLE(a NUMERIC,b NUMERIC,c NUMERIC) LANGUAGE plpgsql AS {sql_literal(body)};",
                    "\\echo " + key,
                    copy_result("SELECT * FROM pg_temp.dialect_execute()"),
                    "DEALLOCATE dialect_numeric;",
                ])
            else:
                commands.extend(["\\echo " + key, copy_result(sql)])
    commands.append("ROLLBACK;")
    with connection(args) as psql:
        version = run([*psql, "-X", "-At", "-c", "SHOW server_version;"]).stdout.strip()
        assert version.split(".")[0] == "16", ("profile requires PostgreSQL 16", version)
        output = run(
            [*psql, "-X", "-q", "-v", "ON_ERROR_STOP=1"], input="\n".join(commands).encode(),
            text=False, timeout=120,
        ).stdout.decode()
    results = parse_results(output)
    assert set(results) == set(expected), ("missing or extra result sections", set(results) ^ set(expected))
    for key, case in expected.items():
        header, _ = csv_record(output, output.index(key + "\n") + len(key) + 1)
        arity, rows = results[key]
        assert arity == len(case["columns"])
        compare(case, [value for value, _quoted in header], rows)
    return version, len(results)


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    group = parser.add_mutually_exclusive_group()
    group.add_argument("--local-bin")
    group.add_argument("--dsn")
    parser.add_argument("--psql")
    args = parser.parse_args()
    if not EXE.is_file():
        raise SystemExit("Build the CLI first: lake build")
    cases = load_cases()
    count = sqlite_checks(cases)
    rejected = restrictions()
    print(f"PASS: SQLite {sqlite3.sqlite_version}; 150 examples, {count} source/render/binding observations, {rejected} profile boundary cases")
    if args.local_bin or args.dsn:
        version, count = postgres_checks(args, cases["postgres_numeric_scale"])
        print(f"PASS: PostgreSQL {version}; 50 NUMERIC scale examples, {count} source/render observations with actual EXECUTE bindings")
    print("Scope: fixed dialect examples and declared parameter maps; no cross-dialect semantic-equivalence claim.")


if __name__ == "__main__":
    main()
