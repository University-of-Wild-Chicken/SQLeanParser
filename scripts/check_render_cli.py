#!/usr/bin/env python3
"""Check the SELECT render boundary and optional independent PostgreSQL witnesses.

The default run exercises the public JSON protocol without a database. Supply
--local-bin or --dsn for fixed PostgreSQL 16 observations, including actual
PREPARE/EXECUTE output. This is finite test evidence, not a parser, renderer, or
semantic-preservation theorem. Only Python's standard library is needed.
"""

from __future__ import annotations

import argparse
from collections import Counter
import json
from pathlib import Path
import subprocess
import tempfile

from check_postgresql_cli import (
    connection, copy_result, csv_record, marker, parse_results, run, sql_literal,
)


ROOT = Path(__file__).resolve().parents[1]
EXE = ROOT / ".lake/build/bin/sqlean"
PROFILES = {
    "identity": "sqlean-select-render-v0.1",
    "postgres": "postgresql-16-select-render-v0.1",
}
EXIT_CODES = {"rendered": 0, "invalid": 1, "unsupported": 3, "inconclusive": 4, "mismatch": 1}


def invoke(mode, sql, *, depth=None, stdin=False):
    args = [str(EXE), "--render-assurance", mode]
    if depth is not None:
        args += ["--max-depth", str(depth)]
    if not stdin:
        args.append(sql)
    result = subprocess.run(
        args, input=sql if stdin else None, text=True, capture_output=True,
        cwd=ROOT, timeout=30, check=False,
    )
    try:
        report = json.loads(result.stdout)
    except json.JSONDecodeError as error:
        raise AssertionError(("expected one render JSON report", args, result.stdout, result.stderr)) from error
    assert isinstance(report, dict), report
    status = report.get("status")
    assert result.returncode == EXIT_CODES[status], (args, result, report)
    assert report.get("profile") == PROFILES[mode], report
    assert report.get("mode") == mode, report
    assert report.get("assurance") == "checked-roundtrip", report
    assert report.get("semanticPreservation") is False, report
    if status == "rendered":
        assert isinstance(report.get("sql"), str) and report["sql"].endswith(";"), report
        assert isinstance(report.get("parameterMap"), list), report
    else:
        assert "sql" not in report and "parameterMap" not in report, report
        assert report.get("diagnostic", {}).get("code"), report
        assert report.get("diagnostic", {}).get("message"), report
    return report


def successful(mode, sql, **kwargs):
    report = invoke(mode, sql, **kwargs)
    assert report["status"] == "rendered", (sql, report)
    again = invoke(mode, sql, **kwargs)
    assert again == report, ("nondeterministic report", report, again)
    canonical = invoke(mode, report["sql"])
    assert canonical["status"] == "rendered" and canonical["sql"] == report["sql"], (
        "unstable canonical bytes", report, canonical,
    )
    return report


def parameter_entries(report):
    entries = report["parameterMap"]
    actual = {}
    for entry in entries:
        source = entry["source"]
        key = source["style"], source["index"]
        assert key not in actual, ("duplicate binding-map entry", entries)
        actual[key] = entry["target"]
    assert len(set(actual.values())) == len(actual), ("noninjective binding map", entries)
    return actual


def cli_checks():
    count = 0
    accepted = [
        "SELECT missing FROM absent",
        'SELECT "a.b", "a"."b" FROM "select" AS "a"',
        'SELECT \'O\'\'Neil\\path\nnext; SELECT 99; --\' AS "quote""name"',
        'SELECT NULL AS absent, \'NULL\' AS text_null, \'\' AS empty, TRUE AS truth',
        'SELECT 1.2500, .5, 1., 1E+02, 1.00000000000000000000000001',
        'SELECT (8 - (4 - 2)), (8 / (4 / 2)), -(-1), NOT (TRUE AND FALSE)',
        'SELECT CAST(1 AS REAL), CAST(1 AS DOUBLE PRECISION), CAST(1 AS NUMERIC(12,4))',
        'SELECT CAST(\'x\' AS VARCHAR(17))',
        '(SELECT 1 LIMIT 1) EXCEPT ((SELECT 2) EXCEPT (SELECT 3 LIMIT 1))',
        'SELECT a.id FROM a LEFT JOIN b ON a.id = b.id WHERE b.id IS NULL',
        'WITH c(x) AS (SELECT 1) SELECT x, x FROM c ORDER BY x NULLS LAST LIMIT 0 OFFSET 0',
        'WITH RECURSIVE c(x) AS (SELECT 1 UNION ALL SELECT x + 1 FROM c WHERE x < 3) SELECT x FROM c',
        'SELECT COUNT(*) FILTER (WHERE x > 0) FROM t GROUP BY x HAVING COUNT(*) > 1',
        'SELECT DISTINCT ON (x) x, y FROM t ORDER BY x, y DESC NULLS FIRST',
        'SELECT * FROM a NATURAL FULL JOIN b',
        'SELECT * FROM a JOIN b USING (id)',
        'SELECT q.x FROM a CROSS JOIN LATERAL (SELECT a.id AS x) q',
        'SELECT EXISTS (SELECT 1 FROM b WHERE b.id = a.id) FROM a',
        'SELECT id IN (SELECT id FROM b) FROM a',
        'SELECT (SELECT a.id) FROM a',
        'SELECT ((SELECT 1) + 2), ((SELECT 1) IN (1, 2)), (1 IN ((SELECT 1), 2))',
        'SELECT * FROM ((SELECT 1 AS id ORDER BY id LIMIT 1) a '
        'LEFT JOIN ((SELECT 2 AS id) b INNER JOIN c USING (id)) ON TRUE) ORDER BY 1 LIMIT 2',
        'SELECT 1 AS "' + "x" * 63 + '"',
        'SELECT 1 AS "' + "界" * 21 + '"',
        'SELECT 1 AS "é", 2 AS "e\u0301"',
    ]
    for mode in PROFILES:
        for sql in accepted:
            report = successful(mode, sql)
            assert parameter_entries(report) == {}, report
            count += 1
        numbered = successful(mode, "SELECT $2 AS second, $1 AS first, $2 AS repeated")
        assert parameter_entries(numbered) == {("numbered", 2): 2, ("numbered", 1): 1}
        assert numbered["sql"].count("$2") == 2 and numbered["sql"].count("$1") == 1
        anonymous = successful(mode, "WITH c(x) AS (SELECT ?) SELECT ?, (SELECT ?), '?' FROM c")
        assert parameter_entries(anonymous) == {
            ("anonymous", 1): 1, ("anonymous", 2): 2, ("anonymous", 3): 3,
        }
        if mode == "postgres":
            assert all(f"${index}" in anonymous["sql"] for index in (1, 2, 3))
        else:
            assert anonymous["sql"].count("?") == 4  # Three bindings plus quoted text.
        between = successful(mode, "SELECT ? BETWEEN ? AND ?")
        assert len(parameter_entries(between)) == 3
        count += 3
        for sql, stdin in [
            ('SELECT 1 AS "' + "x" * 64 + '"', False),
            ('SELECT 1 AS "' + "界" * 22 + '"', False),
            ('SELECT \'before\0after\'', True),
            ('SELECT 1 AS "before\0after"', True),
        ]:
            assert invoke(mode, sql, stdin=stdin)["status"] == "invalid", sql
            count += 1
        for sql, depth in [("SELECT 1", 0), ("SELECT " + "-(" * 20 + "1" + ")" * 20, 5)]:
            assert invoke(mode, sql, depth=depth)["status"] == "inconclusive"
            count += 1
        assert invoke(mode, "DELETE FROM t")["status"] == "unsupported"
        count += 1
    assert invoke("identity", "SELECT $65536")["status"] == "rendered"
    assert invoke("postgres", "SELECT $65536")["status"] == "unsupported"
    count += 2
    # Options that would mix validation and serialization claims are explicit errors.
    for extra in [
        ["--schema", "fixtures/crud/schema.json"], ["--param-types", "int"], ["--ast"],
        ["--postgres"], ["--assurance", "syntax"], ["--render-assurance", "postgres"],
    ]:
        result = subprocess.run(
            [str(EXE), "--render-assurance", "identity", *extra, "SELECT 1"],
            text=True, capture_output=True, cwd=ROOT, timeout=30, check=False,
        )
        assert result.returncode != 0 and '"sql"' not in result.stdout, (extra, result)
        count += 1
    # --file and stdin preserve newlines, quotes, and SQL-looking literal text.
    literal = "SELECT 'line1\nline2; SELECT 99; --' AS text"
    successful("identity", literal, stdin=True)
    with tempfile.TemporaryDirectory(prefix="sqlean-render-") as temporary:
        path = Path(temporary) / "literal.sql"
        path.write_text(literal)
        result = subprocess.run(
            [str(EXE), "--render-assurance", "identity", "--file", str(path)],
            text=True, capture_output=True, cwd=ROOT, timeout=30, check=False,
        )
        assert result.returncode == 0 and json.loads(result.stdout)["status"] == "rendered", result
    return count + 2


SETUP = [
    "CREATE TEMP TABLE render_rows (id INTEGER, grp INTEGER, label TEXT);",
    "INSERT INTO render_rows VALUES (1, 1, 'a'), (2, 1, 'b'), (2, 1, 'b'), (3, 2, NULL);",
    "CREATE TEMP TABLE render_a (id INTEGER);",
    "INSERT INTO render_a VALUES (1), (2);",
    "CREATE TEMP TABLE render_b (id INTEGER, keep BOOLEAN);",
    "INSERT INTO render_b VALUES (1, FALSE);",
]


def database_result(psql, sql, *, setup=()):
    key = marker("render", 1, False, "oracle")
    commands = [
        "\\encoding UTF8", "BEGIN;", "SET LOCAL statement_timeout = '5s';",
        "SET LOCAL standard_conforming_strings = on;",
        "SET LOCAL search_path = pg_temp, pg_catalog;",
        *SETUP, *setup, "\\echo " + key, copy_result(sql), "ROLLBACK;",
    ]
    output = run(
        [*psql, "-X", "-q", "-v", "ON_ERROR_STOP=1"],
        input="\n".join(commands).encode(), text=False, timeout=30,
    ).stdout.decode()
    parsed = parse_results(output)
    assert list(parsed) == [key], parsed
    header, _ = csv_record(output, output.index("\n") + 1)
    return [value for value, _quoted in header], parsed[key][1]


def bag(rows):
    return Counter(map(tuple, rows))


def postgres_checks(args):
    # Every expected observation is authored here independently of renderer output.
    observations = [
        ("SELECT id AS n FROM render_rows", ["n"], [["1"], ["2"], ["2"], ["3"]], "bag"),
        ("SELECT id AS n, label AS value FROM render_rows WHERE label IS NULL",
         ["n", "value"], [["3", None]], "bag"),
        ("SELECT grp AS g, id AS n FROM render_rows ORDER BY grp",
         ["g", "n"], [["1", "1"], ["1", "2"], ["1", "2"], ["2", "3"]], "ties"),
        ("SELECT id AS n FROM render_rows ORDER BY id DESC LIMIT 2",
         ["n"], [["3"], ["2"]], "ordered"),
        ("SELECT 1 AS n EXCEPT (SELECT 1 AS n EXCEPT SELECT 2 AS n)",
         ["n"], [], "bag"),
        ("(SELECT id AS n FROM render_rows ORDER BY id LIMIT 1) UNION ALL SELECT 9 AS n",
         ["n"], [["1"], ["9"]], "bag"),
        ("SELECT a.id AS n FROM render_a a LEFT JOIN render_b b ON a.id = b.id AND b.keep "
         "WHERE b.id IS NULL", ["n"], [["1"], ["2"]], "bag"),
        ("SELECT 8 - (4 - 2) AS subtract, 8 / (4 / 2) AS divide, -(-1) AS negate",
         ["subtract", "divide", "negate"], [["6", "4", "1"]], "ordered"),
        ("SELECT ((SELECT 1) + 2) AS n, ((SELECT 1) IN (1, 2)) AS included, "
         "(1 IN ((SELECT 1), 2)) AS in_values",
         ["n", "included", "in_values"], [["3", "t", "t"]], "ordered"),
        ("SELECT a.id AS a, b.id AS b FROM ((SELECT 1 AS id LIMIT 1) a "
         "LEFT JOIN ((SELECT 2 AS id LIMIT 1) b INNER JOIN render_a c ON b.id = c.id) ON TRUE)",
         ["a", "b"], [["1", "2"]], "ordered"),
        ("SELECT 'O''Neil\\path\nnext; SELECT 99; --' AS \"q\"\"; --\", '界' AS \"a.b\", 'x' AS \"select\"",
         ['q"; --', "a.b", "select"], [["O'Neil\\path\nnext; SELECT 99; --", "界", "x"]], "ordered"),
        ('SELECT 1 AS "' + "界" * 21 + '"', ["界" * 21], [["1"]], "ordered"),
        ("SELECT 1.2500 AS exact, 1E+02 AS exponent",
         ["exact", "exponent"], [["1.2500", "100"]], "ordered"),
        ("SELECT a.id AS outer_id, (SELECT a.id FROM render_b a) AS inner_id FROM render_a a ORDER BY a.id",
         ["outer_id", "inner_id"], [["1", "1"], ["2", "1"]], "ordered"),
        ("SELECT a.id AS n, q.next AS next FROM render_a a "
         "CROSS JOIN LATERAL (SELECT a.id + 1 AS next) q ORDER BY a.id",
         ["n", "next"], [["1", "2"], ["2", "3"]], "ordered"),
        ("WITH RECURSIVE c(n) AS (SELECT 1 UNION ALL SELECT n + 1 FROM c WHERE n < 3) SELECT n FROM c ORDER BY n",
         ["n"], [["1"], ["2"], ["3"]], "ordered"),
    ]
    count = 0
    with connection(args) as psql:
        version = run([*psql, "-X", "-At", "-c", "SHOW server_version;"]).stdout.strip()
        assert version.split(".")[0] == "16", ("renderer profile requires PostgreSQL 16", version)
        settings = run([*psql, "-X", "-At", "-c",
                        "SELECT current_setting('server_encoding'), current_setting('max_identifier_length');"]).stdout.strip()
        assert settings == "UTF8|63", settings
        for source, labels, expected, comparison in observations:
            canonical = successful("postgres", source)["sql"]
            for sql in (source, canonical):
                actual_labels, rows = database_result(psql, sql)
                assert actual_labels == labels, (source, actual_labels, labels)
                if comparison == "ordered":
                    assert rows == expected, (source, rows, expected)
                else:
                    assert bag(rows) == bag(expected), (source, rows, expected)
                    if comparison == "ties":
                        assert [row[0] for row in rows] == sorted(row[0] for row in rows)
                count += 1
        # Capture rows from actual EXECUTE, without placeholder substitution.
        for source, declarations, arguments, columns, expected in [
            ("SELECT $2 AS second, $1 AS first, $2 AS repeated",
             "INTEGER, INTEGER", "11, 22", "second INTEGER, first INTEGER, repeated INTEGER",
             [["22", "11", "22"]]),
            ("WITH c(x) AS (SELECT ?) SELECT ? AS first, (SELECT ?) AS second, x AS third FROM c",
             "INTEGER, INTEGER, INTEGER", "11, 22, 33", "first INTEGER, second INTEGER, third INTEGER",
             [["22", "33", "11"]]),
            ("SELECT ? BETWEEN ? AND ? AS within",
             "INTEGER, INTEGER, INTEGER", "2, 1, 3", "within BOOLEAN", [["t"]]),
            ("SELECT $1 AS absent, $2 AS marker, $3 AS empty",
             "TEXT, TEXT, TEXT", "NULL, 'NULL', ''", "absent TEXT, marker TEXT, empty TEXT",
             [[None, "NULL", ""]]),
        ]:
            report = successful("postgres", source)
            # The returned map must agree with the argument positions used below.
            mapping = parameter_entries(report)
            assert all(index == target for (_style, index), target in mapping.items()), report
            body = "BEGIN RETURN QUERY EXECUTE " + sql_literal(f"EXECUTE render_parameters ({arguments})") + "; END;"
            setup = [
                f"PREPARE render_parameters ({declarations}) AS {report['sql']}",
                f"CREATE FUNCTION pg_temp.render_execute() RETURNS TABLE ({columns}) "
                f"LANGUAGE plpgsql AS {sql_literal(body)};",
            ]
            _labels, actual = database_result(psql, "SELECT * FROM pg_temp.render_execute()", setup=setup)
            assert actual == expected, (source, actual, expected)
            count += 1
        # Errors are observable too: compare independently specified SQLSTATEs.
        for source, expected in [
            ("SELECT 1 / (1 - 1) AS n", "22012"),
            ("SELECT CAST('not-an-integer' AS INTEGER) AS n", "22P02"),
            ("SELECT (SELECT id FROM render_a) AS n", "21000"),
        ]:
            for sql in (source, successful("postgres", source)["sql"]):
                body = ("BEGIN EXECUTE " + sql_literal(sql) +
                        "; RETURN 'no-error'; EXCEPTION WHEN OTHERS THEN RETURN SQLSTATE; END;")
                setup = [f"CREATE FUNCTION pg_temp.render_error() RETURNS TEXT LANGUAGE plpgsql AS {sql_literal(body)};"]
                labels, rows = database_result(psql, "SELECT pg_temp.render_error() AS code", setup=setup)
                assert (labels, rows) == (["code"], [[expected]]), (source, labels, rows, expected)
                count += 1
    return version, count


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    group = parser.add_mutually_exclusive_group()
    group.add_argument("--local-bin")
    group.add_argument("--dsn")
    parser.add_argument("--psql")
    args = parser.parse_args()
    if not EXE.is_file():
        raise SystemExit("Build the CLI first: lake build")
    count = cli_checks()
    print(f"PASS: {count} render CLI cases; profiles, diagnostics, byte stability, and binding maps")
    if args.local_bin or args.dsn:
        version, count = postgres_checks(args)
        print(f"PASS: PostgreSQL {version}; {count} fixed render observations including actual EXECUTE and SQLSTATE errors")
        print("Scope: finite instance evidence under UTF8, 63-byte identifiers, standard_conforming_strings=on; no universal semantics claim.")


if __name__ == "__main__":
    main()
