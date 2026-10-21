#!/usr/bin/env python3
"""Authored recursive CTE analysis and explicit static-profile boundaries.

These inputs may be nonterminating. PostgreSQL only prepares and describes
them; no prepared query executes. Static type, modifier and collation coverage
is recorded separately from native acceptance. No downloaded SQL is read.
"""
import argparse
from collections import Counter
import hashlib
import json

from check_assurance_cli import assert_report
from check_pagination_cli import ROOT, replay
from check_postgresql_cli import connection, run, sql_literal

FIXTURE = ROOT / "fixtures/recursive_contract/boundaries.json"
DIGEST = "5324590dc4f0d8c2ad244e62b3198088b569e4edc5b22dbd10766d93caaf451f"


def load_cases():
    rows = json.loads(FIXTURE.read_text())
    assert hashlib.sha256(json.dumps(rows, sort_keys=True, separators=(",", ":")).encode()).hexdigest() == DIGEST
    assert len(rows) == len({r["id"] for r in rows}) == len({r["sql"] for r in rows}) == 85
    assert Counter(r["expected_status"] for r in rows) == {"valid": 42, "invalid": 38, "unsupported": 5}
    assert Counter(r["postgres_sqlstate"] for r in rows) == {
        "00000": 45, "42P19": 15, "42P21": 11, "42804": 9, "0A000": 5}
    assert sum(len(r["postgres_columns"] or []) for r in rows) == 47
    assert all(r["source_kind"] == "synthetic" and type(r["actual_recursion"]) is bool for r in rows)
    return rows


def static_check(row):
    columns = None if row["output_columns"] is None else tuple(
        (c["name"], c["type"], c["nullable"]) for c in row["output_columns"])
    report = assert_report(["--assurance", "contract", row["sql"]],
                           row["expected_status"], "contract", columns)
    if row["diagnostic"] is not None:
        assert report["diagnostic"]["code"] == row["diagnostic"], (row["id"], report)
        assert "outputCollations" not in report, (row["id"], report)
    else:
        assert report.get("outputCollations") == [c["collation"] for c in row["output_columns"]], (
            row["id"], report)


def native_script(rows, canonical):
    assert len(rows) == len(canonical), "missing recursive canonical witness"
    commands = [
        "BEGIN;", "SET LOCAL statement_timeout = '5s';",
        "CREATE FUNCTION pg_temp.recursive_analysis(q TEXT) RETURNS TEXT LANGUAGE plpgsql AS $$ "
        "DECLARE result TEXT; BEGIN EXECUTE 'PREPARE recursive_probe AS ' || q; "
        "DEALLOCATE recursive_probe; RETURN '00000'; EXCEPTION WHEN OTHERS THEN "
        "result := SQLSTATE; IF EXISTS (SELECT 1 FROM pg_prepared_statements "
        "WHERE name='recursive_probe') THEN DEALLOCATE recursive_probe; END IF; RETURN result; END $$;",
    ]
    expected = []
    for row, rendered in zip(rows, canonical):
        for layout, sql in (("source", row["sql"]), ("canonical", rendered)):
            tag = f"analysis:{row['id']}:{layout}:"
            commands.append("SELECT " + sql_literal(tag) +
                            " || pg_temp.recursive_analysis(" +
                            sql_literal(sql.strip().removesuffix(";")) + ");")
            expected.append(tag + row["postgres_sqlstate"])
    for row, rendered in zip(rows, canonical):
        if row["postgres_columns"] is None:
            continue
        # Native-success/static-Unsupported cases still receive descriptions.
        # Their acceptance is not upgraded into a static certificate.
        for layout, sql in (("source", row["sql"]), ("canonical", rendered)):
            tag = f"description:{row['id']}:{layout}"
            commands.extend([
                "\\echo " + tag,
                "PREPARE recursive_descriptor AS " + sql.strip().removesuffix(";") + ";",
                "EXECUTE recursive_descriptor\\gdesc",
                "DEALLOCATE recursive_descriptor;",
            ])
            expected.extend([tag, *("|".join(c) for c in row["postgres_columns"])])
    commands.append("ROLLBACK;")
    return "\n".join(commands), expected


def validate_native(stdout, expected):
    assert stdout.splitlines() == expected, (stdout.splitlines(), expected)


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    target = parser.add_mutually_exclusive_group(required=True)
    target.add_argument("--local-bin")
    target.add_argument("--dsn")
    parser.add_argument("--psql")
    args = parser.parse_args()
    rows, canonical = load_cases(), []
    for row in rows:
        static_check(row)
        replay("identity", row["sql"])
        canonical.append(replay("postgres", row["sql"])["sql"])
    script, expected = native_script(rows, canonical)
    with connection(args) as psql:
        version = int(run([*psql, "-X", "-qAt", "-c", "SHOW server_version_num;"]).stdout.strip())
        assert 160000 <= version < 170000, "recursive boundary observations target PostgreSQL 16"
        result = run([*psql, "-X", "-qAt", "-v", "ON_ERROR_STOP=1"], input=script, timeout=120)
        validate_native(result.stdout, expected)
    print("PASS: 85 authored recursive boundaries: 42 exact static outputs, 38 Invalid, 5 Unsupported")
    print("PASS: PostgreSQL 16: 170 source/canonical PREPARE outcomes; 90 prepared result descriptions")
    print("Scope: analysis-only evidence; no recursive query values, termination, or downloaded SQL execution claimed.")


if __name__ == "__main__":
    main()
