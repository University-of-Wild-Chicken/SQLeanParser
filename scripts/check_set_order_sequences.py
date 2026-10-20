#!/usr/bin/env python3
"""Authored SQL92 sort-resolution sequences, distinct from set-tree syntax.

PostgreSQL resolves an unknown target when it first becomes a sort key. A
later duplicate-label reference can therefore compare different transformed
expressions, even when the original projections were identical. Native probes
only PREPARE and describe these fixed authored statements; they never execute
them or read any downloaded source corpus.
"""
import argparse
from collections import Counter
import hashlib
import json

from check_assurance_cli import assert_report
from check_pagination_cli import ROOT, replay
from check_postgresql_cli import connection, run, sql_literal

FIXTURE = ROOT / "fixtures/set_operations/order_sequences.json"
DIGEST = "95bfd819bc9f0e5d2102c35b7e9dfcabe55d549731f5ae4c99281990f2757be9"


def load_cases():
    rows = json.loads(FIXTURE.read_text())
    assert hashlib.sha256(json.dumps(rows, sort_keys=True, separators=(",", ":")).encode()).hexdigest() == DIGEST
    assert len(rows) == len({r["id"] for r in rows}) == len({r["sql"] for r in rows}) == 80
    assert Counter(r["expected_status"] for r in rows) == {"valid": 60, "invalid": 20}
    assert Counter(r["expression_kind"] for r in rows) == {
        "unknown-null": 20, "unknown-string": 20, "known-integer": 20, "known-text": 20}
    assert all(r["source_kind"] == "synthetic" for r in rows)
    return rows


def static_check(row):
    columns = None if row["output_columns"] is None else tuple(
        (column["name"], column["type"], column["nullable"]) for column in row["output_columns"])
    report = assert_report(["--assurance", "contract", row["sql"]],
                           row["expected_status"], "contract", columns)
    if row["diagnostic"] is not None:
        assert report["diagnostic"]["code"] == row["diagnostic"], (row["id"], report)


def native_script(rows, canonical):
    assert len(rows) == len(canonical), "missing canonical sequence witness"
    commands = [
        "BEGIN;", "SET LOCAL statement_timeout = '5s';",
        "CREATE FUNCTION pg_temp.sequence_analysis(q TEXT) RETURNS TEXT LANGUAGE plpgsql AS $$ "
        "DECLARE result TEXT; BEGIN EXECUTE 'PREPARE sequence_probe AS ' || q; "
        "DEALLOCATE sequence_probe; RETURN '00000'; EXCEPTION WHEN OTHERS THEN "
        "result := SQLSTATE; IF EXISTS (SELECT 1 FROM pg_prepared_statements "
        "WHERE name='sequence_probe') THEN DEALLOCATE sequence_probe; END IF; RETURN result; END $$;",
    ]
    expected = []
    for row, rendered in zip(rows, canonical):
        for layout, sql in (("source", row["sql"]), ("canonical", rendered)):
            tag = f"analysis:{row['id']}:{layout}:"
            commands.append("SELECT " + sql_literal(tag) +
                            " || pg_temp.sequence_analysis(" +
                            sql_literal(sql.strip().removesuffix(";")) + ");")
            expected.append(tag + row["postgres_sqlstate"])
    for row, rendered in zip(rows, canonical):
        if row["postgres_columns"] is None:
            continue
        for layout, sql in (("source", row["sql"]), ("canonical", rendered)):
            tag = f"description:{row['id']}:{layout}"
            commands.extend([
                "\\echo " + tag,
                "PREPARE descriptor_probe AS " + sql.strip().removesuffix(";") + ";",
                # psql describes the prepared result; it does not execute it.
                "EXECUTE descriptor_probe\\gdesc",
                "DEALLOCATE descriptor_probe;",
            ])
            expected.extend([tag, *("|".join(column) for column in row["postgres_columns"])])
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
        assert 160000 <= version < 170000, "sort-resolution observations target PostgreSQL 16"
        result = run([*psql, "-X", "-qAt", "-v", "ON_ERROR_STOP=1"],
                     input=script, timeout=120)
        validate_native(result.stdout, expected)
    print("PASS: 80 authored sort sequences: 60 exact static outputs, 20 rejected ambiguities; both renderer profiles")
    print("PASS: PostgreSQL 16: 160 source/canonical PREPARE outcomes; 120 prepared result descriptions")
    print("Scope: static resolution and analysis-only metadata; no query values or downloaded source SQL are executed.")


if __name__ == "__main__":
    main()
