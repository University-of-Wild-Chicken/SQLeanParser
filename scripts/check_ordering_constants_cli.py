#!/usr/bin/env python3
"""Regression guard for PostgreSQL's SQL92 ORDER BY constant classification."""
import argparse
from collections import Counter
import hashlib
import json

from check_advanced_cli import question_parameters
from check_assurance_cli import assert_report
from check_pagination_cli import ROOT, replay
from check_postgresql_cli import connection, run, sql_literal

FIXTURE = ROOT / "fixtures/ordering_constants/cases.json"
DIGEST = "42bcd2cf5010e75cf4a22d1091f4c2b36f651a38ccdc28b8b00ce3a2448212d5"


def load_cases():
    rows = json.loads(FIXTURE.read_text())
    assert hashlib.sha256(json.dumps(rows, sort_keys=True, separators=(",", ":")).encode()).hexdigest() == DIGEST
    assert len(rows) == len({r["id"] for r in rows}) == len({r["sql"] for r in rows}) == 108
    assert Counter(r["expected_status"] for r in rows) == {"valid": 59, "invalid": 45, "unsupported": 4}
    assert all(r["source_kind"] == "synthetic" for r in rows)
    return rows


def static_check(row):
    args = ["--assurance", "contract"]
    if row["parameter_types"]:
        args += ["--param-types", row["parameter_types"]]
    columns = (("x", "int32", False), ("y", "int32", False)) if row["expected_status"] == "valid" else None
    report = assert_report([*args, row["sql"]], row["expected_status"], "contract", columns)
    if row["diagnostic"] is not None:
        assert report["diagnostic"]["code"] == row["diagnostic"], (row["id"], report)


def analysis_script(rows, canonical):
    assert len(rows) == len(canonical), "missing canonical sort query"
    commands = [
        "BEGIN;", "SET LOCAL statement_timeout = '5s';",
        "CREATE FUNCTION pg_temp.sort_analysis(q TEXT, declarations TEXT) RETURNS TEXT "
        "LANGUAGE plpgsql AS $$ DECLARE result TEXT; BEGIN "
        "EXECUTE 'PREPARE sort_probe' || declarations || ' AS ' || q; "
        "DEALLOCATE sort_probe; RETURN '00000'; "
        "EXCEPTION WHEN OTHERS THEN result := SQLSTATE; "
        "IF EXISTS (SELECT 1 FROM pg_prepared_statements WHERE name='sort_probe') THEN "
        "DEALLOCATE sort_probe; END IF; RETURN result; END $$;",
    ]
    expected = []
    for row, rendered in zip(rows, canonical):
        declarations = " (" + row["parameter_types"] + ")" if row["parameter_types"] else ""
        for sql in (row["sql"], rendered):
            commands.append("SELECT pg_temp.sort_analysis(" +
                            sql_literal(question_parameters(sql).strip().removesuffix(";")) + "," +
                            sql_literal(declarations) + ");")
            expected.append(row["postgres_sqlstate"])
    commands.append("ROLLBACK;")
    return "\n".join(commands), expected


def validate_analysis(stdout, expected):
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
    script, expected = analysis_script(rows, canonical)
    with connection(args) as psql:
        result = run([*psql, "-X", "-qAt", "-v", "ON_ERROR_STOP=1"], input=script, timeout=120)
        validate_analysis(result.stdout, expected)
        version = run([*psql, "-X", "-At", "-c", "SHOW server_version;"]).stdout.strip()
    print(f"PASS: {len(rows)} authored ORDER BY boundaries and exact renderer roundtrips")
    print(f"PASS: PostgreSQL {version}: {len(expected)} source/canonical PREPARE outcomes")
    print("Scope: SQL92 constant/ordinal classification; no downloaded SQL is executed.")


if __name__ == "__main__":
    main()
