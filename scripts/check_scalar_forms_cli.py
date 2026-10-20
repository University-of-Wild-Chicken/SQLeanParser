#!/usr/bin/env python3
"""Full certificates and native observations for scalar/conditional increments."""
import argparse
import json

from check_assurance_cli import assert_report
from check_extended_types_cli import assurance, database_script
from check_pagination_cli import ROOT, replay
from check_postgresql_cli import connection, parse_results, run, sql_literal

FACTORS = ("functions", "conditional")


def load_cases(factor):
    path = ROOT / "fixtures" / factor
    synthetic = json.loads((path / "synthetic.json").read_text())
    concrete = [json.loads(line) for line in (path / "concrete.jsonl").read_text().splitlines()]
    for population in (synthetic, concrete):
        assert len(population) == 50
        assert len({case["id"] for case in population}) == 50
        assert len({case["sql"] for case in population}) == 50
    return synthetic, concrete


def boundaries():
    # Unknown function environments are unsupported, never certified by guessing.
    for sql in ("SELECT application_function(1)", "SELECT private.abs(1)"):
        assert_report(["--assurance", "contract", sql], "unsupported", "contract")
    invalid = [
        "SELECT lower(1)", "SELECT abs(true)", "SELECT substr('a')",
        "SELECT CASE WHEN 1 THEN 2 ELSE 3 END",
        "SELECT CASE WHEN true THEN 1 ELSE DATE '2024-01-01' END",
        "SELECT COALESCE(1, DATE '2024-01-01')",
        "SELECT GREATEST(JSON '{}', JSON '{}')",
        "SELECT NULLIF(JSON '{}', JSON '{}')",
    ]
    for sql in invalid:
        assert_report(["--assurance", "contract", sql], "invalid", "contract")
    return len(invalid) + 2


def catalog_script():
    """Independently compare the Lean-linked finite table to PostgreSQL pg_proc."""
    signatures = json.loads((ROOT / "fixtures/functions/signatures.json").read_text())
    assert len(signatures) == 84
    assert len({(c["name"], tuple(c["inputs"])) for c in signatures}) == len(signatures)
    statements = []
    for index, case in enumerate(signatures):
        arguments = "ARRAY[" + ",".join(sql_literal(t) + "::regtype::oid"
                                       for t in case["inputs"]) + "]::oid[]"
        statements.append(
            f"SELECT {index}, EXISTS(SELECT FROM pg_catalog.pg_proc "
            "WHERE pronamespace='pg_catalog'::regnamespace "
            f"AND proname={sql_literal(case['name'])} "
            f"AND ARRAY(SELECT unnest(proargtypes::oid[]))={arguments} "
            f"AND prorettype={sql_literal(case['output'])}::regtype::oid "
            "AND (proisstrict OR pronargs=0));")
    return "\n".join(statements), [f"{i}|t" for i in range(len(signatures))]


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    target = parser.add_mutually_exclusive_group(required=True)
    target.add_argument("--local-bin")
    target.add_argument("--dsn")
    parser.add_argument("--psql")
    args = parser.parse_args()
    synthetic, rendered = [], []
    for factor in FACTORS:
        cases, concrete = load_cases(factor)
        for case in cases:
            assurance(case)
            replay("identity", case["sql"])
            rendered.append(replay("postgres", case["sql"])["sql"])
        for case in concrete:
            for mode in ("identity", "postgres"):
                replay(mode, case["sql"])
        synthetic.extend(cases)
    count = boundaries()
    script, expected = database_script(synthetic, rendered)
    with connection(args) as psql:
        result = run([*psql, "-X", "-q", "-v", "ON_ERROR_STOP=1"], input=script, timeout=120)
        actual = parse_results(result.stdout)
        assert actual.keys() == expected.keys(), actual.keys() ^ expected.keys()
        for key, wanted in expected.items():
            assert actual[key] == wanted, (key, actual[key], wanted)
        catalog_sql, catalog_expected = catalog_script()
        catalog = run([*psql, "-X", "-qAt", "-v", "ON_ERROR_STOP=1"], input=catalog_sql)
        assert catalog.stdout.splitlines() == catalog_expected, catalog.stdout
        version = run([*psql, "-X", "-At", "-c", "SHOW server_version;"]).stdout.strip()
    print("PASS: 50 synthetic full SELECT certificates plus 50 unchanged source renderings per factor")
    print(f"PASS: {count} validity boundaries; PostgreSQL {version}: "
          f"{len(expected)} separately bound source/rendered value and native-type observations")
    print("PASS: 84 exact argument/return signatures and strictness rules match PostgreSQL pg_proc")
    print("Scope: fixed built-in function environment; downloaded source statements are never executed.")


if __name__ == "__main__":
    main()
