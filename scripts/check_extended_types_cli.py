#!/usr/bin/env python3
"""Check exact scalar validity and real parameter execution for type coverage.

Native observations cover 50 synthetic statements, not downloaded application
SQL. External statements receive structural rendering checks, with their
provenance separately reproduced by extract_extended_type_corpus.py.
"""
import argparse
import json
import subprocess

from check_advanced_cli import literal, question_parameters
from check_assurance_cli import assert_report
from check_pagination_cli import EXE, ROOT, replay
from check_postgresql_cli import connection, copy_result, marker, parse_results, run, sql_literal

FIXTURES = ROOT / "fixtures/extended_types"


def load_cases():
    synthetic = json.loads((FIXTURES / "synthetic.json").read_text())
    concrete = [json.loads(line) for line in (FIXTURES / "concrete.jsonl").read_text().splitlines()]
    for cases in (synthetic, concrete):
        assert len(cases) == len({case["id"] for case in cases}) == len({case["sql"] for case in cases}) == 50
    return synthetic, concrete


def assurance(case):
    args = ["--assurance", "contract"]
    if case["parameter_types"]:
        args += ["--param-types", case["parameter_types"]]
    args += [case["sql"]]
    return assert_report(args, "valid", "contract", (("v", case["contract_type"], case["nullable"]),))


def capture(sql, types, values):
    # Native PREPARE declarations use SQL types; ? is our metadata nullability
    # suffix and has no role in PostgreSQL's type declaration syntax.
    declarations = types.replace("?", "")
    declaration = f" ({declarations})" if declarations else ""
    source = question_parameters(sql).strip().removesuffix(";")
    observed = f"SELECT v::text, pg_typeof(v)::text FROM ({source}) AS observed"
    execute = "EXECUTE exact_type_parameters"
    if values:
        execute += " (" + ", ".join(map(literal, values)) + ")"
    body = "BEGIN RETURN QUERY EXECUTE " + sql_literal(execute) + "; END;"
    return [
        f"PREPARE exact_type_parameters{declaration} AS {observed};",
        "CREATE OR REPLACE FUNCTION pg_temp.exact_type_rows() RETURNS TABLE (value TEXT, type TEXT) "
        "LANGUAGE plpgsql VOLATILE AS " + sql_literal(body) + ";",
        copy_result("SELECT * FROM pg_temp.exact_type_rows()"),
    ]


def database_script(cases, rendered):
    assert len(cases) == len(rendered), "missing rendered type case"
    commands = ["\\encoding UTF8", "BEGIN;", "SET LOCAL statement_timeout = '5s';",
                "SET LOCAL standard_conforming_strings = on;", "SET LOCAL timezone = 'UTC';",
                "SET LOCAL datestyle = 'ISO, YMD';", "SET LOCAL intervalstyle = 'postgres';",
                "SET LOCAL bytea_output = 'hex';", "SET LOCAL extra_float_digits = 3;"]
    expected = {}
    for index, (case, canonical) in enumerate(zip(cases, rendered), 1):
        for form, sql in (("source", case["sql"]), ("postgres", canonical)):
            parts = capture(sql, case["parameter_types"], case["parameter_values"])
            key = marker("exact_types", index, True, form)
            commands += parts[:-1] + ["\\echo " + key, parts[-1], "DEALLOCATE exact_type_parameters;"]
            expected[key] = (2, [[case["expected_value"], case["postgres_type"]]])
    commands.append("ROLLBACK;")
    return "\n".join(commands), expected


def boundaries():
    invalid = [
        "SELECT JSON '{}' = JSON '{}'",
        "SELECT DISTINCT JSON '{}'",
        "SELECT JSON '{}' AS v ORDER BY v",
        "SELECT JSON '{}' AS v ORDER BY 1",
        "SELECT JSON '{}' IN (JSON '{}')",
        "SELECT JSON '{}' BETWEEN JSON '{}' AND JSON '{}'",
    ]
    for sql in invalid:
        assert_report(["--assurance", "contract", sql], "invalid", "contract")
        assert_report(["--assurance", "checked", sql], "rejected", "checked")
    # Equality/group/set paths in the expanded tier must not inherit TEXT's
    # comparison support merely because JSON's payload looks textual.
    extra = [
        "SELECT COUNT(*) FROM (SELECT JSON '{}' AS v) AS q GROUP BY v",
        "SELECT JSON '{}' UNION SELECT JSON '{}'",
        "SELECT JSON '{}' INTERSECT ALL SELECT JSON '{}'",
        "SELECT JSON '{}' EXCEPT ALL SELECT JSON '{}'",
        "SELECT JSON '{}' AS v UNION ALL SELECT JSON '{}' ORDER BY 1",
        "SELECT * FROM (SELECT JSON '{}' AS v) AS a JOIN (SELECT JSON '{}' AS v) AS b USING(v)",
    ]
    for sql in extra:
        assert_report(["--assurance", "checked", sql], "rejected", "checked")
    for sql in [
        "SELECT JSONB '{}' = JSONB '{}'",
        "SELECT DISTINCT JSONB '{}' AS v ORDER BY 1",
        "SELECT JSON '{}' UNION ALL SELECT JSON '{}'",
    ]:
        assert_report(["--assurance", "checked", sql], "checked", "checked")
    return len(invalid) * 2 + len(extra) + 3


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    group = parser.add_mutually_exclusive_group(required=True)
    group.add_argument("--local-bin")
    group.add_argument("--dsn")
    parser.add_argument("--psql")
    args = parser.parse_args()
    synthetic, concrete = load_cases()
    rendered = []
    for case in synthetic:
        assurance(case)
        replay("identity", case["sql"])
        rendered.append(replay("postgres", case["sql"])["sql"])
    for case in concrete:
        for mode in ("identity", "postgres"):
            replay(mode, case["sql"])
    count = boundaries()
    script, expected = database_script(synthetic, rendered)
    with connection(args) as psql:
        result = run([*psql, "-X", "-q", "-v", "ON_ERROR_STOP=1"], input=script, timeout=120)
        actual = parse_results(result.stdout)
        assert actual.keys() == expected.keys(), actual.keys() ^ expected.keys()
        for key, wanted in expected.items():
            assert actual[key] == wanted, (key, actual[key], wanted)
        version = run([*psql, "-X", "-At", "-c", "SHOW server_version;"]).stdout.strip()
    print("PASS: 50 synthetic exact-type certificates; 50 unchanged concrete statements; "
          "identity/PostgreSQL roundtrip and canonical checks")
    print(f"PASS: {count} comparison boundaries; PostgreSQL {version}: "
          f"{len(expected)} PREPARE/EXECUTE value and native-type observations")
    print("Scope: native values/types of the synthetic cases; no application-schema "
          "or universal database-semantic equivalence claim.")


if __name__ == "__main__":
    main()
