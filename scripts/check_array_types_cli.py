#!/usr/bin/env python3
"""Verify array contracts, native values and exact prepared result metadata."""
import argparse
import json
import subprocess

from check_advanced_cli import literal, question_parameters
from check_assurance_cli import assert_report
from check_extended_types_cli import database_script
from check_pagination_cli import EXE, ROOT, replay, prepare_capture as capture_error
from check_postgresql_cli import connection, marker, parse_results, run
from check_renderer_corpus import parameters

FIXTURES = ROOT / "fixtures/array_types"


def load_cases():
    cases = json.loads((FIXTURES / "synthetic.json").read_text())
    concrete = [json.loads(line) for line in (FIXTURES / "concrete.jsonl").read_text().splitlines()]
    for rows in (cases, concrete):
        assert len(rows) == len({row["id"] for row in rows}) == len({row["sql"] for row in rows}) == 50
    for case in cases:
        assert len(case["output_columns"]) == 1
        assert {index for _, index in parameters(case["sql"], "postgres")} == set(
            range(1, len(case["parameter_values"]) + 1))
        assert parameters(case["sql"], "postgres") == parameters(case["sqlite_sql"], "sqlite")
    return cases, concrete


def validity(case):
    args = ["--assurance", "contract"]
    if case["parameter_types"]:
        args += ["--param-types", case["parameter_types"]]
    columns = tuple((c["name"], c["type"], c["nullable"]) for c in case["output_columns"])
    return assert_report([*args, case["sql"]], "valid", "contract", columns)


def reject_sqlite(case):
    result = subprocess.run([str(EXE), "--render-assurance", "sqlite"], input=case["sqlite_sql"],
                            cwd=ROOT, capture_output=True, text=True, timeout=30)
    report = json.loads(result.stdout)
    assert result.returncode in (1, 3) and report["status"] in ("invalid", "unsupported"), report
    assert "array" in str(report).lower(), report


def describe_script(cases, canonical):
    """Describe real prepared SELECTs, retaining result names and type modifiers.

    RETURNS TABLE wrappers and pg_typeof check OIDs but lose typmods. psql's
    gdesc observes the original result descriptor instead; it does not execute
    the statement. Parameter values stay in EXECUTE, never inside its SELECT.
    """
    assert len(cases) == len(canonical), "missing canonical array description"
    commands = ["BEGIN;", "SET LOCAL standard_conforming_strings = on;"]
    expected = []
    for case, rendered in zip(cases, canonical):
        types = case["parameter_types"].replace("?", "")
        declaration = f" ({types})" if types else ""
        values = "(" + ", ".join(map(literal, case["parameter_values"])) + ")" if case["parameter_values"] else ""
        for sql in (case["sql"], rendered):
            commands += [
                "PREPARE array_description" + declaration + " AS " +
                question_parameters(sql).strip().removesuffix(";") + ";",
                "EXECUTE array_description" + values,
                "\\gdesc",
                "DEALLOCATE array_description;",
            ]
            expected.append("v|" + case["postgres_display_type"])
    commands.append("ROLLBACK;")
    return "\n".join(commands), expected


def parameter_modifier_cases():
    # PostgreSQL discards PREPARE parameter typmods, for scalar and array types.
    # Explicit SELECT casts restore modifiers and perform value conversion.
    examples = [
        ("numeric(6,2)", "numeric", "numeric", "numeric(6,2)", "1.234", "1.234", "1.23"),
        ("varchar(2)", "varchar", "character varying", "character varying(2)", "abcd", "abcd", "ab"),
        ("timestamp(2)", "timestamp", "timestamp without time zone", "timestamp(2) without time zone",
         "2024-01-02 03:04:05.123456", "2024-01-02 03:04:05.123456", "2024-01-02 03:04:05.12"),
        ("numeric(6,2)[]", "numeric[]", "numeric[]", "numeric(6,2)[]",
         "{1.234,NULL}", "{1.234,NULL}", "{1.23,NULL}"),
        ("varchar(2)[]", "varchar[]", "character varying[]", "character varying(2)[]",
         "{abcd,NULL}", "{abcd,NULL}", "{ab,NULL}"),
    ]
    result = []
    for declaration, unmodified, oid_name, modified_display, value, original, casted in examples:
        for cast in (False, True):
            result.append({
                "sql": f"SELECT CAST($1 AS {declaration}) AS v;" if cast else "SELECT $1 AS v;",
                "parameter_types": declaration, "parameter_values": [value],
                "output_columns": [{"name": "v", "type": declaration if cast else unmodified, "nullable": False}],
                "postgres_type": oid_name, "postgres_display_type": modified_display if cast else oid_name,
                "expected_value": casted if cast else original,
            })
    return result


def operator_cases():
    return [
        {"sql": "SELECT CAST('{1,NULL}' AS INTEGER[]) = CAST('{1,NULL}' AS INTEGER[]) AS v;",
         "parameter_types": "", "parameter_values": [], "output_columns": [{"name": "v", "type": "bool", "nullable": False}],
         "postgres_type": "boolean", "postgres_display_type": "boolean", "expected_value": "true"},
        {"sql": "SELECT COALESCE(CAST(NULL AS INTEGER[]), CAST('{2147483648}' AS BIGINT[])) AS v;",
         "parameter_types": "", "parameter_values": [], "output_columns": [{"name": "v", "type": "bigint[]", "nullable": False}],
         "postgres_type": "bigint[]", "postgres_display_type": "bigint[]", "expected_value": "{2147483648}"},
        {"sql": """SELECT CAST(CAST('{NULL,"1"}' AS JSONB[]) AS INTEGER[]) AS v;""",
         "parameter_types": "", "parameter_values": [], "output_columns": [{"name": "v", "type": "integer[]", "nullable": False}],
         "postgres_type": "integer[]", "postgres_display_type": "integer[]", "expected_value": "{NULL,1}"},
    ]


def runtime_error_case():
    return {
        "sql": """SELECT CAST(CAST('{"null","1"}' AS JSONB[]) AS INTEGER[]) AS v;""",
        "parameter_types": "", "parameter_values": [],
        "output_columns": [{"name": "v", "type": "integer[]", "nullable": False}],
    }


def runtime_error_script(case, rendered):
    commands, expected = ["BEGIN;"], {}
    for form, sql in (("source", case["sql"]), ("postgres", rendered)):
        capture = capture_error(sql, "", [], error=True)
        key = marker("array_runtime", 1, True, form)
        commands += [*capture[:-1], "\\echo " + key, capture[-1], "DEALLOCATE pagination_parameters;"]
        expected[key] = (1, [["22023"]])
    commands.append("ROLLBACK;")
    return "\n".join(commands), expected


def boundaries():
    invalid = [
        "SELECT CAST('{1}' AS INTEGER[]) = CAST('{1}' AS BIGINT[])",
        "SELECT CAST('{1}' AS INTEGER[]) < CAST('{1}' AS BIGINT[])",
        "SELECT CAST('{1}' AS INTEGER[]) + 1",
        "SELECT CAST(1 AS INTEGER[])",
    ]
    unsupported = [
        """SELECT CAST('{"{}"}' AS JSON[]) = CAST('{"{}"}' AS JSON[])""",
        """SELECT DISTINCT CAST('{"{}"}' AS JSON[])""",
    ]
    for status, queries in (("invalid", invalid), ("unsupported", unsupported)):
        for sql in queries:
            assert_report(["--assurance", "contract", sql], status, "contract")
    # The coarse tier cannot distinguish INTEGER[] from BIGINT[]. It must not
    # accidentally accept their comparison through the shared integer family.
    coarse = [
        "SELECT CAST('{1}' AS INTEGER[]) = CAST('{1}' AS BIGINT[])",
        "SELECT NULLIF(CAST('{1}' AS INTEGER[]), CAST('{1}' AS BIGINT[]))",
        "SELECT GREATEST(CAST('{1}' AS INTEGER[]), CAST('{1}' AS BIGINT[]))",
        "SELECT CASE CAST('{1}' AS INTEGER[]) WHEN CAST('{1}' AS BIGINT[]) THEN 1 ELSE 0 END",
        "SELECT DISTINCT CAST('{1}' AS INTEGER[])",
    ]
    for sql in coarse:
        assert_report(["--assurance", "checked", sql], "rejected", "checked")
    return len(invalid) + len(unsupported) + len(coarse)


def validate_results(actual, expected):
    assert actual.keys() == expected.keys(), actual.keys() ^ expected.keys()
    for key, wanted in expected.items():
        assert actual[key] == wanted, (key, actual[key], wanted)
    return len(expected)


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    target = parser.add_mutually_exclusive_group(required=True)
    target.add_argument("--local-bin")
    target.add_argument("--dsn")
    parser.add_argument("--psql")
    args = parser.parse_args()
    cases, concrete = load_cases()
    postgres = []
    for case in cases:
        validity(case)
        replay("identity", case["sql"])
        postgres.append(replay("postgres", case["sql"])["sql"])
        reject_sqlite(case)
    for case in concrete:
        for mode in ("identity", "postgres"):
            replay(mode, case["sql"])
    extra = parameter_modifier_cases() + operator_cases()
    for case in extra:
        validity(case)
        postgres.append(replay("postgres", case["sql"])["sql"])
    all_cases = cases + extra
    runtime_case = runtime_error_case()
    validity(runtime_case)
    error_script, expected_errors = runtime_error_script(runtime_case, replay("postgres", runtime_case["sql"])["sql"])
    boundary_count = boundaries()
    script, expected = database_script(all_cases, postgres)
    description, metadata = describe_script(all_cases, postgres)
    with connection(args) as psql:
        result = run([*psql, "-X", "-q", "-v", "ON_ERROR_STOP=1"], input=script, timeout=120)
        validate_results(parse_results(result.stdout), expected)
        result = run([*psql, "-X", "-qAt", "-v", "ON_ERROR_STOP=1"], input=description, timeout=120)
        assert result.stdout.splitlines() == metadata, (result.stdout.splitlines(), metadata)
        result = run([*psql, "-X", "-q", "-v", "ON_ERROR_STOP=1"], input=error_script, timeout=120)
        validate_results(parse_results(result.stdout), expected_errors)
        version = run([*psql, "-X", "-At", "-c", "SHOW server_version;"]).stdout.strip()
    print("PASS: 50 array type complete certificates, 50 unchanged source renderings and 50 explicit SQLite rejections")
    print(f"PASS: {len(extra)} parameter-modifier/operator regressions; {boundary_count} failure boundaries")
    print(f"PASS: PostgreSQL {version}: {len(expected)} bound value/OID observations and {len(metadata)} exact result descriptors")
    print("PASS: 2 expected JSON-null conversion errors, distinguished from SQL NULL array elements")
    print("Scope: synthetic finite observations with exact names/modifiers; concrete source SQL is never executed.")


if __name__ == "__main__":
    main()
