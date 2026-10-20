#!/usr/bin/env python3
"""Verify ARRAY construction, contextual casts, rendering and native boundaries."""
import argparse
import json

from check_array_types_cli import describe_script, reject_sqlite, validate_results, validity
from check_assurance_cli import assert_report
from check_extended_types_cli import database_script
from check_pagination_cli import ROOT, replay, prepare_capture
from check_postgresql_cli import connection, marker, parse_results, run
from check_renderer_corpus import parameters

FIXTURES = ROOT / "fixtures/array_constructors"


def load_cases():
    rows = json.loads((FIXTURES / "synthetic.json").read_text())
    source = [json.loads(line) for line in (FIXTURES / "concrete.jsonl").read_text().splitlines()]
    for population in (rows, source):
        assert len(population) == len({row["id"] for row in population}) == len({row["sql"] for row in population}) == 50
    for row in rows:
        assert {index for _, index in parameters(row["sql"], "postgres")} == set(
            range(1, len(row["parameter_values"]) + 1))
        assert parameters(row["sql"], "postgres") == parameters(row["sqlite_sql"], "sqlite")
    return rows, source


def runtime_cases():
    # All expressions are statically admitted. Rectangular shape, successful
    # element conversion and arithmetic safety are execution obligations.
    examples = [
        ("ARRAY[[1],[2,3]]", "", [], "2202E"),
        ("ARRAY[ARRAY[1],NULL::INTEGER[]]", "", [], "2202E"),
        ("ARRAY[ARRAY[],ARRAY[1]]::INTEGER[]", "", [], "2202E"),
        ("ARRAY[$1]::INTEGER[]", "text", ["bad integer"], "22P02"),
        ("ARRAY[1/$1]", "int", [0], "22012"),
        ("ARRAY['null'::JSONB]::INTEGER[]", "", [], "22023"),
        ("ARRAY[2147483648]::INTEGER[]", "", [], "22003"),
    ]
    return [{
        "sql": f"SELECT {expr} AS v;", "parameter_types": types, "parameter_values": values,
        "output_columns": [{"name": "v", "type": "integer[]", "nullable": False}], "sqlstate": state,
    } for expr, types, values, state in examples]


def error_script(cases, canonical):
    assert len(cases) == len(canonical), "missing rendered runtime boundary"
    commands, expected = ["BEGIN;"], {}
    for i, (case, rendered) in enumerate(zip(cases, canonical), 1):
        for form, sql in (("source", case["sql"]), ("postgres", rendered)):
            capture = prepare_capture(sql, case["parameter_types"], case["parameter_values"], error=True)
            key = marker("array_constructor_error", i, True, form)
            commands += [*capture[:-1], "\\echo " + key, capture[-1], "DEALLOCATE pagination_parameters;"]
            expected[key] = (1, [[case["sqlstate"]]])
    commands.append("ROLLBACK;")
    return "\n".join(commands), expected


def label_cases():
    return [{
        "sql": f"SELECT {expr};", "parameter_types": "", "parameter_values": [],
        "output_columns": [{"name": name, "type": "integer[]", "nullable": False}],
        "postgres_display_type": "integer[]",
    } for expr, name in [
        ("ARRAY[1]", "array"), ("CAST(ARRAY[] AS INTEGER[])", "array"),
        ("CAST(CAST(ARRAY[1] AS INTEGER[]) AS INTEGER[])", "array"),
        ("COALESCE(ARRAY[1],ARRAY[2])", "coalesce"),
    ]]


def modifier_cases():
    # CHAR without a length in declaration SQL means CHAR(1), whereas the
    # unmodified analyzed character OID is bpchar. Reports must distinguish
    # those identities rather than rendering result types as declarations.
    examples = [
        ("$1", "char(3)", ["abcd"], "bpchar", "abcd", "bpchar"),
        ("$1", "char(3)[]", ["{abcd,NULL}"], "bpchar[]", "{abcd,NULL}", "bpchar[]"),
        ("ARRAY['abc'::CHAR(3),NULL]", "", [], "bpchar[]", "{abc,NULL}", "bpchar[]"),
        ("ARRAY['a'::CHAR(2),'bc'::CHAR(3)]", "", [], "bpchar[]", '{"a ","bc "}', "bpchar[]"),
        ("ARRAY['abc'::CHAR(2)]", "", [], "char(2)[]", "{ab}", "character(2)[]"),
        ("COALESCE('abc'::CHAR(2),NULL)", "", [], "bpchar", "ab", "bpchar"),
    ]
    return [{
        "sql": f"SELECT {expr} AS v;", "parameter_types": types, "parameter_values": values,
        "output_columns": [{"name": "v", "type": contract_type, "nullable": False}],
        "expected_value": value, "postgres_display_type": display,
        "postgres_type": "character[]" if display == "character(2)[]" else
                         "character[]" if display == "bpchar[]" else "character",
    } for expr, types, values, contract_type, value, display in examples]


def boundaries():
    invalid = [
        "SELECT ARRAY[]", "SELECT ARRAY[[]]", "SELECT ARRAY[1,TRUE]",
        "SELECT ARRAY[1,ARRAY[2]]", "SELECT ARRAY[ARRAY[],ARRAY[1]]",
        "SELECT ARRAY[COALESCE(ARRAY[],ARRAY[1])]::INTEGER[]",
        "SELECT ARRAY[DATE '2024-01-01',TIMESTAMP '2024-01-01 12:00']::TIME[]",
        "SELECT ARRAY[TRUE]::BIGINT[]", "SELECT ARRAY[1]::JSONB[]",
        "SELECT ARRAY[1] = ARRAY[2147483648]",
        "SELECT 1 WHERE ARRAY[TRUE]", "SELECT 1 LIMIT ARRAY[1]",
    ]
    for sql in invalid:
        assert_report(["--assurance", "contract", sql], "invalid", "contract")
    for sql in ("SELECT ARRAY[JSON '{}'] = ARRAY[JSON '{}']", "SELECT DISTINCT ARRAY[JSON '{}']"):
        assert_report(["--assurance", "contract", sql], "unsupported", "contract")
    # Coarse types are deliberately insufficient for contextual element rules.
    assert_report(["--assurance", "checked", "SELECT ARRAY[1]"], "rejected", "checked")
    return len(invalid) + 3


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    target = parser.add_mutually_exclusive_group(required=True)
    target.add_argument("--local-bin")
    target.add_argument("--dsn")
    parser.add_argument("--psql")
    args = parser.parse_args()
    rows, source = load_cases()
    canonical = []
    for row in rows:
        validity(row)
        replay("identity", row["sql"])
        canonical.append(replay("postgres", row["sql"])["sql"])
        reject_sqlite(row)
    for row in source:
        for profile in ("identity", "postgres"):
            replay(profile, row["sql"])
    extra = modifier_cases()
    for case in extra:
        validity(case)
        canonical.append(replay("postgres", case["sql"])["sql"])
    rows = rows + extra
    errors, labels = runtime_cases(), label_cases()
    error_canonical, label_canonical = [], []
    for cases, rendered in ((errors, error_canonical), (labels, label_canonical)):
        for case in cases:
            validity(case)
            rendered.append(replay("postgres", case["sql"])["sql"])
    count = boundaries()
    values_sql, values = database_script(rows, canonical)
    metadata_sql, metadata = describe_script(rows + labels, canonical + label_canonical)
    errors_sql, expected_errors = error_script(errors, error_canonical)
    with connection(args) as psql:
        result = run([*psql, "-X", "-q", "-v", "ON_ERROR_STOP=1"], input=values_sql, timeout=120)
        validate_results(parse_results(result.stdout), values)
        result = run([*psql, "-X", "-qAt", "-v", "ON_ERROR_STOP=1"], input=metadata_sql, timeout=120)
        assert result.stdout.splitlines() == metadata, (result.stdout.splitlines(), metadata)
        result = run([*psql, "-X", "-q", "-v", "ON_ERROR_STOP=1"], input=errors_sql, timeout=120)
        validate_results(parse_results(result.stdout), expected_errors)
        version = run([*psql, "-X", "-At", "-c", "SHOW server_version;"]).stdout.strip()
    print("PASS: 50 ARRAY constructor certificates, 50 unchanged source renderings and 50 SQLite rejections")
    print(f"PASS: {count} static boundaries and {len(extra)} character modifier regressions; PostgreSQL {version}: {len(values)} value/OID observations")
    print(f"PASS: {len(metadata)} exact result descriptors and {len(expected_errors)} expected runtime errors")
    print("Scope: independent static derivations and finite native observations; source corpus SQL is never executed.")


if __name__ == "__main__":
    main()
