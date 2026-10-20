#!/usr/bin/env python3
"""Check array subscripts/slices, native descriptors and binding preservation."""
import argparse
import json

from check_array_types_cli import describe_script, reject_sqlite, validate_results, validity
from check_assurance_cli import assert_report, invoke
from check_extended_types_cli import database_script
from check_pagination_cli import ROOT, replay, prepare_capture
from check_postgresql_cli import connection, marker, parse_results, run
from check_renderer_corpus import parameters

FIXTURES = ROOT / "fixtures/array_subscripts"
LABEL_SYNTAX_GAPS = {"SELECT NULL::FLOAT", "SELECT (NULL::FLOAT[])[1]"}


def load_cases():
    rows = json.loads((FIXTURES / "synthetic.json").read_text())
    concrete = [json.loads(line) for line in (FIXTURES / "concrete.jsonl").read_text().splitlines()]
    for population in (rows, concrete):
        assert len(population) == len({row["id"] for row in population}) == len({row["sql"] for row in population}) == 50
    for row in rows:
        assert len(row["output_columns"]) == 1
        assert row["output_columns"][0]["name"] == "v"
        assert row["output_columns"][0]["nullable"] is True
        assert {index for _, index in parameters(row["sql"], "postgres")} == set(
            range(1, len(row["parameter_values"]) + 1))
        assert parameters(row["sql"], "postgres") == parameters(row["sqlite_sql"], "sqlite")
    return rows, concrete


def label_cases():
    """Keep every native observation, with two explicit parser exclusions."""
    rows = json.loads((FIXTURES / "labels.json").read_text())
    assert len(rows) == len({row["sql"] for row in rows}) == 87
    assert all(set(row) == {"sql", "name", "type"} for row in rows)
    assert {row["sql"] for row in rows if row["sql"] in LABEL_SYNTAX_GAPS} == LABEL_SYNTAX_GAPS
    supported = [{
        "sql": row["sql"], "parameter_types": "", "parameter_values": [],
        # Only the name is asserted here; full type/nullability checks use the
        # independently authored 50-case population, not fabricated metadata.
        "output_columns": [{"name": row["name"]}],
        "postgres_display_type": row["type"],
    } for row in rows if row["sql"] not in LABEL_SYNTAX_GAPS]
    assert len(supported) == 85
    return supported


def label_validity(case):
    report = assert_report(["--assurance", "contract", case["sql"]], "valid", "contract")
    columns = report.get("outputColumns")
    assert isinstance(columns, list) and len(columns) == 1, report
    assert columns[0]["name"] == case["output_columns"][0]["name"], report
    return report


def validate_descriptors(actual, expected):
    """Compare ordered names and exact type modifiers; no set conversion."""
    assert actual == expected, (actual, expected)
    return len(expected)


def runtime_cases():
    examples = [
        ("(ARRAY[1])[2147483648]", "", [], "22003"),
        ("(ARRAY[1])[CAST($1 AS INTEGER)]", "text", ["bad integer"], "22P02"),
        ("(ARRAY[1])[1/$1]", "int", [0], "22012"),
        ("(ARRAY[[1],[2,3]])[1][1]", "", [], "2202E"),
        ("(CAST($1 AS INTEGER[]))[1]", "text", ["bad array"], "22P02"),
    ]
    return [{
        "sql": f"SELECT {expr} AS v;", "parameter_types": types, "parameter_values": values,
        "output_columns": [{"name": "v", "type": "int32", "nullable": True}], "sqlstate": state,
    } for expr, types, values, state in examples]


def error_script(cases, canonical):
    assert len(cases) == len(canonical), "missing rendered subscript runtime case"
    commands, expected = ["BEGIN;"], {}
    for i, (case, rendered) in enumerate(zip(cases, canonical), 1):
        for form, sql in (("source", case["sql"]), ("postgres", rendered)):
            capture = prepare_capture(sql, case["parameter_types"], case["parameter_values"], error=True)
            key = marker("subscript_error", i, True, form)
            commands += [*capture[:-1], "\\echo " + key, capture[-1], "DEALLOCATE pagination_parameters;"]
            expected[key] = (1, [[case["sqlstate"]]])
    commands.append("ROLLBACK;")
    return "\n".join(commands), expected


def parse_failure(sql):
    result = invoke(["--render-assurance", "identity", sql])
    report = json.loads(result.stdout)
    assert result.returncode == 1 and report["status"] == "invalid", report
    assert report["diagnostic"]["code"] == "input.parse", report


def boundaries():
    invalid = [
        "SELECT (1)[1]", "SELECT (NULL)[1]", "SELECT ('{1,2}')[1]",
        "SELECT (ARRAY[1])['1'::TEXT]", "SELECT (ARRAY[1])[TRUE]",
        "SELECT (ARRAY[1])[DATE '2024-01-01']",
        "SELECT (ARRAY[1])[1:'2'::VARCHAR]", "SELECT (ARRAY[1])[FALSE:1]",
        "SELECT ((ARRAY[[1,2],[3,4]])[1])[2]",
    ]
    unsupported = [
        "SELECT ('[1,2]'::JSONB)[1]",
        "SELECT (ARRAY[1])[1][1][1][1][1][1][1]",
    ]
    syntax = [
        "SELECT (ARRAY[1])[]", "SELECT (ARRAY[1])[1:2:3]",
        "SELECT ARRAY[1,2][1]", "SELECT CAST('{1,2}' AS INTEGER[])[1]",
        "SELECT COALESCE(ARRAY[1],ARRAY[2])[1]",
        "SELECT '{1,2}'::INTEGER[][1]",
        *sorted(LABEL_SYNTAX_GAPS),
    ]
    for status, queries in (("invalid", invalid), ("unsupported", unsupported)):
        for sql in queries:
            assert_report(["--assurance", "contract", sql], status, "contract")
    for sql in syntax:
        parse_failure(sql)
    assert_report(["--assurance", "checked", "SELECT (ARRAY[1])[1]"], "rejected", "checked")
    return len(invalid) + len(unsupported) + len(syntax) + 1


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
    errors, labels = runtime_cases(), label_cases()
    error_canonical, label_canonical = [], []
    for case in errors:
        validity(case)
        error_canonical.append(replay("postgres", case["sql"])["sql"])
    for case in labels:
        label_validity(case)
        replay("identity", case["sql"])
        label_canonical.append(replay("postgres", case["sql"])["sql"])
    count = boundaries()
    values_sql, values = database_script(rows, canonical)
    metadata_sql, metadata = describe_script(rows + labels, canonical + label_canonical)
    errors_sql, expected_errors = error_script(errors, error_canonical)
    with connection(args) as psql:
        result = run([*psql, "-X", "-q", "-v", "ON_ERROR_STOP=1"], input=values_sql, timeout=120)
        validate_results(parse_results(result.stdout), values)
        result = run([*psql, "-X", "-qAt", "-v", "ON_ERROR_STOP=1"], input=metadata_sql, timeout=120)
        validate_descriptors(result.stdout.splitlines(), metadata)
        result = run([*psql, "-X", "-q", "-v", "ON_ERROR_STOP=1"], input=errors_sql, timeout=120)
        validate_results(parse_results(result.stdout), expected_errors)
        version = run([*psql, "-X", "-At", "-c", "SHOW server_version;"]).stdout.strip()
    print("PASS: 50 subscript/slice certificates, 50 unchanged source renderings and 50 SQLite rejections")
    print(f"PASS: {count} boundaries; PostgreSQL {version}: {len(values)} value/OID observations")
    print(f"PASS: {len(metadata)} descriptors, 85 output-label certificates and {len(expected_errors)} expected errors")
    print("Scope: exact static types and finite native observations; source corpus SQL is never executed.")


if __name__ == "__main__":
    main()
