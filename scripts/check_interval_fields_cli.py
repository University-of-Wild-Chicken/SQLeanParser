#!/usr/bin/env python3
"""Verify interval qualifiers, exact typmods, bindings and checked rendering."""
import argparse
import json

from check_array_types_cli import describe_script, validate_results, validity
from check_assurance_cli import assert_report, invoke
from check_extended_types_cli import database_script
from check_extract_cli import error_script, null_script
from check_pagination_cli import ROOT, replay
from check_postgresql_cli import connection, parse_results, run
from check_renderer_corpus import parameters
from generate_interval_field_examples import FIELDS

FIXTURES = ROOT / "fixtures/interval_fields"


def load_cases():
    rows = json.loads((FIXTURES / "synthetic.json").read_text())
    source = [json.loads(line) for line in (FIXTURES / "concrete.jsonl").read_text().splitlines()]
    for population in (rows, source):
        assert len(population) == len({row["id"] for row in population}) == len(
            {row["sql"] for row in population}) == 50
    for row in rows:
        assert row["source_kind"] == "synthetic" and row["sqlite_supported"] is False
        assert len(row["output_columns"]) == 1
        output = row["output_columns"][0]
        assert output["name"] == "v" and type(output["nullable"]) is bool
        type_ = output["type"]
        oid = ("interval[]" if type_.endswith("[]") else "interval") if type_.startswith(
            "interval") else {"bool": "boolean", "timestamp": "timestamp without time zone"}.get(type_, type_)
        assert row["postgres_type"] == oid
        assert row["postgres_display_type"] == {
            "bool": "boolean", "timestamp": "timestamp without time zone"}.get(type_, type_)
        assert row["expected_value"] is None or isinstance(row["expected_value"], str)
        assert row["expected_value"] is not None or output["nullable"]
        assert {slot for _, slot in parameters(row["sql"], "postgres")} == set(
            range(1, len(row["parameter_values"]) + 1))
        assert parameters(row["sql"], "postgres") == parameters(row["sqlite_input"], "sqlite")
    seen = set()
    for row in source:
        assert row["raw_sql"] == row["sql"] and row["transformations"] == []
        assert row["observed_syntax"]["source_free"] is True and row["parameter_types"] is None
        forms = row["observed_syntax"]["interval_fields"]
        assert len(forms) == 1
        form = forms[0]
        assert type(form["mask"]) is int and form["mask"] == FIELDS[form["fields"]]
        assert form["precision"] is None or (type(form["precision"]) is int
                                            and 0 <= form["precision"] <= 6
                                            and form["fields"].endswith("second"))
        seen.add(form["fields"])
    assert seen == set(FIELDS)
    return rows, source


def typmod_script():
    """Inspect native descriptor integers, independent of format_type spelling."""
    commands, expected = ["BEGIN;"], []
    index = 0
    for fields, mask in FIELDS.items():
        for precision in ([None, 0, 2, 6] if fields.endswith("second") else [None]):
            for array in (False, True):
                declaration = "interval " + fields
                if precision is not None:
                    declaration += f"({precision})"
                if array:
                    declaration += "[]"
                typmod = (mask << 16) | (65535 if precision is None else precision)
                commands += [
                    f"CREATE TEMP VIEW interval_descriptor AS SELECT NULL::{declaration} AS v;",
                    f"SELECT {index}, a.attname, a.atttypid::regtype, a.atttypmod, "
                    "pg_catalog.format_type(a.atttypid, a.atttypmod) "
                    "FROM pg_catalog.pg_attribute a WHERE a.attrelid='interval_descriptor'::regclass "
                    "AND a.attnum=1;",
                    "DROP VIEW interval_descriptor;",
                ]
                expected.append(f"{index}|v|interval{'[]' if array else ''}|{typmod}|{declaration}")
                index += 1
    commands.append("ROLLBACK;")
    return "\n".join(commands), expected


def parameter_cases():
    result = []
    for declaration, value, casted in [
        ("interval year", "1 year 2 mons 3 days", "1 year"),
        ("interval day to second(2)", "1 day 01:02:03.456", "1 day 01:02:03.46"),
        ("interval year[]", '{"1 year 2 mons",NULL}', '{"1 year",NULL}'),
        ("interval second(2)[]", "{00:00:01.235,NULL}", "{00:00:01.24,NULL}"),
    ]:
        unmodified = "interval[]" if declaration.endswith("[]") else "interval"
        for cast in (False, True):
            result.append({
                "sql": f"SELECT CAST($1 AS {declaration}) AS v;" if cast else "SELECT $1 AS v;",
                "parameter_types": declaration, "parameter_values": [value],
                "output_columns": [{"name": "v", "type": declaration if cast else unmodified,
                                    "nullable": False}],
                "postgres_type": unmodified,
                "postgres_display_type": declaration if cast else unmodified,
                "expected_value": casted if cast else value,
            })
    return result


def label_cases():
    return [{
        "sql": f"SELECT {expr};", "parameter_types": "", "parameter_values": [],
        "output_columns": [{"name": name, "type": type_, "nullable": nullable}],
        "postgres_display_type": type_,
    } for expr, name, type_, nullable in (
        ("INTERVAL '1' YEAR", "interval", "interval year", False),
        ("'1'::INTERVAL DAY", "interval", "interval day", False),
        ("CAST(INTERVAL '1' MONTH AS TEXT)", "text", "text", False),
        ("CASE WHEN FALSE THEN NULL::INTERVAL YEAR ELSE INTERVAL '1' YEAR END",
         "case", "interval year", True),
        ("COALESCE(NULL::INTERVAL YEAR,INTERVAL '1' YEAR)", "coalesce", "interval year", False),
        ("(ARRAY[INTERVAL '1' YEAR])[1]", "array", "interval year", True),
        ("CAST(INTERVAL '1.234' SECOND(2) AS INTERVAL)", "interval", "interval", False),
        ("INTERVAL '1' DAY + INTERVAL '1' HOUR", "?column?", "interval", False),
    )]


def runtime_cases():
    return [{
        "sql": f"SELECT CAST($1 AS {declaration}) AS v;",
        "parameter_types": "text", "parameter_values": [value],
        "output_columns": [{"name": "v", "type": declaration, "nullable": False}],
        "sqlstate": state,
    } for declaration, value, state in (
        ("interval year", "not an interval", "22007"),
        ("interval year", "2147483648 years", "22015"),
        ("interval day", "123 11", "22007"),
        ("interval second(2)[]", "{not-an-interval}", "22007"),
    )]


def reject_sqlite(case):
    result = invoke(["--render-assurance", "sqlite"], stdin=case["sqlite_input"])
    report = json.loads(result.stdout)
    assert (result.returncode, report["status"], report["diagnostic"]["code"]) in {
        (1, "invalid", "input.parse"),
        *((3, "unsupported", "coverage.sqlite." + code) for code in
          ("PostgreSQL-type", "array-type", "array-constructor", "array-subscript", "extract")),
    }, report


def boundaries():
    invalid = [
        "SELECT 1::INTERVAL YEAR",
        "SELECT INTERVAL '1' YEAR = 1",
        "SELECT ARRAY[INTERVAL '1' YEAR] = ARRAY[1]",
    ]
    unsupported = [
        "SELECT INTERVAL '1' SECOND(7)",
        "SELECT NULL::INTERVAL DAY TO SECOND(7)[]",
        "SELECT (SELECT INTERVAL '1' DAY)",
        "SELECT unknown_function(INTERVAL '1' YEAR)",
        "SELECT INTERVAL '1' MONTH + TRUE",
    ]
    for status, queries in (("invalid", invalid), ("unsupported", unsupported)):
        for sql in queries:
            assert_report(["--assurance", "contract", sql], status, "contract")
    syntax = [
        "SELECT INTERVAL YEAR '1'", "SELECT INTERVAL '1' YEAR(2)",
        "SELECT INTERVAL '1' DAY TO MONTH", "SELECT INTERVAL '1' MONTH TO YEAR",
        "SELECT INTERVAL(2) '1' SECOND", "SELECT INTERVAL(2) '1' YEAR",
        "SELECT INTERVAL '1' SECOND(2,3)", "SELECT INTERVAL '1' SECOND(-1)",
        "SELECT CAST('1' AS INTERVAL YEAR(2))", "SELECT CAST('1' AS INTERVAL(2) YEAR)",
        "SELECT (INTERVAL '1') YEAR", "SELECT INTERVAL '1' AS YEAR TO MONTH",
    ]
    for sql in syntax:
        result = invoke(["--render-assurance", "identity", sql])
        report = json.loads(result.stdout)
        assert (result.returncode, report["status"], report["diagnostic"]["code"]) == (
            1, "invalid", "input.parse"), report
    return len(invalid) + len(unsupported) + len(syntax)


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    target = parser.add_mutually_exclusive_group(required=True)
    target.add_argument("--local-bin")
    target.add_argument("--dsn")
    parser.add_argument("--psql")
    args = parser.parse_args()
    rows, source = load_cases()
    postgres = []
    for row in rows:
        validity(row)
        replay("identity", row["sql"])
        postgres.append(replay("postgres", row["sql"])["sql"])
        reject_sqlite(row)
    # Source statements are certified and rendered only, never sent to a database.
    for row in source:
        form = row["observed_syntax"]["interval_fields"][0]
        type_ = "interval " + form["fields"]
        if form["precision"] is not None:
            type_ += f"({form['precision']})"
        assert_report(["--assurance", "contract", row["sql"]], "valid", "contract",
                      (("interval", type_, False),))
        for profile in ("identity", "postgres"):
            replay(profile, row["sql"])
    extra, errors, labels = parameter_cases(), runtime_cases(), label_cases()
    extra_rendered, error_rendered, label_rendered = [], [], []
    for population, rendered in ((extra, extra_rendered), (errors, error_rendered), (labels, label_rendered)):
        for case in population:
            validity(case)
            rendered.append(replay("postgres", case["sql"])["sql"])
    boundary_count = boundaries()
    values_sql, values = database_script(rows + extra, postgres + extra_rendered)
    nulls_sql, nulls = null_script(rows + extra, postgres + extra_rendered)
    metadata_sql, metadata = describe_script(rows + extra + labels, postgres + extra_rendered + label_rendered)
    errors_sql, expected_errors = error_script(errors, error_rendered)
    typmods_sql, typmods = typmod_script()
    with connection(args) as psql:
        for script, expected in ((values_sql, values), (nulls_sql, nulls), (errors_sql, expected_errors)):
            result = run([*psql, "-X", "-q", "-v", "ON_ERROR_STOP=1"], input=script, timeout=120)
            validate_results(parse_results(result.stdout), expected)
        for script, expected in ((metadata_sql, metadata), (typmods_sql, typmods)):
            result = run([*psql, "-X", "-qAt", "-v", "ON_ERROR_STOP=1"], input=script, timeout=120)
            assert result.stdout.splitlines() == expected, (result.stdout.splitlines(), expected)
        version = run([*psql, "-X", "-At", "-c", "SHOW server_version;"]).stdout.strip()
    print("PASS: 50 synthetic and 50 unchanged source interval qualifier certificates/renderings")
    print(f"PASS: {boundary_count} boundaries, 8 parameter modifier cases and 50 SQLite exclusions")
    print(f"PASS: PostgreSQL {version}: {len(values)} values/OIDs, {len(nulls)} SQL-NULL observations, "
          f"{len(metadata)} exact prepared descriptors")
    print(f"PASS: {len(expected_errors)} expected errors and {len(typmods)} exact native typmod integers")
    print("Scope: finite authored executions; interval input conversion remains a runtime obligation.")


if __name__ == "__main__":
    main()
