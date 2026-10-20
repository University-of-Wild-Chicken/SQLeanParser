#!/usr/bin/env python3
"""Check COLLATE certificates, rendering, and finite native observations.

Only authored terminating examples execute. Unchanged downloaded statements
receive explicit static classifications and checked rendering. PostgreSQL
collation identities are observed independently of the returned row values;
these observations do not assert locale ordering or execution equivalence.
"""
import argparse
import hashlib
import json

from check_advanced_cli import literal, question_parameters
from check_assurance_cli import assert_report, invoke
from check_join_contract_cli import validate_native
from check_locking_cli import copy_cell
from check_pagination_cli import ROOT, replay
from check_postgresql_cli import (
    connection, copy_result, marker, parse_results, run, sql_identifier, sql_literal,
)
from check_renderer_corpus import parameters
from collation_source_contracts import load_observed_source_contracts, load_source_contracts
from generate_collation_examples import STATES, all_cases, population, schema, sqlite_boundary

FIXTURES = ROOT / "fixtures/collations"
# regcollation prints quoted builtins and the visible custom object name.
NATIVE_COLLATIONS = {
    None: None, "default": '"default"', "C": '"C"', "POSIX": '"POSIX"',
    "custom:c_order": "c_order",
}


def source_registry(sources):
    records = load_source_contracts()
    assert [row["id"] for row in records] == [row["id"] for row in sources]
    assert len(records) == len({row["id"] for row in records}) == 50
    combined = {row["id"]: row for row in records}
    for row in load_observed_source_contracts():
        assert combined[row["id"]]["status"] == "deferred"
        combined[row["id"]] = row
    assert all(row["status"] == "valid" and row["eligibility"] == "checker" for row in combined.values())
    assert sum(len(row["output_columns"]) for row in combined.values()) == 71
    return combined


def load_cases():
    rows = json.loads((FIXTURES / "synthetic.json").read_text())
    normalize = lambda value: json.dumps(value, sort_keys=True, separators=(",", ":"))
    assert normalize(rows) == normalize(all_cases())
    assert normalize(json.loads((FIXTURES / "schema.json").read_text())) == normalize(schema())
    sources = [json.loads(line) for line in (FIXTURES / "concrete.jsonl").read_text().splitlines()]
    for group in (rows, sources):
        assert len(group) == len({row["id"] for row in group}) == len({row["sql"] for row in group}) == 50
    for row in rows:
        assert row["source_kind"] == "synthetic"
        assert row["catalogFile"] == "fixtures/collations/schema.json"
        assert set(row["expected_rows_by_state"]) == set(STATES)
        assert parameters(row["sql"], "postgres") == parameters(row["sqlite_sql"], "sqlite")
        slots = {index for _, index in parameters(row["sql"], "postgres")}
        assert slots == set(range(1, len(row["parameter_values"]) + 1))
        assert len(row["parameter_types"].split(",")) == len(slots) if slots else not row["parameter_types"]
        assert all(len(values) == len(row["output_columns"])
                   for state_rows in row["expected_rows_by_state"].values() for values in state_rows)
        assert all(column["collation"] in NATIVE_COLLATIONS for column in row["output_columns"])
        assert (row["sqlite_mode"], row["sqlite_diagnostic"]) == sqlite_boundary(row["shape"])
    for row in sources:
        assert row["sql"] == row["raw_sql"] and row["transformations"] == []
        assert hashlib.sha256(row["sql"].encode()).hexdigest() == row["sql_sha256"]
        assert row["parameter_types"] is None
    return rows, sources


def validity(row, *, sql=None, catalog=None):
    args = ["--assurance", "contract", "--schema", str(catalog or FIXTURES / "schema.json")]
    if row["parameter_types"]:
        args += ["--param-types", row["parameter_types"]]
    columns = tuple((c["name"], c["type"], c["nullable"]) for c in row["output_columns"])
    report = assert_report([*args, row["sql"] if sql is None else sql], "valid", "contract", columns)
    assert report.get("outputCollations") == [c["collation"] for c in row["output_columns"]], (
        row["id"], report.get("outputCollations"), row["output_columns"])
    return report


def sqlite_render(row):
    result = invoke(["--render-assurance", "sqlite"], stdin=row["sqlite_sql"])
    report = json.loads(result.stdout)
    assert row["sqlite_mode"] in ("parse_invalid", "render_unsupported")
    expected_exit, expected_status = ((1, "invalid") if row["sqlite_mode"] == "parse_invalid"
                                      else (3, "unsupported"))
    assert (result.returncode, report["status"], report["diagnostic"]["code"]) == (
        expected_exit, expected_status, row["sqlite_diagnostic"]), (row["id"], report)


def setup_statements():
    # This native snapshot is deliberately small and independent of imported
    # source declarations or the host's installed locale catalog.
    return [
        "CREATE SCHEMA fixture;",
        'CREATE COLLATION fixture.c_order FROM pg_catalog."C";',
        "SET LOCAL search_path=fixture,public,pg_catalog;",
        'CREATE TABLE public.words(value TEXT COLLATE "C" NOT NULL);',
        "CREATE TABLE public.labels(value TEXT NOT NULL);",
    ]


def capture(row, sql, *, metadata=False):
    assert row["source_kind"] == "synthetic", "native execution is restricted to authored fixtures"
    types = row["parameter_types"].replace("?", "")
    declaration = " (" + types + ")" if types else ""
    execute = "EXECUTE collation_parameters"
    if row["parameter_values"]:
        execute += " (" + ", ".join(map(literal, row["parameter_values"])) + ")"
    signature = ", ".join(f"c{i} " + ("TEXT" if metadata else col["postgres_type"])
                          for i, col in enumerate(row["output_columns"]))
    body = "BEGIN RETURN QUERY EXECUTE " + sql_literal(execute) + "; END;"
    return [
        "PREPARE collation_parameters" + declaration + " AS " +
        question_parameters(sql).strip().removesuffix(";") + ";",
        "CREATE OR REPLACE FUNCTION pg_temp.collation_rows() RETURNS TABLE (" + signature +
        ") LANGUAGE plpgsql VOLATILE AS " + sql_literal(body) + ";",
        copy_result("SELECT * FROM pg_temp.collation_rows()"),
    ]


def collation_query(row, sql):
    """Observe resolved collation even when the authored query returns no rows.

    LEFT JOIN supplies one typed NULL tuple when necessary. The nonstrict
    pg_collation_for getter reads resolved expression metadata. Noncollatable
    outputs are independently type-checked by PREPARE/gdesc and yield NULL here.
    Parameters remain bound through PREPARE; no view or literal substitution is
    used, and the original projection is preserved inside the derived table.
    """
    assert row["source_kind"] == "synthetic"
    names = ",".join(f"c{i}" for i in range(len(row["output_columns"])))
    getters = ",".join("NULL::TEXT" if col["collation"] is None else f"pg_collation_for(q.c{i})"
                       for i, col in enumerate(row["output_columns"]))
    return ("SELECT " + getters + " FROM (VALUES(0)) seed(dummy) LEFT JOIN (" +
            sql.strip().removesuffix(";") + ") q(" + names + ") ON TRUE LIMIT 1")


def postgres_script(rows, canonical):
    assert len(rows) == len(canonical), "missing PostgreSQL canonical query"
    assert all(row["source_kind"] == "synthetic" for row in rows)
    commands = ["\\encoding UTF8", "BEGIN;", "SET LOCAL statement_timeout = '5s';",
                "SET LOCAL standard_conforming_strings = on;", *setup_statements()]
    expected = {}
    for state in STATES:
        commands.append("TRUNCATE public.words,public.labels;")
        for table, values in population(state).items():
            if values:
                commands.append("INSERT INTO public." + sql_identifier(table) + " VALUES " +
                                ",".join("(" + ",".join(map(literal, values_)) + ")" for values_ in values) + ";")
        for index, (row, rendered) in enumerate(zip(rows, canonical), 1):
            for form, sql in (("source", row["sql"]), ("postgres", rendered)):
                metadata_rows = [[NATIVE_COLLATIONS[c["collation"]] for c in row["output_columns"]]]
                for kind, query, wanted in (
                    ("rows", sql, row["expected_rows_by_state"][state]),
                    ("collations", collation_query(row, sql), metadata_rows),
                ):
                    key = marker("collation_" + state + "_" + kind, index, state != "empty", form)
                    parts = capture(row, query, metadata=kind == "collations")
                    commands += ["SAVEPOINT collation_case;", *parts[:-1], "\\echo " + key, parts[-1],
                                 "DEALLOCATE collation_parameters;", "ROLLBACK TO SAVEPOINT collation_case;",
                                 "RELEASE SAVEPOINT collation_case;"]
                    expected[key] = (len(row["output_columns"]),
                                     [[copy_cell(v) for v in values] for values in wanted])
    commands.append("ROLLBACK;")
    return "\n".join(commands), expected


def describe_script(rows, canonical):
    assert len(rows) == len(canonical), "missing PostgreSQL canonical descriptor input"
    assert all(row["source_kind"] == "synthetic" for row in rows)
    commands = ["BEGIN;", "SET LOCAL statement_timeout = '5s';", *setup_statements()]
    expected = []
    for row, rendered in zip(rows, canonical):
        types = row["parameter_types"].replace("?", "")
        declaration = " (" + types + ")" if types else ""
        values = "(" + ", ".join(map(literal, row["parameter_values"])) + ")" if row["parameter_values"] else ""
        for sql in (row["sql"], rendered):
            commands += ["PREPARE collation_description" + declaration + " AS " +
                         question_parameters(sql).strip().removesuffix(";") + ";",
                         "EXECUTE collation_description" + values, "\\gdesc", "DEALLOCATE collation_description;"]
            expected += [c["name"] + "|" + c["postgres_display_type"] for c in row["output_columns"]]
    commands.append("ROLLBACK;")
    return "\n".join(commands), expected


def validate_ordered(actual, rows):
    for state in STATES:
        for index, row in enumerate(rows, 1):
            if row["ordered"]:
                expected = [[copy_cell(v) for v in values] for values in row["expected_rows_by_state"][state]]
                for form in ("source", "postgres"):
                    key = marker("collation_" + state + "_rows", index, state != "empty", form)
                    assert actual[key][1] == expected, (row["id"], state, form, actual[key][1], expected)


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    target = parser.add_mutually_exclusive_group(required=True)
    target.add_argument("--local-bin")
    target.add_argument("--dsn")
    parser.add_argument("--psql")
    args = parser.parse_args()
    rows, sources = load_cases()
    registry = source_registry(sources)
    canonical = []
    for row in rows:
        validity(row)
        replay("identity", row["sql"])
        sql = replay("postgres", row["sql"])["sql"]
        validity(row, sql=sql)
        canonical.append(sql)
        sqlite_render(row)
    for source in sources:
        registered = registry[source["id"]]
        if registered["status"] == "valid":
            assert source["observed_parameter_slots"] == []
            typed = {**source, "parameter_types": "", "output_columns": registered["output_columns"]}
            validity(typed, catalog=ROOT / registered["catalogFile"])
        for mode in ("identity", "postgres"):
            rendered = replay(mode, source["sql"])["sql"]
            if registered["status"] == "valid":
                validity(typed, sql=rendered, catalog=ROOT / registered["catalogFile"])
    values_sql, values = postgres_script(rows, canonical)
    descriptors_sql, descriptors = describe_script(rows, canonical)
    with connection(args) as psql:
        result = run([*psql, "-X", "-q", "-v", "ON_ERROR_STOP=1"], input=values_sql, timeout=120)
        observations = parse_results(result.stdout)
        validate_native(observations, values)
        validate_ordered(observations, rows)
        result = run([*psql, "-X", "-qAt", "-v", "ON_ERROR_STOP=1"], input=descriptors_sql, timeout=120)
        assert result.stdout.splitlines() == descriptors, (result.stdout.splitlines(), descriptors)
        version = run([*psql, "-X", "-At", "-c", "SHOW server_version;"]).stdout.strip()
    print("PASS: 50 authored static contracts with exact output collation identities in original and rendered SQL")
    print("PASS: 50 unchanged source contracts/rendering pairs: 18 declared contexts and 32 observed fixture contexts")
    print("PASS: 50 registered SQLite boundaries: 6 parse exclusions and 44 rendering exclusions "
          "(39 collation, 4 scalar-function signatures, 1 PostgreSQL type)")
    print(f"PASS: PostgreSQL {version}: {len(values) // 2} row comparisons, "
          f"{len(values) // 2} exact collation observations, {len(descriptors)} exact descriptor positions")
    print("Scope: authored finite observations and caller-declared catalog identities; no locale-evaluation theorem.")


if __name__ == "__main__":
    main()
