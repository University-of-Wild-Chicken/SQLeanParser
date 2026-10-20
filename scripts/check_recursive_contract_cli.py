#!/usr/bin/env python3
"""Recursive CTE certificates with independent, finite native observations.

Only the authored terminating examples execute. Downloaded statements receive
static certificates where supported and checked rendering; they never execute.
The separate recursive boundary suite only prepares and describes its inputs.
"""
import argparse
import hashlib
import json
import sqlite3

from check_advanced_cli import literal, question_parameters
from check_assurance_cli import assert_report, invoke
from check_join_contract_cli import bag, sqlite_bindings, validate_native
from check_locking_cli import copy_cell
from check_pagination_cli import ROOT, replay
from check_postgresql_cli import connection, copy_result, marker, parse_results, run, sql_identifier, sql_literal
from check_renderer_corpus import parameters
from generate_recursive_contract_examples import STATES, TABLES, population, all_cases, schema

FIXTURES = ROOT / "fixtures/recursive_contract"
SQL_TYPES = {"int": "INTEGER", "text": "TEXT"}
SOURCE_REGISTRY_SHA256 = "d87e149470535fe4aec010bf0c7e9f08fffd6beb9045f1ff4723056e68e4f281"


def source_registry():
    data = json.loads((FIXTURES / "source_contracts.json").read_text())
    assert hashlib.sha256(json.dumps(data, sort_keys=True, separators=(",", ":")).encode()).hexdigest() == SOURCE_REGISTRY_SHA256
    assert isinstance(data, list)
    assert len(data) == len({row["id"] for row in data}) == 21
    columns = [c for row in data for c in row["output_columns"]]
    assert len(columns) == 24
    assert all(type(c["nullable"]) is bool and c["nullable"] for c in columns)
    return {row["id"]: tuple((c["name"], c["type"], c["nullable"]) for c in row["output_columns"])
            for row in data}


def load_cases():
    rows = json.loads((FIXTURES / "synthetic.json").read_text())
    canonical_json = lambda value: json.dumps(value, sort_keys=True, separators=(",", ":"))
    assert canonical_json(rows) == canonical_json(all_cases())
    assert canonical_json(json.loads((FIXTURES / "schema.json").read_text())) == canonical_json(schema())
    sources = [json.loads(line) for line in (FIXTURES / "concrete.jsonl").read_text().splitlines()]
    for group in (rows, sources):
        assert len(group) == len({r["id"] for r in group}) == len({r["sql"] for r in group}) == 50
    for row in rows:
        assert row["source_kind"] == "synthetic"
        assert row["catalogFile"] == "fixtures/recursive_contract/schema.json"
        assert set(row["expected_rows_by_state"]) == set(row["sqlite_expected_rows_by_state"]) == set(STATES)
        assert parameters(row["sql"], "postgres") == parameters(row["sqlite_sql"], "sqlite")
        indexes = {index for _, index in parameters(row["sql"], "postgres")}
        assert indexes == set(range(1, len(row["parameter_values"]) + 1))
        assert len(row["parameter_types"].split(",")) == len(indexes) if indexes else not row["parameter_types"]
        for field in ("expected_rows_by_state", "sqlite_expected_rows_by_state"):
            assert all(len(values) == len(row["output_columns"])
                       for state_rows in row[field].values() for values in state_rows)
    registry = source_registry()
    assert set(registry) <= {r["id"] for r in sources}
    for row in sources:
        assert row["sql"] == row["raw_sql"] and row["transformations"] == []
        assert hashlib.sha256(row["sql"].encode()).hexdigest() == row["sql_sha256"]
        assert row["parameter_types"] is None
        if row["id"] in registry:
            assert row["observed_parameter_slots"] == []
    return rows, sources


def validity(row):
    args = ["--assurance", "contract", "--schema", str(FIXTURES / "schema.json")]
    if row["parameter_types"]:
        args += ["--param-types", row["parameter_types"]]
    output = tuple((c["name"], c["type"], c["nullable"]) for c in row["output_columns"])
    return assert_report([*args, row["sql"]], "valid", "contract", output)


def table_statements(postgres=True):
    return ["CREATE " + ("" if postgres else "TEMP ") + "TABLE " +
            ("public." if postgres else "") + sql_identifier(name) + " (" +
            ", ".join(sql_identifier(field) + " " + SQL_TYPES[type_] +
                      ("" if nullable else " NOT NULL") for field, type_, nullable in columns) + ");"
            for name, columns in TABLES.items()]


def capture(row, sql):
    assert row["source_kind"] == "synthetic", "native execution is restricted to authored fixtures"
    types = row["parameter_types"].replace("?", "")
    declaration = " (" + types + ")" if types else ""
    execute = "EXECUTE recursive_parameters"
    if row["parameter_values"]:
        execute += " (" + ", ".join(map(literal, row["parameter_values"])) + ")"
    signature = ", ".join(f"c{i} {col['postgres_type']}" for i, col in enumerate(row["output_columns"]))
    body = "BEGIN RETURN QUERY EXECUTE " + sql_literal(execute) + "; END;"
    return [
        "PREPARE recursive_parameters" + declaration + " AS " + question_parameters(sql).strip().removesuffix(";") + ";",
        "CREATE OR REPLACE FUNCTION pg_temp.recursive_rows() RETURNS TABLE (" + signature +
        ") LANGUAGE plpgsql VOLATILE AS " + sql_literal(body) + ";",
        copy_result("SELECT * FROM pg_temp.recursive_rows()"),
    ]


def postgres_script(rows, canonical):
    assert len(rows) == len(canonical), "missing PostgreSQL canonical query"
    commands = ["\\encoding UTF8", "BEGIN;", "SET LOCAL statement_timeout = '5s';",
                "SET LOCAL standard_conforming_strings = on;", *table_statements()]
    expected = {}
    for state in STATES:
        commands.append("TRUNCATE public.nodes,public.edges;")
        for name, values in population(state).items():
            if values:
                commands.append("INSERT INTO public." + sql_identifier(name) + " VALUES " +
                                ", ".join("(" + ", ".join(map(literal, row)) + ")" for row in values) + ";")
        for index, (row, rendered) in enumerate(zip(rows, canonical), 1):
            for form, sql in (("source", row["sql"]), ("postgres", rendered)):
                key = marker("recursive_" + state, index, state != "empty", form)
                parts = capture(row, sql)
                commands += ["SAVEPOINT recursive_case;", *parts[:-1], "\\echo " + key, parts[-1],
                             "DEALLOCATE recursive_parameters;", "ROLLBACK TO SAVEPOINT recursive_case;",
                             "RELEASE SAVEPOINT recursive_case;"]
                expected[key] = (len(row["output_columns"]),
                                 [[copy_cell(v) for v in values] for values in row["expected_rows_by_state"][state]])
    commands.append("ROLLBACK;")
    return "\n".join(commands), expected


def describe_script(rows, canonical):
    assert len(rows) == len(canonical), "missing canonical descriptor input"
    assert all(row["source_kind"] == "synthetic" for row in rows)
    commands = ["BEGIN;", "SET LOCAL statement_timeout = '5s';", *table_statements()]
    expected = []
    for row, rendered in zip(rows, canonical):
        types = row["parameter_types"].replace("?", "")
        declaration = " (" + types + ")" if types else ""
        values = "(" + ", ".join(map(literal, row["parameter_values"])) + ")" if row["parameter_values"] else ""
        for sql in (row["sql"], rendered):
            commands += ["PREPARE recursive_description" + declaration + " AS " +
                         question_parameters(sql).strip().removesuffix(";") + ";",
                         "EXECUTE recursive_description" + values, "\\gdesc", "DEALLOCATE recursive_description;"]
            expected += [c["name"] + "|" + c["postgres_display_type"] for c in row["output_columns"]]
    commands.append("ROLLBACK;")
    return "\n".join(commands), expected


def sqlite_render(row):
    if row["sqlite_mode"] in ("render_unsupported", "input_excluded"):
        result = invoke(["--render-assurance", "sqlite"], stdin=row["sqlite_sql"])
        report = json.loads(result.stdout)
        status = (1, "invalid") if row["sqlite_mode"] == "input_excluded" else (3, "unsupported")
        assert (result.returncode, report["status"], report["diagnostic"]["code"]) == (
            *status, row["sqlite_diagnostic"]), (row["id"], report)
        return None
    return replay("sqlite", row["sqlite_sql"])["sql"]


def sqlite_observations(rows, canonical):
    assert len(rows) == len(canonical), "missing SQLite canonical query"
    assert all(row["source_kind"] == "synthetic" for row in rows)
    assert sqlite3.sqlite_version_info >= (3, 39, 0)
    count = errors = 0
    with sqlite3.connect(":memory:") as database:
        database.set_progress_handler(lambda: 1, 1_000_000)
        for command in table_statements(False):
            database.execute(command)
        for state in STATES:
            for name, values in population(state).items():
                database.execute("DELETE FROM " + sql_identifier(name))
                slots = ",".join("?" for _ in TABLES[name])
                database.executemany("INSERT INTO " + sql_identifier(name) + " VALUES (" + slots + ")", values)
            for row, rendered in zip(rows, canonical):
                assert (rendered is None) == (row["sqlite_mode"] in ("render_unsupported", "input_excluded")), row["id"]
                if rendered is None:
                    continue
                for sql in (row["sqlite_sql"], rendered):
                    try:
                        cursor = database.execute(sql, sqlite_bindings(sql, row["parameter_values"]))
                        observed = cursor.fetchall()
                    except sqlite3.OperationalError as error:
                        assert row["sqlite_mode"] == "analysis_error" and row["sqlite_error"] == str(error), (
                            row["id"], sql, str(error))
                        errors += 1
                    else:
                        assert row["sqlite_mode"] == "execute", row["id"]
                        assert [c[0] for c in cursor.description] == row["sqlite_output_names"], (
                            row["id"], cursor.description)
                        assert bag(observed) == bag(row["sqlite_expected_rows_by_state"][state]), (
                            row["id"], state, sql, observed)
                        if row["ordered"]:
                            assert [list(v) for v in observed] == row["sqlite_expected_rows_by_state"][state], (
                                row["id"], state, "ordered", observed)
                        count += 1
    return count, errors


def validate_ordered(actual, rows):
    for state in STATES:
        for index, row in enumerate(rows, 1):
            if not row["ordered"]:
                continue
            expected = [[copy_cell(v) for v in values] for values in row["expected_rows_by_state"][state]]
            for form in ("source", "postgres"):
                key = marker("recursive_" + state, index, state != "empty", form)
                assert actual[key][1] == expected, (row["id"], state, form, actual[key][1], expected)


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    target = parser.add_mutually_exclusive_group(required=True)
    target.add_argument("--local-bin")
    target.add_argument("--dsn")
    parser.add_argument("--psql")
    args = parser.parse_args()
    rows, sources = load_cases()
    canonical, sqlite = [], []
    for row in rows:
        validity(row)
        replay("identity", row["sql"])
        canonical.append(replay("postgres", row["sql"])["sql"])
        sqlite.append(sqlite_render(row))
    registry = source_registry()
    for source in sources:
        if source["id"] in registry:
            assert_report(["--assurance", "contract", source["sql"]], "valid", "contract", registry[source["id"]])
        for mode in ("identity", "postgres"):
            replay(mode, source["sql"])
    sqlite_count, sqlite_errors = sqlite_observations(rows, sqlite)
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
    print(f"PASS: 50 authored + {len(registry)} fixed source static contracts; 50 unchanged source rendering pairs")
    print(f"PASS: PostgreSQL {version}: {len(values)} result comparisons, {len(descriptors)} exact descriptor positions")
    print(f"PASS: SQLite {sqlite3.sqlite_version}: {sqlite_count} result comparisons, "
          f"{sqlite_errors} registered analysis errors, {sum(s is None for s in sqlite)} input/render exclusions")
    print("Scope: finite observations of authored terminating fixtures; no universal termination or execution-equivalence claim.")


if __name__ == "__main__":
    main()
