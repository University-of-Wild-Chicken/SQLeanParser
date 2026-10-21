#!/usr/bin/env python3
"""Set-operation certificates and independent finite native dialect observations."""
import argparse
from collections import Counter
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
from generate_set_operation_examples import FACTORS, STATES, TABLES, population, all_cases, schema

FIXTURES = ROOT / "fixtures/set_operations"
SQL_TYPES = {"int": "INTEGER", "text": "TEXT"}


def source_registry():
    data = json.loads((FIXTURES / "source_contracts.json").read_text())
    assert hashlib.sha256(json.dumps(data, sort_keys=True, separators=(",", ":")).encode()).hexdigest() == SOURCE_REGISTRY_SHA256
    assert isinstance(data, dict) and set(data) == set(FACTORS)
    assert {factor: len(data[factor]) for factor in FACTORS} == {"union": 50, "intersect": 6, "except": 6}
    rows = [row for factor in FACTORS for row in data[factor]]
    assert len(rows) == len({row["id"] for row in rows}) == 62
    columns = [c for row in rows for c in row["output_columns"]]
    assert len(columns) == 83
    assert all(type(c["nullable"]) is bool for c in columns)
    return {row["id"]: tuple((c["name"], c["type"], c["nullable"]) for c in row["output_columns"])
            for row in rows}


SOURCE_REGISTRY_SHA256 = "cdcb59a9619748976cb6103fc02eacb9e855403ad4eb23c14e632db980579ec1"


def load_cases():
    rows = json.loads((FIXTURES / "synthetic.json").read_text())
    canonical_json = lambda value: json.dumps(value, sort_keys=True, separators=(",", ":"))
    assert canonical_json(rows) == canonical_json(all_cases())
    assert canonical_json(json.loads((FIXTURES / "schema.json").read_text())) == canonical_json(schema())
    sources = [json.loads(line) for line in (FIXTURES / "concrete.jsonl").read_text().splitlines()]
    for group in (rows, sources):
        assert len(group) == len({r["id"] for r in group}) == len({r["sql"] for r in group}) == 150
    for group in (rows, sources):
        assert Counter(r["factor"] for r in group) == {f: 50 for f in FACTORS}
    for row in rows:
        assert row["catalogFile"] == "fixtures/set_operations/schema.json"
        assert set(row["expected_rows_by_state"]) == set(row["sqlite_expected_rows_by_state"]) == set(STATES)
        assert parameters(row["sql"], "postgres") == parameters(row["sqlite_sql"], "sqlite")
        indexes = {index for _, index in parameters(row["sql"], "postgres")}
        assert indexes == set(range(1, len(row["parameter_values"]) + 1))
        for field in ("expected_rows_by_state", "sqlite_expected_rows_by_state"):
            assert all(len(values) == len(row["output_columns"])
                       for state_rows in row[field].values() for values in state_rows)
    registry = source_registry()
    assert all(type(r["observed_syntax"]["source_free"]) is bool for r in sources)
    assert set(registry) == {r["id"] for r in sources if r["observed_syntax"]["source_free"]}
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


def boundary_cases():
    result = []
    def add(factor, shape, sql, status, state, execution=None):
        result.append({"id": f"set-{factor}-{shape}", "sql": sql,
                       "status": status, "prepare_state": state,
                       "execute_state": state if execution is None else execution})
    for factor in FACTORS:
        op = factor.upper()
        for shape, left, right, state in (
            ("width", "SELECT 1", "SELECT 1,2", "42601"),
            ("boolean-integer", "SELECT TRUE", "SELECT 1", "42804"),
            ("text-integer", "SELECT CAST('1' AS TEXT)", "SELECT 1", "42804"),
            ("finalized-inner-null", "(SELECT NULL UNION SELECT NULL)", "SELECT 1", "42804"),
            ("distinct-finalizes", "SELECT DISTINCT NULL", "SELECT 1", "42804"),
            ("ordinal-finalizes", "(SELECT NULL ORDER BY 1)", "SELECT 1", "42804"),
            ("label-finalizes", "(SELECT NULL AS x ORDER BY x)", "SELECT 1", "42804"),
            ("cte-finalizes", "SELECT x FROM (WITH c AS (SELECT NULL AS x) SELECT x FROM c) d", "SELECT 1", "42804"),
            ("derived-finalizes", "SELECT x FROM (SELECT NULL AS x) d", "SELECT 1", "42804"),
            ("missing-column", "SELECT missing FROM items", "SELECT 1", "42703"),
            ("json-equality", "SELECT CAST('1' AS JSON)", "SELECT CAST('1' AS JSON)", "42883"),
            ("json-array-equality", "SELECT ARRAY[CAST('1' AS JSON)]", "SELECT ARRAY[CAST('1' AS JSON)]", "42883"),
        ):
            add(factor, shape, f"{left} {op} {right}", "invalid", state)
        for shape, suffix, state in (
            ("ordinal-zero", "0", "42P10"), ("ordinal-high", "2", "42P10"),
            ("ordinal-negative", "-1", "42P10"), ("noninteger", "1.2", "42601"),
            ("missing-label", "right_label", "42703"),
            ("qualified-label", "items.v", "42P01"),
            ("expression", "v+1", "0A000"), ("positive-operator", "+1", "0A000"),
            ("cast", "CAST(1 AS INTEGER)", "0A000"),
        ):
            add(factor, shape, f"SELECT 1 AS v {op} SELECT 2 AS right_label ORDER BY {suffix}", "invalid", state)
        add(factor, "duplicate-set-label", f"SELECT 1 AS x,1 AS x {op} SELECT 1,1 ORDER BY x", "invalid", "42702")
        add(factor, "set-lock", f"SELECT id FROM items {op} SELECT id FROM labels FOR UPDATE", "invalid", "0A000")
        add(factor, "left-arm-lock", f"(SELECT id FROM items FOR SHARE) {op} SELECT id FROM labels", "invalid", "0A000")
        add(factor, "right-arm-lock", f"SELECT id FROM items {op} (SELECT id FROM labels FOR KEY SHARE)", "invalid", "0A000")
        add(factor, "aggregation", f"SELECT COUNT(*) FROM items {op} SELECT CAST(1 AS BIGINT)", "unsupported", "00000")
        add(factor, "scalar-subquery", f"SELECT (SELECT 1) {op} SELECT 1", "valid", "00000")
        add(factor, "recursive", f"WITH RECURSIVE c AS (SELECT 1 AS x) SELECT x FROM c {op} SELECT 1", "valid", "00000")
        add(factor, "lateral", f"SELECT d.x FROM LATERAL (SELECT 1 AS x) d {op} SELECT 1", "unsupported", "00000")
        # Existing contracts certify type/coercion admissibility, not literal
        # input-function success (which PostgreSQL may check during analysis).
        add(factor, "unknown-string-conversion", f"SELECT 'bad' {op} SELECT 1", "valid", "22P02")
    return result


def boundaries():
    for row in boundary_cases():
        label = "x" if row["id"].endswith("-recursive") else "?column?"
        assert_report(["--assurance", "contract", "--schema", str(FIXTURES / "schema.json"), row["sql"]],
                      row["status"], "contract",
                      ((label, "int32", row["id"].endswith("-scalar-subquery")),) if row["status"] == "valid" else None)
    for sql in ("SELECT ? AS v UNION SELECT 1", "SELECT 1 INTERSECT SELECT $1"):
        assert_report(["--assurance", "contract", sql], "invalid", "contract")
    return len(boundary_cases()) + 2


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
    execute = "EXECUTE set_parameters"
    if row["parameter_values"]:
        execute += " (" + ", ".join(map(literal, row["parameter_values"])) + ")"
    signature = ", ".join(f"c{i} {col['postgres_type']}" for i, col in enumerate(row["output_columns"]))
    body = "BEGIN RETURN QUERY EXECUTE " + sql_literal(execute) + "; END;"
    return [
        "PREPARE set_parameters" + declaration + " AS " + question_parameters(sql).strip().removesuffix(";") + ";",
        "CREATE OR REPLACE FUNCTION pg_temp.set_rows() RETURNS TABLE (" + signature +
        ") LANGUAGE plpgsql VOLATILE AS " + sql_literal(body) + ";",
        copy_result("SELECT * FROM pg_temp.set_rows()"),
    ]


def postgres_script(rows, canonical):
    assert len(rows) == len(canonical), "missing PostgreSQL canonical query"
    commands = ["\\encoding UTF8", "BEGIN;", "SET LOCAL statement_timeout = '5s';",
                "SET LOCAL standard_conforming_strings = on;", *table_statements()]
    expected = {}
    for state in STATES:
        commands.append("TRUNCATE public.items,public.labels;")
        for name, values in population(state).items():
            if values:
                commands.append("INSERT INTO public." + sql_identifier(name) + " VALUES " +
                                ", ".join("(" + ", ".join(map(literal, row)) + ")" for row in values) + ";")
        for index, (row, rendered) in enumerate(zip(rows, canonical), 1):
            for form, sql in (("source", row["sql"]), ("postgres", rendered)):
                key = marker("set_" + state, index, state != "empty", form)
                parts = capture(row, sql)
                commands += ["SAVEPOINT set_case;", *parts[:-1], "\\echo " + key, parts[-1],
                             "DEALLOCATE set_parameters;", "ROLLBACK TO SAVEPOINT set_case;",
                             "RELEASE SAVEPOINT set_case;"]
                expected[key] = (len(row["output_columns"]),
                                 [[copy_cell(v) for v in values] for values in row["expected_rows_by_state"][state]])
    commands.append("ROLLBACK;")
    return "\n".join(commands), expected


def describe_script(rows, canonical):
    assert len(rows) == len(canonical), "missing canonical descriptor input"
    assert all(row["source_kind"] == "synthetic" for row in rows)
    commands = ["BEGIN;", *table_statements()]
    expected = []
    for row, rendered in zip(rows, canonical):
        types = row["parameter_types"].replace("?", "")
        declaration = " (" + types + ")" if types else ""
        values = "(" + ", ".join(map(literal, row["parameter_values"])) + ")" if row["parameter_values"] else ""
        for sql in (row["sql"], rendered):
            commands += ["PREPARE set_description" + declaration + " AS " +
                         question_parameters(sql).strip().removesuffix(";") + ";",
                         "EXECUTE set_description" + values, "\\gdesc", "DEALLOCATE set_description;"]
            expected += [c["name"] + "|" + c["postgres_display_type"] for c in row["output_columns"]]
    commands.append("ROLLBACK;")
    return "\n".join(commands), expected


def analysis_script(canonical=None):
    rows = boundary_cases()
    if canonical is not None:
        assert len(canonical) == len(rows), "missing canonical boundary input"
    commands = ["BEGIN;", "SET LOCAL statement_timeout = '5s';", *table_statements(),
                "CREATE FUNCTION pg_temp.set_stage(q TEXT, execute_it BOOLEAN) RETURNS TEXT "
                "LANGUAGE plpgsql AS $$ DECLARE result TEXT; BEGIN EXECUTE 'PREPARE set_probe AS ' || q; "
                "IF execute_it THEN EXECUTE 'EXECUTE set_probe'; END IF; "
                "DEALLOCATE set_probe; RETURN '00000'; "
                "EXCEPTION WHEN OTHERS THEN result := SQLSTATE; "
                "IF EXISTS (SELECT 1 FROM pg_prepared_statements WHERE name='set_probe') THEN "
                "DEALLOCATE set_probe; END IF; RETURN result; END $$;"]
    expected = []
    for index, row in enumerate(rows):
        for sql in ([row["sql"]] if canonical is None else [row["sql"], canonical[index]]):
            for stage in ("prepare", "execute"):
                commands.append("SELECT pg_temp.set_stage(" + sql_literal(sql) + "," +
                                ("TRUE" if stage == "execute" else "FALSE") + ");")
                expected.append(row[stage + "_state"])
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
                for form, sql in (("source", row["sqlite_sql"]), ("sqlite", rendered)):
                    try:
                        cursor = database.execute(sql, sqlite_bindings(sql, row["parameter_values"]))
                    except sqlite3.OperationalError as error:
                        assert form == "source" and row["sqlite_source_error"] == str(error), (row["id"], str(error))
                        errors += 1
                    else:
                        assert row["sqlite_mode"] == "execute", row["id"]
                        assert not (form == "source" and row["sqlite_source_error"]), row["id"]
                        assert [c[0] for c in cursor.description] == row["sqlite_output_names"], (
                            row["id"], cursor.description)
                        observed = cursor.fetchall()
                        assert bag(observed) == bag(row["sqlite_expected_rows_by_state"][state]), (
                            row["id"], state, sql, observed)
                        if row["ordered"]:
                            assert [list(v) for v in observed] == row["sqlite_expected_rows_by_state"][state], (
                                row["id"], state, "ordered", observed)
                        count += 1
    return count, errors


def validate_ordered(actual, rows):
    """Pagination/order fixtures compare sequence as well as bag multiplicity."""
    for state in STATES:
        for index, row in enumerate(rows, 1):
            if not row["ordered"]:
                continue
            expected = [[copy_cell(v) for v in values] for values in row["expected_rows_by_state"][state]]
            for form in ("source", "postgres"):
                key = marker("set_" + state, index, state != "empty", form)
                assert actual[key][1] == expected, (row["id"], state, form, actual[key][1], expected)


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    target = parser.add_mutually_exclusive_group(required=True)
    target.add_argument("--local-bin")
    target.add_argument("--dsn")
    parser.add_argument("--psql")
    parser.add_argument("--source-registry", action="store_true", help="require the fixed source registry (always enforced)")
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
    static_count = boundaries()
    boundary_canonical = []
    for boundary in boundary_cases():
        replay("identity", boundary["sql"])
        boundary_canonical.append(replay("postgres", boundary["sql"])["sql"])
    sqlite_count, sqlite_errors = sqlite_observations(rows, sqlite)
    values_sql, values = postgres_script(rows, canonical)
    descriptors_sql, descriptors = describe_script(rows, canonical)
    stages_sql, stages = analysis_script(boundary_canonical)
    with connection(args) as psql:
        result = run([*psql, "-X", "-q", "-v", "ON_ERROR_STOP=1"], input=values_sql, timeout=120)
        observations = parse_results(result.stdout)
        validate_native(observations, values)
        validate_ordered(observations, rows)
        for script, expected in ((descriptors_sql, descriptors), (stages_sql, stages)):
            result = run([*psql, "-X", "-qAt", "-v", "ON_ERROR_STOP=1"], input=script, timeout=120)
            assert result.stdout.splitlines() == expected, (result.stdout.splitlines(), expected)
        version = run([*psql, "-X", "-At", "-c", "SHOW server_version;"]).stdout.strip()
    print(f"PASS: 150 authored and {len(registry)} fixed source certificates; 150 original source renderings")
    print(f"PASS: {static_count} static boundaries; PostgreSQL {version}: {len(values)} typed row observations, "
          f"{len(descriptors)} descriptor positions, {len(stages)} analysis/planning observations")
    print(f"PASS: SQLite {sqlite3.sqlite_version}: {sqlite_count} row/label observations, "
          f"{sqlite_errors} expected analysis errors, "
          f"{sum(row['sqlite_mode'] in ('render_unsupported', 'input_excluded') for row in rows)} input/render exclusions")
    print("Scope: authored statements execute in private databases; original source SQL is never executed.")


if __name__ == "__main__":
    main()
