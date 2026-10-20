#!/usr/bin/env python3
"""Ordinary CTE certificates and separate, finite native dialect observations."""
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
from generate_cte_contract_examples import STATES, TABLES, population, all_cases, schema

FIXTURES = ROOT / "fixtures/cte_contract"
SQL_TYPES = {"int": "INTEGER", "text": "TEXT"}


def source_registry():
    data = json.loads((FIXTURES / "source_contracts.json").read_text())
    # The complete source registry is authored independently of checker results.
    assert hashlib.sha256(json.dumps(data, sort_keys=True, separators=(",", ":")).encode()).hexdigest() == (
        "fc9a8a34c590c2988cf3dd5eb60c5cbdd7b59d85b480cc99a201c84db21e3fce")
    assert isinstance(data, list) and len(data) == 13
    assert len({row["id"] for row in data}) == 13
    columns = [c for row in data for c in row["output_columns"]]
    assert len(columns) == 21
    assert Counter(c["type"] for c in columns) == {"int32": 15, "text": 2, "bool": 4}
    assert all(type(c["nullable"]) is bool and not c["nullable"] for c in columns)
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
        assert row["catalogFile"] == "fixtures/cte_contract/schema.json"
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
    # Statuses describe this static contract. PREPARE and execution states are
    # separate native observations; planning restrictions can disappear when a
    # definition is unused. SQL here is authored, never scraped.
    cases = [
        ("WITH a AS (SELECT * FROM b), b AS (SELECT 1 AS x) SELECT * FROM a", "invalid", "42P01", "42P01"),
        ("WITH c AS (SELECT * FROM c) SELECT * FROM c", "invalid", "42P01", "42P01"),
        ("WITH c AS (SELECT 1), c AS (SELECT 2) SELECT * FROM c", "invalid", "42712", "42712"),
        ("WITH c(a,b) AS (SELECT 1) SELECT * FROM c", "invalid", "42P10", "42P10"),
        ("WITH c AS (SELECT 1 AS x,2 AS x) SELECT x FROM c", "invalid", "42702", "42702"),
        ("WITH c AS (SELECT 'x' AS x) SELECT x+1 FROM c", "invalid", "42883", "42883"),
        ("WITH unused AS (SELECT * FROM absent) SELECT 1", "invalid", "42P01", "42P01"),
        ("WITH c AS (SELECT 1 AS x) SELECT * FROM c FOR UPDATE OF c", "invalid", "0A000", "0A000"),
        ("WITH c AS (SELECT 1 AS x) SELECT * FROM c d FOR SHARE OF d", "invalid", "0A000", "0A000"),
        ("WITH c AS (SELECT 1 AS x) SELECT * FROM c WHERE x", "invalid", "42804", "42804"),
        ("WITH unused AS (SELECT 1 = TRUE AS x) SELECT 1", "invalid", "42883", "42883"),
        ("WITH unused AS (SELECT DISTINCT id FROM items FOR UPDATE) SELECT 1", "invalid", "0A000", "0A000"),
        ("WITH unused AS (SELECT r.id FROM items l LEFT JOIN labels r ON FALSE FOR UPDATE OF r) SELECT 1",
         "unsupported", "00000", "00000"),
        ("WITH c AS (SELECT r.id FROM items l LEFT JOIN labels r ON FALSE FOR UPDATE OF r) SELECT * FROM c",
         "unsupported", "00000", "0A000"),
        ("WITH RECURSIVE c AS (SELECT 1 AS x) SELECT x FROM c", "valid", "00000", "00000"),
        ("WITH c AS (SELECT COUNT(*) AS n FROM items) SELECT n FROM c", "unsupported", "00000", "00000"),
        ("WITH c AS (SELECT 1 AS x UNION ALL SELECT 2) SELECT x FROM c", "valid", "00000", "00000"),
        ("WITH c AS (SELECT (SELECT 1) AS x) SELECT x FROM c", "unsupported", "00000", "00000"),
        ("WITH c AS (SELECT 1 AS x) SELECT d.x FROM c CROSS JOIN LATERAL (SELECT c.x) d",
         "unsupported", "00000", "00000"),
        ("WITH c AS (SELECT 1 AS x) SELECT d.x FROM c CROSS JOIN (SELECT c.x) d",
         "invalid", "42P01", "42P01"),
        ("WITH unused AS (WITH inner_cte AS (SELECT 1 AS x) SELECT x FROM inner_cte) SELECT * FROM inner_cte",
         "invalid", "42P01", "42P01"),
        ("WITH c AS (SELECT id FROM items) SELECT items.id FROM c", "invalid", "42P01", "42P01"),
        ("WITH c AS (SELECT 1 AS x) SELECT c.x FROM c d", "invalid", "42P01", "42P01"),
        ("WITH c AS (SELECT 1 AS x) SELECT * FROM c a CROSS JOIN c a", "invalid", "42712", "42712"),
        ("WITH c AS (SELECT DISTINCT id FROM items) SELECT * FROM c FOR UPDATE", "valid", "00000", "00000"),
        ("WITH a AS (SELECT * FROM items), items AS (SELECT 99 AS id) SELECT * FROM a", "valid", "00000", "00000"),
        ("WITH c(x,x) AS (SELECT 1,2) SELECT * FROM c", "valid", "00000", "00000"),
        ("WITH c AS (SELECT 1 AS x) SELECT * FROM c a CROSS JOIN c b FOR UPDATE", "valid", "00000", "00000"),
    ]
    return [{"sql": sql, "status": status, "prepare_state": prepare, "execute_state": execute}
            for sql, status, prepare, execute in cases]


def boundaries():
    for row in boundary_cases():
        if row["sql"].startswith("WITH RECURSIVE"):
            assert_report(["--assurance", "contract", "--schema", str(FIXTURES / "schema.json"), row["sql"]],
                          row["status"], "contract", (("x", "int32", False),))
            continue
        assert_report(["--assurance", "contract", "--schema", str(FIXTURES / "schema.json"), row["sql"]],
                      row["status"], "contract")
    for sql in ("WITH unused AS (SELECT $1 AS x) SELECT 1",
                "WITH c AS (SELECT ? AS x) SELECT x FROM c"):
        assert_report(["--assurance", "contract", sql], "invalid", "contract")
    return len(boundary_cases()) + 2


def table_statements(postgres=True):
    return ["CREATE " + ("" if postgres else "TEMP ") + "TABLE " +
            ("public." if postgres else "") + sql_identifier(name) + " (" +
            ", ".join(sql_identifier(field) + " " + SQL_TYPES[type_] +
                      ("" if nullable else " NOT NULL") for field, type_, nullable in columns) + ");"
            for name, columns in TABLES.items()]


def capture(row, sql):
    types = row["parameter_types"].replace("?", "")
    declaration = " (" + types + ")" if types else ""
    execute = "EXECUTE cte_parameters"
    if row["parameter_values"]:
        execute += " (" + ", ".join(map(literal, row["parameter_values"])) + ")"
    signature = ", ".join(f"c{i} {col['postgres_type']}" for i, col in enumerate(row["output_columns"]))
    body = "BEGIN RETURN QUERY EXECUTE " + sql_literal(execute) + "; END;"
    return [
        "PREPARE cte_parameters" + declaration + " AS " + question_parameters(sql).strip().removesuffix(";") + ";",
        "CREATE OR REPLACE FUNCTION pg_temp.cte_rows() RETURNS TABLE (" + signature +
        ") LANGUAGE plpgsql VOLATILE AS " + sql_literal(body) + ";",
        copy_result("SELECT * FROM pg_temp.cte_rows()"),
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
                key = marker("cte_" + state, index, state != "empty", form)
                parts = capture(row, sql)
                commands += ["SAVEPOINT cte_case;", *parts[:-1], "\\echo " + key, parts[-1],
                             "DEALLOCATE cte_parameters;", "ROLLBACK TO SAVEPOINT cte_case;",
                             "RELEASE SAVEPOINT cte_case;"]
                expected[key] = (len(row["output_columns"]),
                                 [[copy_cell(v) for v in values] for values in row["expected_rows_by_state"][state]])
    commands.append("ROLLBACK;")
    return "\n".join(commands), expected


def describe_script(rows, canonical):
    assert len(rows) == len(canonical), "missing canonical descriptor input"
    commands = ["BEGIN;", *table_statements()]
    expected = []
    for row, rendered in zip(rows, canonical):
        types = row["parameter_types"].replace("?", "")
        declaration = " (" + types + ")" if types else ""
        values = "(" + ", ".join(map(literal, row["parameter_values"])) + ")" if row["parameter_values"] else ""
        for sql in (row["sql"], rendered):
            commands += ["PREPARE cte_description" + declaration + " AS " +
                         question_parameters(sql).strip().removesuffix(";") + ";",
                         "EXECUTE cte_description" + values, "\\gdesc", "DEALLOCATE cte_description;"]
            expected += [c["name"] + "|" + c["postgres_display_type"] for c in row["output_columns"]]
    commands.append("ROLLBACK;")
    return "\n".join(commands), expected


def analysis_script():
    commands = ["BEGIN;", "SET LOCAL statement_timeout = '5s';", *table_statements(),
                "CREATE FUNCTION pg_temp.cte_stage(q TEXT, execute_it BOOLEAN) RETURNS TEXT "
                "LANGUAGE plpgsql AS $$ DECLARE result TEXT; BEGIN EXECUTE 'PREPARE cte_probe AS ' || q; "
                "IF execute_it THEN EXECUTE 'EXECUTE cte_probe'; END IF; "
                "DEALLOCATE cte_probe; RETURN '00000'; "
                "EXCEPTION WHEN OTHERS THEN result := SQLSTATE; "
                "IF EXISTS (SELECT 1 FROM pg_prepared_statements WHERE name='cte_probe') THEN "
                "DEALLOCATE cte_probe; END IF; RETURN result; END $$;"]
    expected = []
    for row in boundary_cases():
        for stage in ("prepare", "execute"):
            commands.append("SELECT pg_temp.cte_stage(" + sql_literal(row["sql"]) + "," +
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
                    except sqlite3.OperationalError as error:
                        assert row["sqlite_mode"] == "analysis_error", (row["id"], str(error))
                        assert row["sqlite_error"] in str(error), (row["id"], str(error))
                        errors += 1
                    else:
                        assert row["sqlite_mode"] == "execute", row["id"]
                        assert [c[0] for c in cursor.description] == row["sqlite_output_names"], (
                            row["id"], cursor.description)
                        observed = cursor.fetchall()
                        assert bag(observed) == bag(row["sqlite_expected_rows_by_state"][state]), (
                            row["id"], state, sql, observed)
                        count += 1
    return count, errors


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
    static_count = boundaries()
    sqlite_count, sqlite_errors = sqlite_observations(rows, sqlite)
    values_sql, values = postgres_script(rows, canonical)
    descriptors_sql, descriptors = describe_script(rows, canonical)
    stages_sql, stages = analysis_script()
    with connection(args) as psql:
        result = run([*psql, "-X", "-q", "-v", "ON_ERROR_STOP=1"], input=values_sql, timeout=120)
        validate_native(parse_results(result.stdout), values)
        for script, expected in ((descriptors_sql, descriptors), (stages_sql, stages)):
            result = run([*psql, "-X", "-qAt", "-v", "ON_ERROR_STOP=1"], input=script, timeout=120)
            assert result.stdout.splitlines() == expected, (result.stdout.splitlines(), expected)
        version = run([*psql, "-X", "-At", "-c", "SHOW server_version;"]).stdout.strip()
    print(f"PASS: 50 authored and {len(registry)} fixed source certificates; 50 original source renderings")
    print(f"PASS: {static_count} static boundaries; PostgreSQL {version}: {len(values)} typed row observations, "
          f"{len(descriptors)} descriptor positions, {len(stages)} analysis/planning observations")
    print(f"PASS: SQLite {sqlite3.sqlite_version}: {sqlite_count} row/label observations, "
          f"{sqlite_errors} expected analysis errors, "
          f"{sum(row['sqlite_mode'] in ('render_unsupported', 'input_excluded') for row in rows)} input/render exclusions")
    print("Scope: authored statements execute in private databases; original source SQL is never executed.")


if __name__ == "__main__":
    main()
