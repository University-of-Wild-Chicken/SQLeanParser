#!/usr/bin/env python3
"""Check relation identity, exact result descriptors and finite bound executions.

Only authored statements execute. Unchanged application sources receive
rendering certificates without invented schemas or parameter declarations.
"""
from __future__ import annotations

import argparse
import json
import subprocess
import uuid
from pathlib import Path

from check_advanced_cli import literal, question_parameters
from check_assurance_cli import assert_report
from check_join_contract_cli import validate_native
from check_locking_cli import PersistentPsql, copy_cell
from check_merged_join_cli import prepare_capture
from check_pagination_cli import EXE, replay
from check_postgresql_cli import connection, marker, parse_results, run, sql_identifier, sql_literal
from check_renderer_corpus import parameters
from generate_qualified_name_examples import DATA, TABLES

ROOT = Path(__file__).resolve().parents[1]
FIXTURES = ROOT / "fixtures/qualified_names"
SQL_TYPES = {"int": "INTEGER", "text": "TEXT", "bool": "BOOLEAN"}
DISPLAY_TYPES = {"int32": "integer", "text": "text", "bool": "boolean"}


def load_cases():
    cases = json.loads((FIXTURES / "synthetic.json").read_text())
    sources = [json.loads(line) for line in (FIXTURES / "concrete.jsonl").read_text().splitlines()]
    for population in (cases, sources):
        assert len(population) == len({c["id"] for c in population}) == len({c["sql"] for c in population}) == 50
    for case in cases:
        assert case["catalogFile"] == "fixtures/qualified_names/schema.json"
        slots = {index for _, index in parameters(case["sql"], "postgres")}
        assert parameters(case["sql"], "postgres") == parameters(case["sqlite_sql"], "sqlite")
        assert slots == set(range(1, len(case["parameter_values"]) + 1))
        assert len([t for t in case["parameter_types"].split(",") if t]) == len(slots)
        assert all(len(row) == len(case["output_columns"]) for row in case["expected_rows"])
        assert all(type(c["nullable"]) is bool for c in case["output_columns"])
    return cases, sources


def validity(case):
    args = ["--assurance", "contract", "--schema", str(FIXTURES / "schema.json")]
    if case["parameter_types"]:
        args += ["--param-types", case["parameter_types"]]
    columns = tuple((c["name"], c["type"], c["nullable"]) for c in case["output_columns"])
    return assert_report([*args, case["sql"]], "valid", "contract", columns)


def sqlite_rejection(sql):
    result = subprocess.run([str(EXE), "--render-assurance", "sqlite"], input=sql,
                            cwd=ROOT, capture_output=True, text=True, timeout=30)
    report = json.loads(result.stdout)
    code = report.get("diagnostic", {}).get("code")
    parse_reason = (
        "SQLite does not support row-locking clauses" if "FOR UPDATE" in sql else
        "SQL-standard SUBSTRING syntax is not supported by the SQLite profile" if "SUBSTRING(" in sql else
        "reserved identifier key" if "AS u(key" in sql else None)
    if parse_reason is not None:
        # Existing SQLite input restrictions precede the new namespace boundary.
        assert result.returncode == 1 and report["status"] == "invalid" and code == "input.parse", report
        assert parse_reason in report["diagnostic"]["message"], report
    else:
        assert result.returncode == 3 and report["status"] == "unsupported", report
        assert code == "coverage.sqlite.schema-qualification", report
    assert report["evidence"] == "none", report
    assert not ({"sql", "parameterMap", "theorems"} & report.keys()), report


# Native PREPARE/EXPLAIN results are pinned separately from the classification.
# Missing qualified columns can invoke function-on-whole-row notation instead.
BOUNDARIES = [
    ("SELECT users.name FROM qa.users CROSS JOIN qb.users", "invalid", "42P09"),
    ("SELECT users.* FROM qa.users CROSS JOIN qb.users", "invalid", "42P09"),
    ("SELECT qa.users.id FROM qa.users u", "invalid", "42P01"),
    ("SELECT qa.users.id FROM qa.users AS users", "invalid", "42P01"),
    ("SELECT users.id FROM qa.users u", "invalid", "42P01"),
    ("SELECT qa.users.id FROM qa.users CROSS JOIN qa.users", "invalid", "42712"),
    ("SELECT qa.users.id FROM users CROSS JOIN qa.users", "invalid", "42712"),
    ("SELECT u.id FROM qa.users u CROSS JOIN qb.users u", "invalid", "42712"),
    ("SELECT qa.users.id FROM qa.users RIGHT JOIN qb.users ON qa.users.id = qb.users.id FOR UPDATE OF users",
     "invalid", "0A000"),
    ("SELECT qa.users.id FROM qa.users FOR UPDATE OF absent", "invalid", "42P01"),
    ("SELECT missing.users.id FROM qa.users", "invalid", "42P01"),
    ("SELECT qa.users.absent FROM qa.users", "unsupported", "42703"),
    ("SELECT qa.users.to_json FROM qa.users", "unsupported", "00000"),
    ("SELECT users.to_json FROM qa.users", "unsupported", "00000"),
    ("SELECT users FROM qa.users", "unsupported", "00000"),
    ("SELECT ctid FROM qa.users", "unsupported", "00000"),
    ("SELECT xmin FROM qa.users", "unsupported", "00000"),
    ("SELECT xmax FROM qa.users", "unsupported", "00000"),
    ("SELECT cmin FROM qa.users", "unsupported", "00000"),
    ("SELECT cmax FROM qa.users", "unsupported", "00000"),
    ("SELECT tableoid FROM qa.users", "unsupported", "00000"),
    ("SELECT ctid FROM qa.users, (SELECT 1 AS ctid) d", "unsupported", "42702"),
    ("SELECT ctid FROM qa.users CROSS JOIN (SELECT 1 AS ctid) d", "unsupported", "00000"),
    ("SELECT d.absent FROM (SELECT qa.users.id FROM qa.users) d", "unsupported", "42703"),
    ("SELECT d.id FROM (SELECT qa.users.id AS id, qa.users.id AS id FROM qa.users) d", "invalid", "42702"),
]


def boundaries():
    for sql, status, _ in BOUNDARIES:
        assert_report(["--assurance", "contract", "--schema", str(FIXTURES / "schema.json"), sql],
                      status, "contract")
    return len(BOUNDARIES)


def qualified_name(identity):
    return ".".join(map(sql_identifier, identity))


def setup():
    commands = ["\\encoding UTF8", "BEGIN;", "SET LOCAL statement_timeout = '5s';",
                "SET LOCAL standard_conforming_strings = on;"]
    commands += ["CREATE SCHEMA " + sql_identifier(name) + ";" for name in dict.fromkeys(k[0] for k in TABLES)]
    commands += ["SET LOCAL search_path = qa, qb, public;"]
    for identity, columns in TABLES.items():
        commands.append("CREATE TABLE " + qualified_name(identity) + " (" +
                        ", ".join(sql_identifier(name) + " " + SQL_TYPES[kind] +
                                  ("" if nullable else " NOT NULL") for name, kind, nullable in columns) + ");")
    return commands


def insert_statements():
    return ["INSERT INTO " + qualified_name(identity) + " VALUES " +
            ", ".join("(" + ", ".join(map(literal, row)) + ")" for row in rows) + ";"
            for identity, rows in DATA.items()]


def postgres_script(cases, canonical):
    assert len(cases) == len(canonical), "missing canonical qualified-name case"
    commands, expected = setup(), {}
    for populated in (False, True):
        if populated:
            commands += insert_statements()
        for index, (case, rendered) in enumerate(zip(cases, canonical), 1):
            for form, sql in (("source", case["sql"]), ("postgres", rendered)):
                capture = prepare_capture(case, sql)
                key = marker("qualified_names", index, populated, form)
                commands += ["SAVEPOINT qualified_case;", *capture[:-1], "\\echo " + key, capture[-1],
                             "DEALLOCATE merged_parameters;", "ROLLBACK TO SAVEPOINT qualified_case;",
                             "RELEASE SAVEPOINT qualified_case;"]
                rows = case["expected_rows"] if populated else []
                expected[key] = (len(case["output_columns"]), [[copy_cell(v) for v in row] for row in rows])
    commands.append("ROLLBACK;")
    return "\n".join(commands), expected


def describe_script(cases, canonical):
    """Observe original ordered labels and OIDs; duplicate labels stay intact."""
    assert len(cases) == len(canonical), "missing canonical qualified-name description"
    commands, expected = setup(), []
    for case, rendered in zip(cases, canonical):
        types = case["parameter_types"].replace("?", "")
        declaration = " (" + types + ")" if types else ""
        values = "(" + ", ".join(map(literal, case["parameter_values"])) + ")" if case["parameter_values"] else ""
        for sql in (case["sql"], rendered):
            commands += [
                "PREPARE qualified_description" + declaration + " AS " +
                question_parameters(sql).strip().removesuffix(";") + ";",
                "EXECUTE qualified_description" + values, "\\gdesc",
                "DEALLOCATE qualified_description;",
            ]
            expected += [c["name"] + "|" + DISPLAY_TYPES[c["type"]] for c in case["output_columns"]]
    commands.append("ROLLBACK;")
    return "\n".join(commands), expected


def boundary_script():
    commands = setup()
    body = ("BEGIN EXECUTE 'PREPARE qualified_boundary AS ' || query; "
            "EXECUTE 'EXPLAIN EXECUTE qualified_boundary'; "
            "DEALLOCATE qualified_boundary; RETURN '00000'; "
            "EXCEPTION WHEN OTHERS THEN "
            "IF EXISTS (SELECT 1 FROM pg_prepared_statements WHERE name = 'qualified_boundary') THEN "
            "DEALLOCATE qualified_boundary; END IF; RETURN SQLSTATE; END;")
    commands.append("CREATE FUNCTION pg_temp.qualified_analysis(query TEXT) RETURNS TEXT LANGUAGE plpgsql AS " +
                    sql_literal(body) + ";")
    commands += ["SELECT pg_temp.qualified_analysis(" + sql_literal(sql) + ");" for sql, _, _ in BOUNDARIES]
    commands.append("ROLLBACK;")
    return "\n".join(commands), [state for _, _, state in BOUNDARIES]


def visibility_script():
    """Check that the authored catalog's exposure is faithful to this session."""
    catalog = json.loads((FIXTURES / "schema.json").read_text())
    commands, expected = setup(), []
    for table in catalog["tables"]:
        identity = (table["schema"], table["name"])
        commands.append("SELECT pg_table_is_visible(" + sql_literal(qualified_name(identity)) + "::regclass);")
        expected.append("t" if table["exposeUnqualified"] else "f")
    commands.append("ROLLBACK;")
    return "\n".join(commands), expected


def first_lock_observations(psql):
    """Two sessions distinguish which same-basename range entry OF selects."""
    prefix = "sqlean_names_" + uuid.uuid4().hex
    schemas = [prefix + "_a", prefix + "_b"]
    tables = [qualified_name((s, "users")) for s in schemas]
    setup_sql = []
    for namespace, table in zip(schemas, tables):
        setup_sql += ["CREATE SCHEMA " + sql_identifier(namespace) + ";",
                      "CREATE TABLE " + table + "(id INTEGER NOT NULL);",
                      "INSERT INTO " + table + " VALUES(1);"]
    # Atomic setup ensures cleanup never acts on a partially claimed namespace.
    run([*psql, "-X", "-q", "-v", "ON_ERROR_STOP=1"], input="BEGIN;\n" + "\n".join(setup_sql) + "\nCOMMIT;")
    owner = None
    count = 0
    try:
        owner = PersistentPsql(psql)
        for first, second in (tables, list(reversed(tables))):
            sql = f"SELECT {first}.id FROM {first} JOIN {second} ON {first}.id = {second}.id FOR UPDATE OF users"
            for query in (sql, replay("postgres", sql)["sql"]):
                assert owner.command("BEGIN; " + query.strip().removesuffix(";") + ";") == ["1"]
                for table, wanted in ((first, "55P03"), (second, "00000")):
                    body = ("BEGIN PERFORM id FROM " + table + " FOR UPDATE NOWAIT; RETURN '00000'; "
                            "EXCEPTION WHEN OTHERS THEN RETURN SQLSTATE; END;")
                    commands = ["BEGIN;", "SET LOCAL statement_timeout = '2s';",
                                "CREATE FUNCTION pg_temp.probe() RETURNS TEXT LANGUAGE plpgsql AS " + sql_literal(body) + ";",
                                "SELECT pg_temp.probe();", "ROLLBACK;"]
                    observed = run([*psql, "-X", "-qAt", "-v", "ON_ERROR_STOP=1"],
                                   input="\n".join(commands), timeout=10).stdout.splitlines()
                    assert observed == [wanted], (query, table, observed, wanted)
                    count += 1
                assert owner.command("ROLLBACK;") == []
    finally:
        if owner is not None:
            owner.close()
        run([*psql, "-X", "-q", "-v", "ON_ERROR_STOP=1"],
            input="\n".join("DROP SCHEMA " + sql_identifier(s) + " CASCADE;" for s in schemas), timeout=10)
    return count


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    target = parser.add_mutually_exclusive_group(required=True)
    target.add_argument("--local-bin")
    target.add_argument("--dsn")
    parser.add_argument("--psql")
    args = parser.parse_args()
    cases, sources = load_cases()
    canonical = []
    for case in cases:
        validity(case)
        replay("identity", case["sql"])
        canonical.append(replay("postgres", case["sql"])["sql"])
        sqlite_rejection(case["sqlite_sql"])
    for case in sources:
        for mode in ("identity", "postgres"):
            replay(mode, case["sql"])
    boundary_count = boundaries()
    script, expected = postgres_script(cases, canonical)
    with connection(args) as psql:
        output = run([*psql, "-X", "-q", "-v", "ON_ERROR_STOP=1"], input=script, timeout=120).stdout
        validate_native(parse_results(output), expected)
        description, columns = describe_script(cases, canonical)
        output = run([*psql, "-X", "-qAt", "-v", "ON_ERROR_STOP=1"], input=description, timeout=120).stdout.splitlines()
        assert output == columns, (output, columns)
        probe, states = boundary_script()
        output = run([*psql, "-X", "-qAt", "-v", "ON_ERROR_STOP=1"], input=probe).stdout.splitlines()
        assert output == states, (output, states)
        probe, exposed = visibility_script()
        output = run([*psql, "-X", "-qAt", "-v", "ON_ERROR_STOP=1"], input=probe).stdout.splitlines()
        assert output == exposed, (output, exposed)
        locks = first_lock_observations(psql)
        version = run([*psql, "-X", "-At", "-c", "SHOW server_version;"]).stdout.strip()
    print("PASS: 50 qualified-name full-query certificates; 50 unchanged source rendering examples; 50 SQLite exclusions")
    print(f"PASS: PostgreSQL {version}: {len(expected)} bound row observations, {len(columns)} ordered column descriptors, "
          f"{boundary_count} analysis boundaries, {len(exposed)} namespace visibility checks, "
          f"{locks} two-session first-target observations")
    print("Scope: caller-declared namespace visibility and finite authored executions; source SQL is never executed.")


if __name__ == "__main__":
    main()
