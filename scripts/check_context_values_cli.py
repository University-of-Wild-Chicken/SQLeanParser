#!/usr/bin/env python3
"""Verify context/NAME certificates and finite authored PostgreSQL observations."""
import argparse
import json

from check_advanced_cli import question_parameters
from check_array_types_cli import describe_script, validate_results, validity
from check_assurance_cli import assert_report, invoke
from check_extended_types_cli import database_script
from check_json_containment_cli import error_script
from check_json_extraction_cli import null_script
from check_pagination_cli import ROOT, replay
from check_postgresql_cli import connection, parse_results, run, sql_literal
from check_renderer_corpus import parameters

FIXTURES = ROOT / "fixtures/context_values"


def source_registry():
    """Independently reviewed identities and ordered results, before checking."""
    pg = "context_values:postgres:src/test/regress/sql/"
    duck = "context_values:duckdb:test/sql/pg_catalog/system_functions.test:sqllogic-query-"
    result = {
        pg + "expressions.sql:statement-12": (("?column?", "bool", False),),
        pg + "expressions.sql:statement-13": (("current_schema", "name", True),),
        pg + "guc.sql:statement-156": (("?column?", "bool", False),),
        pg + "privileges.sql:statement-150": (("session_user", "name", False), ("current_user", "name", False)),
        pg + "temp.sql:statement-160": (("is_temp_schema", "bool", True),),
        "context_values:materialize:test/sqllogictest/current_database.slt:sqllogic-query-12":
            (("current_database", "name", False),),
        "context_values:materialize:test/sqllogictest/schemas.slt:sqllogic-query-41":
            (("current_schema", "name", True),),
        "context_values:pgweb:pkg/client/client.go:go-string-15103":
            (("current_user", "name", False), ("current_database", "name", False)),
        "context_values:river:riverdriver/riverpgxv5/river_pgx_v5_driver.go:go-string-44649":
            (("coalesce", "name", False),),
    }
    result.update({duck + str(index): ((label, "name", False),)
                   for index, label in ((6, "current_user"), (11, "current_catalog"),
                                        (26, "user"), (31, "session_user"))})
    assert len(result) == 13 and sum(map(len, result.values())) == 15
    return result


def unsupported_source_free():
    prefix = "context_values:postgres:src/test/regress/sql/privileges.sql:statement-"
    return {prefix + str(index) for index in (100, 116, 696, 709, 710, 721, 722)} | {
        "context_values:pgweb:pkg/statements/sql/info.sql:whole-file",
        "context_values:pgweb:pkg/statements/sql/info_simple.sql:whole-file",
    }


def load_cases():
    rows = json.loads((FIXTURES / "synthetic.json").read_text())
    sources = [json.loads(line) for line in (FIXTURES / "concrete.jsonl").read_text().splitlines()]
    for population in (rows, sources):
        assert len(population) == len({r["id"] for r in population}) == len({r["sql"] for r in population}) == 50
    expected_columns = (
        [("name", True)] * 4 + [("bool", False)] * 6
        + [("name[]", False), ("bool", False), ("name[]", True), ("name[]", False),
           ("bool", False), ("name[]", True), ("name", False), ("name", False),
           ("text", False), ("name", True), ("text", True), ("text", True),
           ("varchar(3)", True), ("char(12)", True), ("name", False), ("name", False),
           ("name", True)]
        + [("bool", True)] * 16
        + [("int32", True), ("int32", False), ("name[]", False), ("bool", False),
           ("bool", True), ("name", True), ("name", True)])
    assert len(expected_columns) == 50
    oid_names = {"bool": "boolean", "int32": "integer",
                 "varchar(3)": "character varying", "char(12)": "character"}
    modifier_names = {"varchar(3)": "character varying(3)", "char(12)": "character(12)"}
    for index, (row, (type_, nullable)) in enumerate(zip(rows, expected_columns), 1):
        assert row["source_kind"] == "synthetic" and row["search_path"] == "pg_catalog"
        assert row["id"].startswith(f"context-values-{index:02}-")
        assert row["output_columns"] == [{"name": "v", "type": type_, "nullable": nullable}]
        assert type(row["output_columns"][0]["nullable"]) is bool
        assert row["postgres_type"] == oid_names.get(type_, type_)
        assert row["postgres_display_type"] == modifier_names.get(type_, oid_names.get(type_, type_))
        assert row["expected_value"] is None or type(row["expected_value"]) is str
        assert type(row["expected_sql_null"]) is bool
        assert row["expected_sql_null"] == (index in {13, 16, 49})
        assert row["expected_sql_null"] == (row["expected_value"] is None)
        if type_ == "bool":
            assert row["expected_value"] in {"true", "false"}
        assert not row["expected_sql_null"] or row["output_columns"][0]["nullable"]
        assert row["sqlite_supported"] is False
        assert row["sqlite_input"] == row["sql"].replace("$", "?")
        uses = parameters(row["sql"], "postgres")
        assert {slot for _, slot in uses} == set(range(1, len(row["parameter_values"]) + 1))
        assert len([t for t in row["parameter_types"].split(",") if t]) == len(row["parameter_values"])
        assert question_parameters(row["sql"]) == row["postgres_input"]
    assert all(type(r["observed_syntax"]["source_free"]) is bool for r in sources)
    assert {r["id"] for r in sources if r["observed_syntax"]["source_free"]} == (
        source_registry().keys() | unsupported_source_free())
    assert not (source_registry().keys() & unsupported_source_free())
    return rows, sources


def controlled_path(script):
    """Set the authored environment, retaining each helper's rollback boundary."""
    assert script.count("BEGIN;") == 1 and script.endswith("ROLLBACK;")
    return script.replace("BEGIN;", "BEGIN;\nSET LOCAL search_path=pg_catalog;", 1)


def sqlite_expectation(case):
    """Register the specific boundary reached by each authored fixture."""
    index = int(case["id"].split("-")[2])
    groups = {
        "context-value": {1, 5, 6, 7, 8, 9, 10, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26,
                          28, 29, 30, 31, 32, 33, 34, 35, 36, 37, 38, 49},
        "scalar-function-signatures": {2, 3, 4, 11, 13, 14, 16, 44, 45},
        "input.parse": {12, 15, 40, 41, 42, 43, 46, 47, 48, 50},
        "PostgreSQL-type": {27}, "ILIKE": {39},
    }
    assert sum(map(len, groups.values())) == 50 and set.union(*groups.values()) == set(range(1, 51))
    selected = [key for key, indexes in groups.items() if index in indexes]
    assert len(selected) == 1
    code = selected[0]
    return (1, "invalid", code) if code == "input.parse" else (3, "unsupported", "coverage.sqlite." + code)


def reject_sqlite(case):
    result = invoke(["--render-assurance", "sqlite"], stdin=case["sqlite_input"])
    report = json.loads(result.stdout)
    assert (result.returncode, report["status"], report["diagnostic"]["code"]) == sqlite_expectation(case), report
    assert report["evidence"] == "none" and not ({"sql", "parameterMap", "theorems"} & report.keys()), report


def catalog_script():
    functions = json.loads((FIXTURES / "function_signatures.json").read_text())
    operators = json.loads((FIXTURES / "operator_signatures.json").read_text())
    casts = json.loads((FIXTURES / "cast_signatures.json").read_text())
    assert len(functions) == 6 and len(operators) == 26 and len(casts) == 6
    assert all(set(r) == {"name", "inputs", "output"} and type(r["inputs"]) is list
               and all(type(t) is str for t in r["inputs"]) for r in functions)
    assert {(r["name"], tuple(r["inputs"]), r["output"]) for r in functions} == {
        ("current_schema", (), "name"), ("current_database", (), "name"),
        ("current_schemas", ("boolean",), "name[]"), ("current_user", (), "name"),
        ("session_user", (), "name"), ("system_user", (), "text"),
    }
    assert all(set(r) == {"operator", "left", "right", "output", "function"} for r in operators)
    expected_operators = {
        (symbol, left, right, "boolean", function)
        for symbol, stem in (("=", "eq"), ("<>", "ne"), ("<", "lt"),
                             ("<=", "le"), (">", "gt"), (">=", "ge"))
        for left, right, function in (
            ("name", "name", "name" + stem), ("name", "text", "name" + stem + "text"),
            ("text", "name", "text" + stem + "name"))
    } | {(
        symbol, "name", "text", "boolean", function
    ) for symbol, function in (
        ("~~", "namelike"), ("!~~", "namenlike"), ("~~*", "nameiclike"), ("!~~*", "nameicnlike"),
        ("~", "nameregexeq"), ("!~", "nameregexne"), ("~*", "nameicregexeq"), ("!~*", "nameicregexne"))}
    assert {tuple(r[key] for key in ("operator", "left", "right", "output", "function"))
            for r in operators} == expected_operators
    assert all(set(r) == {"source", "target", "context", "function"} for r in casts)
    assert {tuple(r[key] for key in ("source", "target", "context", "function"))
            for r in casts} == {
        ("name", "text", "implicit", "text"), ("name", "character", "assignment", "bpchar"),
        ("name", "character varying", "assignment", "varchar"),
        ("text", "name", "implicit", "name"), ("character", "name", "implicit", "name"),
        ("character varying", "name", "implicit", "name"),
    }
    checks = []
    for row in [*functions, {"name": "length", "inputs": ["bytea", "name"], "output": "integer"}]:
        inputs = row["inputs"]
        signature = ",".join(inputs)
        checks.append(
            "EXISTS(SELECT FROM pg_catalog.pg_proc p WHERE "
            f"p.oid={sql_literal(row['name'] + '(' + signature + ')')}::regprocedure "
            f"AND p.proname={sql_literal(row['name'])} AND p.pronamespace='pg_catalog'::regnamespace "
            f"AND p.pronargs={len(inputs)} AND p.prorettype={sql_literal(row['output'])}::regtype "
            "AND p.proisstrict AND NOT p.proretset AND p.provariadic=0 AND p.pronargdefaults=0 "
            "AND p.provolatile='s' "
            "AND p.prokind='f')")
    strategies = {"<": 1, "<=": 2, "=": 3, "<>": 3, ">=": 4, ">": 5}
    for row in operators:
        op, left, right, output, function = (sql_literal(row[k]) for k in
                                           ("operator", "left", "right", "output", "function"))
        predicate = (
            "o.oprnamespace='pg_catalog'::regnamespace "
            f"AND o.oprname={op} AND o.oprleft={left}::regtype AND o.oprright={right}::regtype "
            f"AND o.oprresult={output}::regtype AND p.proname={function} "
            "AND p.pronamespace='pg_catalog'::regnamespace AND p.proisstrict "
            "AND NOT p.proretset AND p.pronargs=2 AND p.provariadic=0 AND p.prokind='f'")
        checks.append("EXISTS(SELECT FROM pg_catalog.pg_operator o JOIN pg_catalog.pg_proc p "
                      "ON p.oid=o.oprcode WHERE " + predicate + ")")
        if row["operator"] in strategies:
            target = "o.oprnegate" if row["operator"] == "<>" else "o.oid"
            checks.append(
                "EXISTS(SELECT FROM pg_catalog.pg_operator o JOIN pg_catalog.pg_proc p ON p.oid=o.oprcode "
                f"JOIN pg_catalog.pg_amop a ON a.amopopr={target} "
                "JOIN pg_catalog.pg_am m ON m.oid=a.amopmethod WHERE "
                + predicate + f" AND m.amname='btree' AND a.amopstrategy={strategies[row['operator']]} "
                f"AND a.amoplefttype={left}::regtype AND a.amoprighttype={right}::regtype)")
    for row in casts:
        checks.append(
            "EXISTS(SELECT FROM pg_catalog.pg_cast c JOIN pg_catalog.pg_proc p ON p.oid=c.castfunc "
            f"WHERE c.castsource={sql_literal(row['source'])}::regtype "
            f"AND c.casttarget={sql_literal(row['target'])}::regtype "
            f"AND c.castcontext={sql_literal({'implicit': 'i', 'assignment': 'a'}[row['context']])} "
            f"AND c.castmethod='f' AND p.proname={sql_literal(row['function'])} "
            "AND p.pronamespace='pg_catalog'::regnamespace)")
    checks.append(
        "EXISTS(SELECT FROM pg_catalog.pg_type t JOIN pg_catalog.pg_type a ON a.oid=t.typarray "
        "WHERE t.oid='name'::regtype AND t.typlen=64 AND NOT t.typbyval AND t.typcategory='S' "
        "AND NOT t.typispreferred AND t.typcollation='\"C\"'::regcollation "
        "AND a.oid='name[]'::regtype AND a.typelem=t.oid AND a.typlen=-1 AND a.typdelim=',')")
    return "\n".join(f"SELECT {index}, {condition};" for index, condition in enumerate(checks)), [
        f"{index}|t" for index in range(len(checks))]


def label_cases():
    cases = [
        (word, word.lower(), "text" if word == "SYSTEM_USER" else "name",
         word in ("CURRENT_SCHEMA", "SYSTEM_USER"))
        for word in ("CURRENT_SCHEMA", "CURRENT_CATALOG", "CURRENT_USER", "USER",
                     "CURRENT_ROLE", "SESSION_USER", "SYSTEM_USER")
    ] + [
        ("current_schema()", "current_schema", "name", True),
        ("current_database()", "current_database", "name", False),
        ("current_schemas(FALSE)", "current_schemas", "name[]", False),
        ('"current_user"()', "current_user", "name", False),
        ('"session_user"()', "session_user", "name", False),
        ('"system_user"()', "system_user", "text", True),
        ("CURRENT_SCHEMA::TEXT", "current_schema", "text", True),
        ("CAST(current_schema() AS VARCHAR(20))", "current_schema", "varchar(20)", True),
        ("COALESCE(NULL::NAME, CURRENT_SCHEMA)", "coalesce", "name", True),
        ("CASE WHEN TRUE THEN NULL ELSE CURRENT_SCHEMA END", "current_schema", "name", True),
        ("ARRAY[CURRENT_SCHEMA]", "array", "name[]", False),
    ]
    return [{
        "sql": "SELECT " + expression + ";", "parameter_types": "", "parameter_values": [],
        "output_columns": [{"name": label, "type": type_, "nullable": nullable}],
        "postgres_display_type": "character varying(20)" if type_ == "varchar(20)" else type_,
    } for expression, label, type_, nullable in cases]


def runtime_cases():
    return [{
        "sql": f"SELECT {expression} AS v;", "parameter_types": types, "parameter_values": values,
        "sqlstate": state, "output_columns": [{"name": "v", "type": type_, "nullable": nullable}],
    } for expression, types, values, state, type_, nullable in (
        ("length($1::BYTEA, COALESCE(NULLIF(CURRENT_SCHEMA,CURRENT_SCHEMA),$2::NAME))",
         "text,text", ["\\xff", "UTF8"], "22021", "int32", False),
        ("length('abc'::BYTEA, COALESCE(NULLIF(CURRENT_SCHEMA,CURRENT_SCHEMA),$1::NAME))",
         "text", ["NO_SUCH_ENCODING"], "22023", "int32", False),
        ("CURRENT_SCHEMA ~ $1", "text", ["["], "2201B", "bool", True),
        ("CURRENT_SCHEMA = CAST(1 / $1 AS NAME)", "int", [0], "22012", "bool", True),
    )]


def analysis_boundaries():
    return [(sql, "invalid", state) for sql, state in (
        ("SELECT CURRENT_SCHEMA + 1", "42883"), ("SELECT -CURRENT_USER", "42883"),
        ("SELECT current_schema(1)", "42883"), ("SELECT current_database(1)", "42883"),
        ("SELECT current_schemas()", "42883"), ("SELECT current_schemas(1)", "42883"),
        ("SELECT current_schemas(TRUE,FALSE)", "42883"), ("SELECT CURRENT_SCHEMA = 1", "42883"),
        ("SELECT CURRENT_SCHEMA LIKE 1", "42883"), ("SELECT CURRENT_SCHEMA ~ TRUE", "42883"),
    )] + [(sql, "parse", "42601") for sql in (
        "SELECT 'a'::NAME(2)", "SELECT CAST(NULL AS NAME(2)[])",
    )] + [(sql, "valid", "00000") for sql in (
        "SELECT NAME 'x' = NAME 'x'", "SELECT CURRENT_SCHEMA = 'pg_catalog'::CHAR(12)",
        "SELECT length('abc'::BYTEA,'UTF8')")]


def analysis_script():
    body = ("BEGIN EXECUTE 'PREPARE context_boundary AS ' || query; "
            "DEALLOCATE context_boundary; RETURN '00000'; EXCEPTION WHEN OTHERS THEN RETURN SQLSTATE; END;")
    commands = ["BEGIN;", "CREATE FUNCTION pg_temp.context_analysis(query TEXT) RETURNS TEXT LANGUAGE plpgsql AS "
                + sql_literal(body) + ";"]
    commands += ["SELECT pg_temp.context_analysis(" + sql_literal(sql) + ");"
                 for sql, _, _ in analysis_boundaries()]
    commands.append("ROLLBACK;")
    return "\n".join(commands), [state for _, _, state in analysis_boundaries()]


def boundaries():
    for sql, status, _ in analysis_boundaries():
        if status != "parse":
            assert_report(["--assurance", "contract", sql], status, "contract")
    unsupported = [
        'SELECT "CURRENT_USER"()',
        'SELECT app.current_schema()',
    ]
    promoted = [
        ('SELECT CURRENT_SCHEMA = (SELECT CURRENT_SCHEMA)', (('?column?', 'bool', True),)),
    ]
    for sql, columns in promoted:
        assert_report(["--assurance", "contract", sql], "valid", "contract", columns)
    for sql in unsupported:
        assert_report(["--assurance", "contract", sql], "unsupported", "contract")
    malformed = ["SELECT " + word + "()" for word in (
        "CURRENT_CATALOG", "CURRENT_USER", "USER", "CURRENT_ROLE", "SESSION_USER", "SYSTEM_USER")]
    malformed += [sql for sql, status, _ in analysis_boundaries() if status == "parse"]
    for sql in malformed:
        result = invoke(["--render-assurance", "identity"], stdin=sql)
        report = json.loads(result.stdout)
        assert (result.returncode, report["status"], report["diagnostic"]["code"]) == (
            1, "invalid", "input.parse"), report
    # The expanded tier retains NAME as its own opaque family for direct
    # context results; it does not erase the value to TEXT.
    assert_report(["--assurance", "checked", "SELECT CURRENT_SCHEMA"], "checked", "checked")
    return sum(status != "parse" for _, status, _ in analysis_boundaries()) + len(unsupported) + len(malformed) + 1 + len(promoted)


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    target = parser.add_mutually_exclusive_group(required=True)
    target.add_argument("--local-bin")
    target.add_argument("--dsn", help="requires private role creation and session-authorization privileges")
    parser.add_argument("--psql")
    args = parser.parse_args()
    rows, sources = load_cases()
    canonical = []
    for row in rows:
        validity(row)
        replay("identity", row["sql"])
        canonical.append(replay("postgres", row["sql"])["sql"])
        reject_sqlite(row)
    registry = source_registry()
    for source in sources:
        if source["id"] in registry:
            assert_report(["--assurance", "contract", source["sql"]], "valid", "contract", registry[source["id"]])
        elif source["id"] in unsupported_source_free():
            assert_report(["--assurance", "contract", source["sql"]], "unsupported", "contract")
        for profile in ("identity", "postgres"):
            replay(profile, source["sql"])
    errors, labels = runtime_cases(), label_cases()
    error_rendered, label_rendered = [], []
    for population, output in ((errors, error_rendered), (labels, label_rendered)):
        for case in population:
            validity(case)
            output.append(replay("postgres", case["sql"])["sql"])
    boundary_count = boundaries()
    values_sql, values = database_script(rows, canonical)
    null_sql, nulls = null_script(rows, canonical)
    metadata_sql, metadata = describe_script(rows + labels, canonical + label_rendered)
    errors_sql, error_states = error_script(errors, error_rendered)
    catalog_sql, catalog = catalog_script()
    boundary_sql, states = analysis_script()
    with connection(args) as psql:
        for script, expected in ((values_sql, values), (null_sql, nulls), (errors_sql, error_states)):
            result = run([*psql, "-X", "-q", "-v", "ON_ERROR_STOP=1"],
                         input=controlled_path(script), timeout=120)
            validate_results(parse_results(result.stdout), expected)
        for script, expected in ((controlled_path(metadata_sql), metadata),
                                 (catalog_sql, catalog), (boundary_sql, states)):
            result = run([*psql, "-X", "-qAt", "-v", "ON_ERROR_STOP=1"], input=script, timeout=120)
            assert result.stdout.splitlines() == expected, (result.stdout.splitlines(), expected)
        from context_values_native_states import check_states
        state_count = check_states(psql)
        version = run([*psql, "-X", "-At", "-c", "SHOW server_version;"]).stdout.strip()
    print("PASS: 50 authored full-query certificates; 50 source renderings and 13 fixed source certificates")
    print(f"PASS: {boundary_count} static/parser boundaries; 50 exact SQLite exclusions/input boundaries")
    print(f"PASS: PostgreSQL {version}: {len(values)} value/OID, {len(nulls)} SQL NULL, "
          f"{len(metadata)} descriptor, {len(error_states)} expected-error observations")
    print(f"PASS: {len(catalog)} catalog/B-tree declarations, {len(states)} analysis outcomes; native states {state_count}")
    print("Scope: finite authored executions and fixed context typing; source corpus SQL is never executed.")


if __name__ == "__main__":
    main()
