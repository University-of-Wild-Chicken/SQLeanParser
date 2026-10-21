#!/usr/bin/env python3
"""Check keyword function heads, LEFT/RIGHT typing and authored native values."""
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

FIXTURES = ROOT / "fixtures/keyword_functions"


def source_registry():
    """Ordered metadata fixed independently of the implementation being checked."""
    result = {
        "keyword_functions:postgres:src/test/regress/sql/text.sql:statement-16":
            (("left", "text", False), ("right", "text", False)),
    }
    prefix = "keyword_functions:materialize:test/sqllogictest/string.slt:sqllogic-query-"
    for function, indexes in (
        ("left", (1251, 1256, 1263, 1268, 1273, 1287, 1293)),
        ("right", (1381, 1386, 1393, 1398, 1403, 1417, 1423)),
    ):
        for index in indexes:
            result[prefix + str(index)] = ((function, "text", index in {1251, 1256, 1381, 1386}),)
    prefix = "keyword_functions:doltgresql:testing/generation/function_coverage/output/"
    for function, indexes in (
        ("left", (1287, 3096, 4987, 6830, 7133, 9001, 10863, 12761, 14700,
                  15026, 16981, 18966, 20926, 22891, 23211, 813, 2093)),
        ("right", (1294, 3121, 5030, 6891, 7197, 9083, 10963, 12879, 14836,
                   15165, 17138, 19141, 21119, 23102, 23425, 815, 2108)),
    ):
        for index in indexes:
            result[f"{prefix}{function}_test.go:go-string-{index}"] = ((function, "text", False),)
    assert len(result) == 49 and sum(map(len, result.values())) == 50
    return result


def external_source_id():
    return "keyword_functions:river:riverdriver/riverpgxv5/internal/dbsqlc/schema.sql.go:indexReindexArtifacts"


def load_cases():
    rows = json.loads((FIXTURES / "synthetic.json").read_text())
    sources = [json.loads(line) for line in (FIXTURES / "concrete.jsonl").read_text().splitlines()]
    for population in (rows, sources):
        assert len(population) == len({r["id"] for r in population}) == len({r["sql"] for r in population}) == 50
    for index, row in enumerate(rows, 1):
        ordinal = (index - 1) % 25 + 1
        type_ = "bool" if ordinal == 25 else "text"
        nullable = ordinal in {15, 16, 17, 18, 19}
        assert row["id"].startswith(f"keyword-functions-{index:02}-")
        assert row["source_kind"] == "synthetic" and row["sqlite_supported"] is False
        assert row["output_columns"] == [{"name": "v", "type": type_, "nullable": nullable}]
        assert type(row["output_columns"][0]["nullable"]) is bool
        assert row["postgres_type"] == row["postgres_display_type"] == ("boolean" if type_ == "bool" else "text")
        assert type(row["expected_sql_null"]) is bool and row["expected_sql_null"] == nullable
        assert row["expected_value"] is None or type(row["expected_value"]) is str
        assert (row["expected_value"] is None) == nullable
        assert row["sqlite_input"] == row["sql"].replace("$", "?")
        assert question_parameters(row["sql"]) == row["postgres_input"]
        assert {slot for _, slot in parameters(row["sql"], "postgres")} == set(
            range(1, len(row["parameter_values"]) + 1))
        assert len([t for t in row["parameter_types"].split(",") if t]) == len(row["parameter_values"])
    registry = source_registry()
    assert {row["id"] for row in sources} == registry.keys() | {external_source_id()}
    for source in sources:
        assert source["parameter_types"] is None
        assert source["raw_sql"] == source["sql"] and source["transformations"] == []
        assert type(source["observed_syntax"]["source_free"]) is bool
        assert source["observed_syntax"]["source_free"] == (source["id"] in registry)
    return rows, sources


def function_script():
    rows = json.loads((FIXTURES / "function_signatures.json").read_text())
    assert rows == [{"name": name, "inputs": ["text", "integer"], "output": "text"}
                    for name in ("left", "right")]
    return "\n".join(
        f"SELECT {index}, EXISTS(SELECT FROM pg_catalog.pg_proc p WHERE "
        f"p.oid='pg_catalog.{name}(text,integer)'::regprocedure "
        f"AND p.proname='{name}' AND p.pronamespace='pg_catalog'::regnamespace "
        "AND p.pronargs=2 AND p.prorettype='text'::regtype AND p.proisstrict "
        "AND p.proargnames IS NULL AND p.pronargdefaults=0 AND p.provariadic=0 "
        "AND p.provolatile='i' AND p.prokind='f' AND NOT p.proretset);"
        for index, name in enumerate(("left", "right"))
    ), ["0|t", "1|t"]


def type_boundaries():
    types = ("SMALLINT", "INTEGER", "BIGINT", "NUMERIC(8,2)", "REAL", "DOUBLE PRECISION",
             "TEXT", "VARCHAR(5)", "CHAR(5)", "NAME", "BOOLEAN", "DATE", "TIME",
             "TIME WITH TIME ZONE", "TIMESTAMP", "TIMESTAMP WITH TIME ZONE", "INTERVAL",
             "INTERVAL DAY TO SECOND(2)", "UUID", "JSON", "JSONB", "BYTEA", "INTEGER[]", "TEXT[]", "NAME[]")
    return [
        (f"SELECT {function}(CAST(NULL AS {first}), CAST(NULL AS {second}))",
         "valid" if first in types[6:10] and second in types[:2] else "invalid",
         "00000" if first in types[6:10] and second in types[:2] else "42883")
        for function in ("left", "right") for first in types for second in types
    ]


def analysis_boundaries():
    return type_boundaries() + [
        (f"SELECT {function}({arguments})", status, state)
        for function in ("left", "right") for arguments, status, state in (
            ("", "invalid", "42883"), ("'abc'", "invalid", "42883"),
            ("'abc', 1, 2", "invalid", "42883"),
            ("NULL, NULL", "valid", "00000"),
            ("'abc', 'bad'", "valid", "22P02"),
            ("'abc', '2147483648'", "valid", "22003"),
            ("'abc', '2'", "valid", "00000"),
            ("'abc', -2147483648", "valid", "00000"),
        )
    ]


def analysis_script():
    body = ("BEGIN EXECUTE 'PREPARE keyword_boundary AS ' || query; "
            "DEALLOCATE keyword_boundary; RETURN '00000'; EXCEPTION WHEN OTHERS THEN RETURN SQLSTATE; END;")
    commands = ["BEGIN;", "CREATE FUNCTION pg_temp.keyword_analysis(query TEXT) RETURNS TEXT LANGUAGE plpgsql AS "
                + sql_literal(body) + ";"]
    commands += ["SELECT pg_temp.keyword_analysis(" + sql_literal(sql) + ");"
                 for sql, _, _ in analysis_boundaries()]
    commands.append("ROLLBACK;")
    return "\n".join(commands), [state for _, _, state in analysis_boundaries()]


def runtime_cases():
    return [{
        "sql": f"SELECT {function}({arguments}) AS v;",
        "parameter_types": types, "parameter_values": values,
        "output_columns": [{"name": "v", "type": "text", "nullable": nullable}], "sqlstate": state,
    } for function in ("left", "right") for arguments, types, values, nullable, state in (
        ("'abc', CAST($1 AS INTEGER)", "text", ["bad"], False, "22P02"),
        ("'abc', CAST($1 AS INTEGER)", "text", ["2147483648"], False, "22003"),
        ("'abc', 1 / $1", "int", [0], False, "22012"),
        ("NULL, CAST($1 AS INTEGER)", "text", ["bad"], True, "22P02"),
    )]


def label_cases():
    return [{
        "sql": f"SELECT {expression};", "parameter_types": "", "parameter_values": [],
        "output_columns": [{"name": label, "type": type_, "nullable": False}],
        "postgres_display_type": "character varying(2)" if type_ == "varchar(2)" else "text",
    } for function in ("left", "right") for expression, label, type_ in (
        (f"{function}('abc',2)", function, "text"),
        (f'"{function}"(\'abc\',2)', function, "text"),
        (f"CAST({function}('abc',2) AS VARCHAR(2))", function, "varchar(2)"),
        (f"CASE WHEN TRUE THEN {function}('abc',2) ELSE 'x' END", "case", "text"),
        (f"CASE WHEN TRUE THEN 'x' ELSE {function}('abc',2) END", function, "text"),
        (f"COALESCE({function}(NULL,1),'fallback')", "coalesce", "text"),
    )]


def boundaries():
    for sql, status, _ in analysis_boundaries():
        assert_report(["--assurance", "contract", sql], status, "contract")
    unsupported = [
        'SELECT "LEFT"(\'abc\',1)',
        "SELECT app.left('abc',1)",
        'SELECT left(unknown_fn(),1)',
        "SELECT left(string => 'abc', n => 1)",
        'SELECT join(1)',
        'SELECT ilike(1)',
    ]
    promoted = [
        ("SELECT left('abc',(SELECT 1))", (('left', 'text', True),)),
    ]
    for sql, columns in promoted:
        assert_report(["--assurance", "contract", sql], "valid", "contract", columns)
    for sql in unsupported:
        assert_report(["--assurance", "contract", sql], "unsupported", "contract")
    malformed = [
        "SELECT left", "SELECT right.x", "SELECT left.right('abc',1)",
        "SELECT left('abc',)", "SELECT right(,1)", "SELECT left('abc',1",
    ]
    for sql in malformed:
        result = invoke(["--render-assurance", "identity"], stdin=sql)
        report = json.loads(result.stdout)
        assert (result.returncode, report["status"], report["diagnostic"]["code"]) == (
            1, "invalid", "input.parse"), report
    return len(analysis_boundaries()) + len(unsupported) + len(malformed) + len(promoted)


def sqlite_expectation(case):
    index = int(case["id"].split("-")[2])
    if index in {24, 49}:
        return 3, "unsupported", "coverage.sqlite.scalar-function-signatures"
    return 1, "invalid", "input.parse"


def reject_sqlite(case):
    result = invoke(["--render-assurance", "sqlite"], stdin=case["sqlite_input"])
    report = json.loads(result.stdout)
    assert (result.returncode, report["status"], report["diagnostic"]["code"]) == sqlite_expectation(case), report
    assert report["evidence"] == "none" and not ({"sql", "parameterMap", "theorems"} & report.keys()), report


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    target = parser.add_mutually_exclusive_group(required=True)
    target.add_argument("--local-bin")
    target.add_argument("--dsn")
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
        for profile in ("identity", "postgres"):
            replay(profile, source["sql"])
    errors, labels = runtime_cases(), label_cases()
    error_rendered, label_rendered = [], []
    for population, output in ((errors, error_rendered), (labels, label_rendered)):
        for row in population:
            validity(row)
            output.append(replay("postgres", row["sql"])["sql"])
    boundary_count = boundaries()
    values_sql, values = database_script(rows, canonical)
    null_sql, nulls = null_script(rows, canonical)
    metadata_sql, metadata = describe_script(rows + labels, canonical + label_rendered)
    errors_sql, error_states = error_script(errors, error_rendered)
    catalog_sql, catalog = function_script()
    boundary_sql, states = analysis_script()
    with connection(args) as psql:
        for script, expected in ((values_sql, values), (null_sql, nulls), (errors_sql, error_states)):
            result = run([*psql, "-X", "-q", "-v", "ON_ERROR_STOP=1"], input=script, timeout=120)
            validate_results(parse_results(result.stdout), expected)
        for script, expected in ((metadata_sql, metadata), (catalog_sql, catalog), (boundary_sql, states)):
            result = run([*psql, "-X", "-qAt", "-v", "ON_ERROR_STOP=1"], input=script, timeout=120)
            assert result.stdout.splitlines() == expected, (result.stdout.splitlines(), expected)
        version = run([*psql, "-X", "-At", "-c", "SHOW server_version;"]).stdout.strip()
    print("PASS: 50 authored and 49 fixed source certificates; 50 original-source renderings")
    print(f"PASS: {boundary_count} static/parser boundaries; 50 exact SQLite exclusions")
    print(f"PASS: PostgreSQL {version}: {len(values)} value/OID, {len(nulls)} SQL NULL, "
          f"{len(metadata)} descriptor, {len(error_states)} expected-error observations")
    print(f"PASS: two exact native declarations and {len(states)} native analysis outcomes")
    print("Scope: authored executions only; source SQL is never executed. INT32_MIN RIGHT values are not a portable oracle.")


if __name__ == "__main__":
    main()
