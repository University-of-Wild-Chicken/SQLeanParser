#!/usr/bin/env python3
"""Check named/default argument certificates and finite native observations."""
import argparse
import hashlib
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
from observe_named_argument_source import INTERFACE_CASES, INTERFACE_PATH, interface_evidence

FIXTURES = ROOT / "fixtures/named_arguments"
NAMES = ("years", "months", "weeks", "days", "hours", "mins", "secs")


def source_registry():
    """Fix result and input declarations before consulting the checker."""
    pg = "named_arguments:postgres:src/test/regress/sql/interval.sql:statement-"
    sqlc = "named_arguments:sqlc:internal/endtoend/testdata/func_args/pgx/v5/query.sql:statement-"
    result = {
        pg + str(i): {"parameter_types": "", "columns": (
            ("?column?", "bool", False) if i == 323 else ("make_interval", "interval", False),)}
        for i in range(320, 325)
    }
    # These concrete input types are recorded by the pinned generated sqlc
    # methods (float64 and int32); no application relation catalog is invented.
    result[sqlc + "1"] = {"parameter_types": "double precision", "columns": (("make_interval", "interval", False),)}
    result[sqlc + "2"] = {"parameter_types": "integer", "columns": (("make_interval", "interval", False),)}
    return result


def load_cases():
    rows = json.loads((FIXTURES / "synthetic.json").read_text())
    sources = [json.loads(line) for line in (FIXTURES / "concrete.jsonl").read_text().splitlines()]
    for population in (rows, sources):
        assert len(population) == len({r["id"] for r in population}) == len({r["sql"] for r in population}) == 50
    for i, row in enumerate(rows, 1):
        type_ = {46: "numeric", 47: "interval day to second(2)", 48: "bool", 50: "bool"}.get(i, "interval")
        assert row["id"].startswith(f"named-arguments-{i:02}-") and row["source_kind"] == "synthetic"
        assert row["output_columns"] == [{"name": "v", "type": type_, "nullable": i in {42, 43, 49}}]
        assert type(row["output_columns"][0]["nullable"]) is bool
        assert row["postgres_type"] == ("boolean" if type_ == "bool" else "interval" if i == 47 else type_)
        assert row["postgres_display_type"] == ("boolean" if type_ == "bool" else type_)
        assert row["expected_value"] is None or type(row["expected_value"]) is str
        assert type(row["expected_sql_null"]) is bool and row["expected_sql_null"] == (i in {42, 43, 49})
        assert row["expected_sql_null"] == (row["expected_value"] is None)
        assert row["sqlite_supported"] is False and row["sqlite_input"] == row["sql"].replace("$", "?")
        assert {slot for _, slot in parameters(row["sql"], "postgres")} == set(
            range(1, len(row["parameter_values"]) + 1))
        assert len([t for t in row["parameter_types"].split(",") if t]) == len(row["parameter_values"])
        assert question_parameters(row["sql"]) == row["postgres_input"]
    assert set(source_registry()) <= {r["id"] for r in sources}
    assert all(r["raw_sql"] == r["sql"] and r["transformations"] == [] for r in sources)
    assert all(type(r["observed_syntax"]["source_free"]) is bool for r in sources)
    assert sum(r["observed_syntax"]["source_free"] for r in sources) == 46
    interface = (ROOT / "fixtures/factor_sources/sources/sqlc" / INTERFACE_PATH).read_text()
    assert hashlib.sha256(interface.encode()).hexdigest() == (
        "625c536dc7ea795ca784ceaad0dc0e0f9175cb6df1a9a838c1dd37bb8abd78e2")
    interface_url = ("https://github.com/sqlc-dev/sqlc/blob/"
                     "0f1602fe1a4b780336e3e878dde720892fd8578d/" + INTERFACE_PATH)
    for source in sources:
        if source["id"] in INTERFACE_CASES:
            assert source["parameter_types"] == source_registry()[source["id"]]["parameter_types"]
            assert source["parameter_type_provenance"] == interface_evidence(
                source["id"], source["sql"], interface, interface_url)
        else:
            assert source["parameter_types"] is None and "parameter_type_provenance" not in source
    return rows, sources


def function_script():
    rows = json.loads((FIXTURES / "function_signatures.json").read_text())
    assert rows == [{
        "name": "make_interval", "names": list(NAMES),
        "inputs": ["integer"] * 6 + ["double precision"], "defaults": ["0"] * 6 + ["0.0"],
        "output": "interval",
    }]
    sql = (
        "SELECT EXISTS(SELECT FROM pg_catalog.pg_proc p "
        "WHERE p.oid='pg_catalog.make_interval(integer,integer,integer,integer,integer,integer,double precision)'::regprocedure "
        "AND p.pronamespace='pg_catalog'::regnamespace AND p.proname='make_interval' "
        "AND p.proargnames=ARRAY['years','months','weeks','days','hours','mins','secs']::text[] "
        "AND p.pronargs=7 AND p.pronargdefaults=7 "
        "AND pg_catalog.pg_get_expr(p.proargdefaults,0)='0, 0, 0, 0, 0, 0, 0.0' "
        "AND p.prorettype='interval'::regtype AND p.proisstrict AND p.provolatile='i' "
        "AND NOT p.proretset AND p.provariadic=0 AND p.prokind='f');")
    return sql, ["t"]


def default_cases():
    """All 128 omission sets; expected interval fields are authored separately."""
    result = []
    for mask in range(128):
        present = [i for i in range(7) if mask & (1 << i)]
        arguments = ", ".join(f"{NAMES[i]} => 1" for i in reversed(present))
        fields = []
        if 0 in present:
            fields.append("1 year")
        if 1 in present:
            fields.append("1 mon")
        days = (7 if 2 in present else 0) + (1 if 3 in present else 0)
        if days:
            fields.append(f"{days} days")
        fields.append(":".join("01" if i in present else "00" for i in (4, 5, 6)))
        expected = " ".join(fields)
        result.append({
            "sql": f"SELECT make_interval({arguments}) = INTERVAL '{expected}' AS v;",
            "parameter_types": "", "parameter_values": [],
            "output_columns": [{"name": "v", "type": "bool", "nullable": False}],
            "postgres_type": "boolean", "postgres_display_type": "boolean",
            "expected_value": "true", "expected_sql_null": False,
        })
    return result


def type_boundaries():
    scalar_types = ("SMALLINT", "INTEGER", "BIGINT", "NUMERIC(8,2)", "REAL", "DOUBLE PRECISION",
                    "TEXT", "NAME", "VARCHAR(4)", "CHAR(4)", "BOOLEAN", "DATE", "TIME",
                    "TIME WITH TIME ZONE", "TIMESTAMP", "TIMESTAMP WITH TIME ZONE", "INTERVAL",
                    "UUID", "JSON", "JSONB", "BYTEA")
    return [
        (f"SELECT make_interval({name} => CAST(NULL AS {type_}))",
         "valid" if index < (6 if name == "secs" else 2) else "invalid",
         "00000" if index < (6 if name == "secs" else 2) else "42883")
        for name in NAMES for index, type_ in enumerate(scalar_types)
    ]


def analysis_boundaries():
    return type_boundaries() + [
        ("SELECT " + expr, status, state) for expr, status, state in (
            ("make_interval(days => 1, 2)", "invalid", "42601"),
            ("make_interval(days => 1, days := 2)", "invalid", "42601"),
            ("make_interval(1, years => 2)", "invalid", "42883"),
            ("make_interval(1, 2, months => 3)", "invalid", "42883"),
            ("make_interval(day => 1)", "invalid", "42883"),
            ('make_interval("Years" => 1)', "invalid", "42883"),
            ("make_interval(1,2,3,4,5,6,7,8)", "invalid", "42883"),
            ("make_interval(1,2,3,4,5,6,7,secs=>8)", "invalid", "42883"),
            ("make_interval(years => 'bad')", "valid", "22P02"),
            ("make_interval(secs => 'bad')", "valid", "22P02"),
            ("make_interval(years => '2147483648')", "valid", "22003"),
            ('make_interval("years" => NULL)', "valid", "00000"),
        )
    ]


def analysis_script():
    body = ("BEGIN EXECUTE 'PREPARE named_boundary AS ' || query; "
            "DEALLOCATE named_boundary; RETURN '00000'; EXCEPTION WHEN OTHERS THEN RETURN SQLSTATE; END;")
    commands = ["BEGIN;", "CREATE FUNCTION pg_temp.named_analysis(query TEXT) RETURNS TEXT LANGUAGE plpgsql AS "
                + sql_literal(body) + ";"]
    commands += ["SELECT pg_temp.named_analysis(" + sql_literal(sql) + ");"
                 for sql, _, _ in analysis_boundaries()]
    commands.append("ROLLBACK;")
    return "\n".join(commands), [state for _, _, state in analysis_boundaries()]


def runtime_cases():
    return [{
        "sql": f"SELECT {expr} AS v;", "parameter_types": types, "parameter_values": values,
        "output_columns": [{"name": "v", "type": "interval", "nullable": nullable}], "sqlstate": state,
    } for expr, types, values, nullable, state in (
        ("make_interval(secs => CAST($1 AS FLOAT8))", "text", ["Infinity"], False, "22008"),
        ("make_interval(secs := CAST($1 AS FLOAT8))", "text", ["NaN"], False, "22008"),
        ("make_interval(days => CAST($1 AS INTEGER))", "text", ["bad"], False, "22P02"),
        ("make_interval(years => CAST($1 AS INTEGER))", "text", ["2147483648"], False, "22003"),
        ("make_interval(days => 1 / $1)", "int", [0], False, "22012"),
        ("make_interval(days => NULL, secs => CAST($1 AS FLOAT8))", "text", ["bad"], True, "22P02"),
    )]


def label_cases():
    return [{
        "sql": "SELECT " + expr + ";", "parameter_types": "", "parameter_values": [],
        "output_columns": [{"name": label, "type": type_, "nullable": nullable}],
        "postgres_display_type": type_,
    } for expr, label, type_, nullable in (
        ("make_interval()", "make_interval", "interval", False),
        ("make_interval(days => 1)", "make_interval", "interval", False),
        ("make_interval(days := 1)", "make_interval", "interval", False),
        ("pg_catalog.make_interval(days => 1)", "make_interval", "interval", False),
        ('"make_interval"(days => 1)', "make_interval", "interval", False),
        ("CAST(make_interval(days => 1) AS TEXT)", "make_interval", "text", False),
        ("CASE WHEN TRUE THEN make_interval(days => 1) ELSE make_interval() END",
         "make_interval", "interval", False),
        ("COALESCE(make_interval(days => NULL), make_interval())", "coalesce", "interval", False),
        ("ARRAY[make_interval(),make_interval(secs => NULL)]", "array", "interval[]", False),
        ("make_interval(secs => NULL)", "make_interval", "interval", True),
    )]


def boundaries():
    for sql, status, _ in analysis_boundaries():
        assert_report(["--assurance", "contract", sql], status, "contract")
    unsupported = [
        "SELECT custom_fn(x => 1)", "SELECT app.make_interval(days => 1)",
        'SELECT "MAKE_INTERVAL"(days => 1)', "SELECT make_interval(days => (SELECT 1))",
        "SELECT make_interval(days => unknown_fn())", "SELECT lower(string => 'X')",
    ]
    for sql in unsupported:
        assert_report(["--assurance", "contract", sql], "unsupported", "contract")
    malformed = [
        "SELECT make_interval(days =>)", "SELECT make_interval(=> 1)",
        "SELECT make_interval(days :=)", "SELECT make_interval(days => 1,)",
        "SELECT make_interval(days => 1 secs => 2)", "SELECT make_interval(days = > 1)",
        "SELECT make_interval(days : = 1)", "SELECT make_interval(1 => 2)",
    ]
    for sql in malformed:
        result = invoke(["--render-assurance", "identity"], stdin=sql)
        report = json.loads(result.stdout)
        assert (result.returncode, report["status"], report["diagnostic"]["code"]) == (
            1, "invalid", "input.parse"), report
    return len(analysis_boundaries()) + len(unsupported) + len(malformed)


def sqlite_expectation(case):
    index = int(case["id"].split("-")[2])
    if index <= 8:
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
            entry = registry[source["id"]]
            args_ = ["--assurance", "contract"]
            if entry["parameter_types"]:
                args_ += ["--param-types", entry["parameter_types"]]
            assert_report([*args_, source["sql"]], "valid", "contract", entry["columns"])
        elif source["observed_syntax"]["source_free"]:
            assert_report(["--assurance", "contract", source["sql"]], "unsupported", "contract")
        for profile in ("identity", "postgres"):
            replay(profile, source["sql"])
    defaults, errors, labels = default_cases(), runtime_cases(), label_cases()
    default_rendered, error_rendered, label_rendered = [], [], []
    for population, output in ((defaults, default_rendered), (errors, error_rendered), (labels, label_rendered)):
        for row in population:
            validity(row)
            output.append(replay("postgres", row["sql"])["sql"])
    boundary_count = boundaries()
    values_sql, values = database_script(rows + defaults, canonical + default_rendered)
    null_sql, nulls = null_script(rows + defaults, canonical + default_rendered)
    metadata_sql, metadata = describe_script(rows + defaults + labels, canonical + default_rendered + label_rendered)
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
    print("PASS: 50 authored and seven fixed source certificates; 50 original-source renderings")
    print(f"PASS: all 128 default subsets; {boundary_count} static/parser boundaries; 50 exact SQLite exclusions")
    print(f"PASS: PostgreSQL {version}: {len(values)} value/OID, {len(nulls)} SQL NULL, "
          f"{len(metadata)} descriptor, {len(error_states)} expected-error observations")
    print(f"PASS: exact seven-slot catalog declaration/defaults and {len(states)} native analysis outcomes")
    print("Scope: authored executions only; source SQL is never executed. No general runtime-success proof.")


if __name__ == "__main__":
    main()
