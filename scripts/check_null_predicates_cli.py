#!/usr/bin/env python3
"""Check exact NULL-predicate certificates and separate native dialect observations."""
import argparse
from collections import Counter
import hashlib
import json
import sqlite3

from check_advanced_cli import question_parameters
from check_array_types_cli import describe_script, validate_results, validity
from check_assurance_cli import assert_report, invoke
from check_extended_types_cli import database_script
from check_json_containment_cli import error_script
from check_json_extraction_cli import null_script
from check_pagination_cli import ROOT, replay, sqlite_bindings
from check_postgresql_cli import connection, parse_results, run, sql_literal
from check_renderer_corpus import parameters

FACTORS = ("distinct_from", "null_predicates")
FIXTURES = ROOT / "fixtures"
TYPES = ("SMALLINT", "INTEGER", "BIGINT", "NUMERIC(8,2)", "REAL", "DOUBLE PRECISION",
         "TEXT", "VARCHAR(5)", "CHAR(5)", "NAME", "BOOLEAN", "DATE", "TIME",
         "TIME WITH TIME ZONE", "TIMESTAMP", "TIMESTAMP WITH TIME ZONE", "INTERVAL",
         "UUID", "JSON", "JSONB", "BYTEA", "INTEGER[]", "BIGINT[]", "TEXT[]",
         "VARCHAR(5)[]", "JSON[]", "JSONB[]", "NAME[]")


def source_registry():
    """Fixed eligibility and ordered metadata, registered independently of SQLean."""
    path = FIXTURES / "null_predicates" / "source_contracts.json"
    data = json.loads(path.read_text())
    # Frozen after independent source inspection and cross-check against the
    # separately declared Lean registry, not generated from checker successes.
    assert hashlib.sha256(json.dumps(data, sort_keys=True, separators=(",", ":")).encode()).hexdigest() == (
        "af3bd7a953618ca59d7809f715d34a5adaed6eb8b74a8c58875fb32f1430021b")
    assert set(data) == set(FACTORS)
    result = {}
    for factor, count, arity in (("distinct_from", 25, 34), ("null_predicates", 22, 25)):
        rows = data[factor]
        assert isinstance(rows, list) and len(rows) == len({r["id"] for r in rows}) == count
        columns = [c for row in rows for c in row["output_columns"]]
        assert len(columns) == arity
        assert Counter(c["type"] for c in columns) == (
            {"bool": 34} if factor == "distinct_from" else {"bool": 23, "varchar": 2})
        for row in rows:
            assert set(row) == {"id", "output_columns"} and row["id"].startswith(factor + ":")
            assert isinstance(row["output_columns"], list) and row["output_columns"]
            for column in row["output_columns"]:
                assert set(column) == {"name", "type", "nullable"}
                assert isinstance(column["name"], str) and column["name"]
                assert type(column["nullable"]) is bool and column["nullable"] is False
        result[factor] = {row["id"]: tuple((c["name"], c["type"], c["nullable"])
                                        for c in row["output_columns"]) for row in rows}
    return result


def load_cases():
    authored, concrete = [], []
    registry = source_registry()
    for factor in FACTORS:
        rows = json.loads((FIXTURES / factor / "synthetic.json").read_text())
        sources = [json.loads(line) for line in (FIXTURES / factor / "concrete.jsonl").read_text().splitlines()]
        for population in (rows, sources):
            assert len(population) == len({r["id"] for r in population}) == len({r["sql"] for r in population}) == 50
        prefix = factor.replace("_", "-")
        for index, row in enumerate(rows, 1):
            ordinal = (index - 1) % 25 + 1
            assert row["id"].startswith(f"{prefix}-{index:02}-")
            assert row["source_kind"] == "synthetic"
            assert row["output_columns"] == [{"name": "v", "type": "bool", "nullable": False}]
            assert type(row["output_columns"][0]["nullable"]) is bool
            assert row["postgres_type"] == row["postgres_display_type"] == "boolean"
            assert row["expected_value"] in ("true", "false") and row["expected_sql_null"] is False
            assert type(row["sqlite_supported"]) is bool
            sqlite = ordinal <= 11 or ordinal in {14, 15, 17} if factor == "distinct_from" else ordinal <= 9 or ordinal >= 22
            assert row["sqlite_supported"] == sqlite
            assert row["sqlite_expected_value"] in (0, 1) if sqlite else row["sqlite_expected_value"] is None
            assert not sqlite or type(row["sqlite_expected_value"]) is int
            assert row["sqlite_input"] == row["sql"].replace("$", "?")
            assert (row["sqlite_sql"] is not None) == sqlite
            if sqlite:
                assert parameters(row["sqlite_sql"], "sqlite") == parameters(row["sqlite_input"], "sqlite")
            assert question_parameters(row["sql"]) == row["postgres_input"]
            assert {slot for _, slot in parameters(row["sql"], "postgres")} == set(
                range(1, len(row["parameter_values"]) + 1))
            assert len([t for t in row["parameter_types"].split(",") if t]) == len(row["parameter_values"])
        assert registry[factor].keys() <= {r["id"] for r in sources}
        eligible = {r["id"] for r in sources
                    if r["observed_syntax"]["source_free"] and r["source"] != "calcite"}
        assert eligible == registry[factor].keys()
        assert sum(r["observed_syntax"]["source_free"] for r in sources) == (
            25 if factor == "distinct_from" else 23)
        excluded_closed = [r for r in sources if r["observed_syntax"]["source_free"]
                           and r["id"] not in eligible]
        assert len(excluded_closed) == (0 if factor == "distinct_from" else 1)
        if excluded_closed:
            assert excluded_closed[0]["source"] == "calcite"
            assert any(e["nested_row"] for e in excluded_closed[0]["observed_syntax"][factor])
        for source in sources:
            assert source["parameter_types"] is None
            assert source["raw_sql"] == source["sql"] and source["transformations"] == []
            assert type(source["observed_syntax"]["source_free"]) is bool
        authored += rows
        concrete += sources
    return authored, concrete


def native_equality_pair(first, second):
    """Independent PG16 analysis expectations for these 28 exact declarations."""
    numeric = set(TYPES[:6])
    strings = set(TYPES[6:10])
    dates = {"DATE", "TIMESTAMP", "TIMESTAMP WITH TIME ZONE"}
    if any(first in group and second in group for group in (numeric, strings, dates)):
        return True
    if (first, second) in {("TIME", "TIME WITH TIME ZONE"), ("TIME WITH TIME ZONE", "TIME"),
                           ("TIME", "INTERVAL"), ("INTERVAL", "TIME")}:
        return True
    return first == second and first != "JSON"


def type_boundaries():
    rows = []
    for negated in (False, True):
        op = "IS NOT DISTINCT FROM" if negated else "IS DISTINCT FROM"
        for first in TYPES:
            for second in TYPES:
                native = native_equality_pair(first, second)
                status = "unsupported" if first == second == "JSON[]" else "valid" if native else "invalid"
                for row in (False, True):
                    left, right = f"CAST(NULL AS {first})", f"CAST(NULL AS {second})"
                    if row:
                        left, right = f"ROW({left})", f"ROW({right})"
                    rows.append((f"SELECT {left} {op} {right}", status, "00000" if native else "42883"))
    return rows


def analysis_boundaries():
    rows = type_boundaries()
    for type_ in TYPES:
        for subject in (f"CAST(NULL AS {type_})", f"ROW(CAST(NULL AS {type_}))"):
            for expression in (f"{subject} IS DISTINCT FROM NULL", f"NULL IS DISTINCT FROM {subject}",
                               f"{subject} IS NOT DISTINCT FROM NULL", f"NULL IS NOT DISTINCT FROM {subject}",
                               f"{subject} ISNULL", f"{subject} NOTNULL"):
                rows.append((f"SELECT {expression}", "valid", "00000"))
    rows += [("SELECT " + expr, status, state) for expr, status, state in (
        ("ROW() IS DISTINCT FROM ROW()", "valid", "00000"),
        ("ROW() IS NOT DISTINCT FROM ROW()", "valid", "00000"),
        ("ROW() ISNULL", "valid", "00000"), ("ROW() NOTNULL", "valid", "00000"),
        ("ROW() IS DISTINCT FROM ROW(1)", "invalid", "42601"),
        ("ROW(1,2) IS NOT DISTINCT FROM ROW(1)", "invalid", "42601"),
        ("ROW(NULL::JSON) IS DISTINCT FROM ROW(NULL)", "invalid", "42883"),
        ("ROW(NULL) IS NOT DISTINCT FROM ROW(NULL::JSON)", "invalid", "42883"),
        ("'bad' IS DISTINCT FROM 1", "valid", "22P02"),
        ("'2147483648' IS NOT DISTINCT FROM 1", "valid", "22003"),
        ("NULL IS DISTINCT FROM COALESCE(NULL,NULL)", "valid", "00000"),
        ("1 = 1 ISNULL", "valid", "00000"),
        ("1 = NULL NOTNULL", "valid", "00000"),
        ("TRUE ISNULL ISNULL", "valid", "00000"),
        ("1 ISNULL IS DISTINCT FROM FALSE", "valid", "00000"),
        ("1 IS DISTINCT FROM 1 = 1", "invalid", "42883"),
    )]
    return rows


def analysis_script():
    body = ("BEGIN EXECUTE 'PREPARE null_boundary AS ' || query; "
            "DEALLOCATE null_boundary; RETURN '00000'; EXCEPTION WHEN OTHERS THEN RETURN SQLSTATE; END;")
    commands = ["BEGIN;", "CREATE FUNCTION pg_temp.null_analysis(query TEXT) RETURNS TEXT LANGUAGE plpgsql AS "
                + sql_literal(body) + ";"]
    commands += ["SELECT pg_temp.null_analysis(" + sql_literal(sql) + ");"
                 for sql, _, _ in analysis_boundaries()]
    commands.append("ROLLBACK;")
    return "\n".join(commands), [state for _, _, state in analysis_boundaries()]


def runtime_cases():
    return [{"sql": f"SELECT {expression} AS v;", "parameter_types": types,
             "parameter_values": values,
             "output_columns": [{"name": "v", "type": "bool", "nullable": False}],
             "sqlstate": state}
            for expression, types, values, state in (
                ("CAST($1 AS INTEGER) IS DISTINCT FROM NULL", "text", ["bad"], "22P02"),
                ("1 / $1 IS NOT DISTINCT FROM NULL", "int", [0], "22012"),
                ("ROW(CAST($1 AS INTEGER)) IS DISTINCT FROM ROW(1)", "text", ["bad"], "22P02"),
                ("ROW(1 / $1,NULL) ISNULL", "int", [0], "22012"),
                ("CAST($1 AS JSON) NOTNULL", "text", ["bad json"], "22P02"),
                ("ARRAY[[1],[2,3]] IS DISTINCT FROM NULL", "", [], "2202E"),
                ("ROW(ARRAY[[1],[2,3]]) IS NULL", "", [], "2202E"),
                ("CAST($1 AS INTEGER) NOTNULL", "text", ["2147483648"], "22003"),
            )]


def label_cases():
    return [{"sql": f"SELECT {expression};", "parameter_types": "", "parameter_values": [],
             "output_columns": [{"name": label, "type": type_, "nullable": False}],
             "postgres_display_type": "boolean" if type_ == "bool" else "text"}
            for expression, label, type_ in (
                ("1 IS DISTINCT FROM 2", "?column?", "bool"),
                ("NULL IS NOT DISTINCT FROM NULL", "?column?", "bool"),
                ("1 ISNULL", "?column?", "bool"), ("NULL NOTNULL", "?column?", "bool"),
                ("ROW(1,NULL) ISNULL", "?column?", "bool"),
                ("ROW() NOTNULL", "?column?", "bool"),
                ("ROW(1) IS DISTINCT FROM ROW(2)", "?column?", "bool"),
                ("ROW(NULL) IS NOT DISTINCT FROM NULL", "?column?", "bool"),
                ("CAST(1 IS DISTINCT FROM 2 AS TEXT)", "text", "text"),
                ("CAST(ROW(1) ISNULL AS TEXT)", "text", "text"),
                ("CASE WHEN TRUE THEN 1 ISNULL ELSE 2 NOTNULL END", "case", "bool"),
                ("COALESCE(NULL IS DISTINCT FROM NULL,TRUE)", "coalesce", "bool"),
            )]


def boundaries():
    for sql, status, _ in analysis_boundaries():
        assert_report(["--assurance", "contract", sql], status, "contract")
    unsupported = [
        'SELECT ROW(ROW(1,NULL)) IS DISTINCT FROM ROW(ROW(1,NULL))',
        'SELECT ROW(ROW(NULL)) ISNULL',
        'SELECT ROW(1) IS DISTINCT FROM 1',
        'SELECT unknown_fn() ISNULL',
        'SELECT isnull(1)',
        'SELECT notnull(1)',
    ]
    promoted = [
        ('SELECT (SELECT 1) IS DISTINCT FROM 1', (('?column?', 'bool', False),)),
    ]
    for sql, columns in promoted:
        assert_report(["--assurance", "contract", sql], "valid", "contract", columns)
    for sql in unsupported:
        assert_report(["--assurance", "contract", sql], "unsupported", "contract")
    undeclared = ["SELECT $1 IS DISTINCT FROM NULL", "SELECT NULL IS DISTINCT FROM $1", "SELECT $1 ISNULL"]
    for sql in undeclared:
        assert_report(["--assurance", "contract", sql], "invalid", "contract")
    parse_boundaries = ["SELECT 1 IS DISTINCT 2", "SELECT 1 IS DISTINCT FROM",
                 "SELECT 1 IS NOT DISTINCT 2", "SELECT ISNULL", "SELECT 1 IS NOTNULL",
                 "SELECT 1 IS DISTINCT FROM 1 ISNULL", "SELECT 1 IS DISTINCT FROM 2 IS DISTINCT FROM 3",
                 # Valid PostgreSQL syntax; RECORD is outside the typed parser's coverage.
                 "SELECT ROW(1) IS DISTINCT FROM NULL::RECORD"]
    for sql in parse_boundaries:
        result = invoke(["--render-assurance", "identity"], stdin=sql)
        report = json.loads(result.stdout)
        assert (result.returncode, report["status"], report["diagnostic"]["code"]) == (
            1, "invalid", "input.parse"), report
    return len(analysis_boundaries()) + len(unsupported) + len(undeclared) + len(parse_boundaries) + len(promoted)


def sqlite_expectation(case):
    ordinal = (int(case["id"].split("-")[2]) - 1) % 25 + 1
    if case["id"].startswith("distinct-from"):
        if ordinal in {12, 16, 18, 19}:
            return 3, "unsupported", "coverage.sqlite.PostgreSQL-type"
        return 1, "invalid", "input.parse"
    if ordinal in (10, 11, 12):
        return 3, "unsupported", "coverage.sqlite.PostgreSQL-type"
    return 1, "invalid", "input.parse"


def sqlite_render(case):
    if case["sqlite_supported"]:
        return replay("sqlite", case["sqlite_input"])["sql"]
    result = invoke(["--render-assurance", "sqlite"], stdin=case["sqlite_input"])
    report = json.loads(result.stdout)
    assert (result.returncode, report["status"], report["diagnostic"]["code"]) == sqlite_expectation(case), (case["id"], report)
    assert report["evidence"] == "none" and not ({"sql", "parameterMap", "theorems"} & report.keys()), report
    return None


def sqlite_observations(cases, canonical):
    assert len(cases) == len(canonical)
    count = 0
    with sqlite3.connect(":memory:") as db:
        for row, rendered in zip(cases, canonical):
            assert (rendered is not None) == row["sqlite_supported"]
            if rendered is None:
                continue
            for sql in (row["sqlite_sql"], rendered):
                cursor = db.execute(sql, sqlite_bindings(sql, row["parameter_values"]))
                assert [col[0] for col in cursor.description] == ["v"], (row["id"], cursor.description)
                actual = cursor.fetchall()
                assert actual == [(row["sqlite_expected_value"],)], (row["id"], sql, actual)
                count += 1
    return count


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
    registry = {key: value for values in source_registry().values() for key, value in values.items()}
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
    sqlite_count = sqlite_observations(rows, sqlite)
    values_sql, values = database_script(rows, canonical)
    null_sql, nulls = null_script(rows, canonical)
    metadata_sql, metadata = describe_script(rows + labels, canonical + label_rendered)
    errors_sql, error_states = error_script(errors, error_rendered)
    boundary_sql, states = analysis_script()
    with connection(args) as psql:
        for script, expected in ((values_sql, values), (null_sql, nulls), (errors_sql, error_states)):
            result = run([*psql, "-X", "-q", "-v", "ON_ERROR_STOP=1"], input=script, timeout=120)
            validate_results(parse_results(result.stdout), expected)
        for script, expected in ((metadata_sql, metadata), (boundary_sql, states)):
            result = run([*psql, "-X", "-qAt", "-v", "ON_ERROR_STOP=1"], input=script, timeout=120)
            assert result.stdout.splitlines() == expected, (result.stdout.splitlines(), expected)
        version = run([*psql, "-X", "-At", "-c", "SHOW server_version;"]).stdout.strip()
    print(f"PASS: 100 authored and {len(registry)} fixed source certificates; 100 original-source renderings")
    print(f"PASS: {boundary_count} static/parser boundaries; 46 exact SQLite exclusions")
    print(f"PASS: PostgreSQL {version}: {len(values)} value/OID, {len(nulls)} SQL NULL, "
          f"{len(metadata)} descriptor, {len(error_states)} expected-error observations")
    print(f"PASS: {len(states)} native analysis outcomes; SQLite {sqlite3.sqlite_version}: {sqlite_count} observations")
    print("Scope: authored executions and dialect-specific expectations only; source SQL is never executed.")


if __name__ == "__main__":
    main()
