#!/usr/bin/env python3
"""Verify JSONB existence contracts, bindings and finite native observations."""
import argparse
from collections import Counter
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

FIXTURES = ROOT / "fixtures/json_existence"


def source_registry():
    """Independently reviewed, closed source IDs and ordered output columns."""
    result = {}

    def add(prefix, indexes, double=(), nullable=()):
        for index in indexes:
            result[prefix + str(index)] = tuple(
                ("?column?", "bool", index in nullable) for _ in range(2 if index in double else 1))

    add("json_existence:postgres:contrib/pg_stat_statements/sql/select.sql:statement-", [25])
    add("json_existence:postgres:src/test/regress/sql/jsonb.sql:statement-",
        [189, 190, 191, 192, 201, 202, 203, 204, 205, 211, 212, 213, 214, 215, 216,
         707, 708, 709, 710, 711, 712])
    add("json_existence:cockroach:pkg/sql/logictest/testdata/logic_test/json:sqllogic-query-",
        [467, 472, 477, 482, 487, 492, 498, 504, 509, 514, 519, 524, 529, 534],
        double=[467, 472, 477, 487])
    add("json_existence:materialize:test/sqllogictest/jsonb.slt:sqllogic-query-",
        [657, 663, 668, 719, 745, 751, 756, 761], double=[657, 719], nullable=[663, 668])
    assert len(result) == 44 and sum(map(len, result.values())) == 50
    return result


def load_cases():
    rows = json.loads((FIXTURES / "synthetic.json").read_text())
    sources = [json.loads(line) for line in (FIXTURES / "concrete.jsonl").read_text().splitlines()]
    for population in (rows, sources):
        assert len(population) == len({r["id"] for r in population}) == len({r["sql"] for r in population}) == 50
    assert Counter(r["operator_kind"] for r in rows) == {"key": 20, "any": 15, "all": 15}
    for row in rows:
        assert row["source_kind"] == "synthetic" and len(row["output_columns"]) == 1
        column = row["output_columns"][0]
        assert column["name"] == "v" and column["type"] == "bool" and type(column["nullable"]) is bool
        assert row["postgres_type"] == row["postgres_display_type"] == "boolean"
        assert row["expected_value"] in ("true", "false", None)
        assert type(row["expected_sql_null"]) is bool
        assert row["expected_sql_null"] == (row["expected_value"] is None)
        assert not row["expected_sql_null"] or column["nullable"]
        assert row["sqlite_supported"] is False
        uses = parameters(row["sql"], "postgres")
        # SQLite excludes this operator family; its lexical '?' marker rules
        # are intentionally different, so no SQLite binding equivalence is claimed.
        assert row["sqlite_input"] == row["sql"].replace("$", "?")
        assert {slot for _, slot in uses} == set(range(1, len(row["parameter_values"]) + 1))
        assert len([t for t in row["parameter_types"].split(",") if t]) == len(row["parameter_values"])
        # These explicit native templates were authored independently of the
        # observer, including marker/operator adjacency and repeated $n uses.
        assert question_parameters(row["sql"]) == row["postgres_input"], row["id"]
    registry = source_registry()
    assert all(type(r["observed_syntax"]["source_free"]) is bool for r in sources)
    assert {r["id"] for r in sources if r["observed_syntax"]["source_free"]} == registry.keys()
    return rows, sources


def operator_script():
    signatures = json.loads((FIXTURES / "function_signatures.json").read_text())
    fields = ("operator", "left", "right", "output", "function")
    wanted = {
        ("?", "jsonb", "text", "boolean", "jsonb_exists"),
        ("?|", "jsonb", "text[]", "boolean", "jsonb_exists_any"),
        ("?&", "jsonb", "text[]", "boolean", "jsonb_exists_all"),
    }
    assert len(signatures) == 3 and {tuple(r[k] for k in fields) for r in signatures} == wanted
    # This fourth declaration explains why unknown ?| unknown is ambiguous.
    observations = [*signatures, {"operator": "?|", "left": "point", "right": "point",
                                  "output": "boolean", "function": "point_vert"}]
    commands, expected = [], []
    for index, record in enumerate(observations):
        operator, left, right, output, function = map(sql_literal, (record[k] for k in fields))
        commands.append(
            f"SELECT {index}, EXISTS(SELECT FROM pg_catalog.pg_operator o "
            "JOIN pg_catalog.pg_proc p ON p.oid=o.oprcode "
            f"WHERE o.oprnamespace='pg_catalog'::regnamespace AND o.oprname={operator} "
            f"AND o.oprleft={left}::regtype AND o.oprright={right}::regtype "
            f"AND o.oprresult={output}::regtype AND p.prorettype={output}::regtype "
            f"AND p.proname={function} AND p.pronamespace='pg_catalog'::regnamespace "
            f"AND p.proargtypes[0]={left}::regtype AND p.proargtypes[1]={right}::regtype "
            "AND p.proisstrict AND NOT p.proretset AND p.pronargs=2 "
            "AND p.provariadic=0 AND p.provolatile='i' AND p.prokind='f');")
        expected.append(f"{index}|t")
    return "\n".join(commands), expected


def reject_sqlite(case):
    result = invoke(["--render-assurance", "sqlite"], stdin=case["sqlite_input"])
    report = json.loads(result.stdout)
    # Existing SQLite input boundaries occur before operator admissibility:
    # JSON extraction (case20), ARRAY constructors and PostgreSQL array types.
    # The other 25 cases reach the explicit JSONB existence exclusion.
    parse_excluded = case["shape"] == "nested-extraction" or (
        case["operator_kind"] != "key" and case["shape"] not in (
            "unknown-key-array", "anonymous", "nullable-binding"))
    expected = (1, "invalid", "input.parse") if parse_excluded else (
        3, "unsupported", "coverage.sqlite.json-existence")
    assert (result.returncode, report["status"], report["diagnostic"]["code"]) == expected, report
    assert report["evidence"] == "none", report
    assert not ({"sql", "parameterMap", "theorems"} & report.keys()), report


def runtime_cases():
    inputs = [
        ("CAST($1 AS JSONB) ? 'a'", "text", "bad json", "22P02"),
        ("CAST($1 AS JSONB) ?| ARRAY['a']", "text", r'{"a":"\u0000"}', "22P05"),
        ("'{}'::JSONB ?& CAST($1 AS TEXT[])", "text", "bad array", "22P02"),
        ("'{}'::JSONB ?| CAST($1 AS TEXT[])", "text", "[1:2]={a}", "22P02"),
        ("'{}'::JSONB ? CAST(1 / $1 AS TEXT)", "int", 0, "22012"),
    ]
    return [{
        "sql": "SELECT " + expression + " AS v;", "parameter_types": types,
        "parameter_values": [value], "sqlstate": state,
        "output_columns": [{"name": "v", "type": "bool", "nullable": False}],
    } for expression, types, value, state in inputs]


def label_cases():
    return [{
        "sql": "SELECT " + expression + ";", "parameter_types": "", "parameter_values": [],
        "output_columns": [{"name": name, "type": type_, "nullable": nullable}],
        "postgres_display_type": "boolean" if type_ == "bool" else "text",
    } for expression, name, type_, nullable in (
        ("'{}'::JSONB ? 'a'", "?column?", "bool", False),
        ("'{}'::JSONB ?| ARRAY['a']", "?column?", "bool", False),
        ("'{}' ?& '{}'", "?column?", "bool", False),
        ("NULL::JSONB ? 'a'", "?column?", "bool", True),
        ("'{}'::JSONB ?& NULL", "?column?", "bool", True),
        ("CAST('{}'::JSONB ? 'a' AS BOOLEAN)", "bool", "bool", False),
        ("CASE WHEN TRUE THEN '{}'::JSONB ? 'a' ELSE TRUE END", "case", "bool", False),
        ("'{}'::JSONB ? 'a' || 'suffix'", "?column?", "text", False),
        ("""'{}'::JSONB || '{"a":1}'::JSONB ? 'a'""", "?column?", "bool", False),
        ("'{}'::JSONB ? ('a' || 'b')", "?column?", "bool", False),
    )]


def analysis_boundaries():
    rows = []
    for operator, key in (("?", "'a'"), ("?|", "ARRAY['a']"), ("?&", "ARRAY['a']")):
        rows += [(f"SELECT {left} {operator} {key}", "invalid", "42883")
                 for left in ("'{}'::JSON", "'{}'::TEXT", "1", "TRUE")]
        rows += [(f"SELECT '{{}}'::JSONB {operator} {right}", "invalid", "42883")
                 for right in ("1", "TRUE", "ARRAY[1]")]
    rows += [(f"SELECT {left} ?| {right}", "invalid", "42725")
             for left in ("'{}'", "NULL") for right in ("'{}'", "NULL")]
    rows += [
        ("SELECT '{}' ? 'a'", "valid", "00000"),
        ("SELECT '{}' ?& '{}'", "valid", "00000"),
        ("SELECT NULL ? 'a'", "valid", "00000"),
        ("SELECT NULL ?& NULL", "valid", "00000"),
        ("SELECT '{}' ?| ARRAY['a']", "valid", "00000"),
        ("SELECT '{}'::JSONB ?| NULL", "valid", "00000"),
        ("SELECT '{}'::JSONB ?1", "invalid", "42883"),
    ]
    return rows


def boundary_script():
    body = ("BEGIN EXECUTE 'PREPARE existence_boundary AS ' || query; "
            "DEALLOCATE existence_boundary; RETURN '00000'; "
            "EXCEPTION WHEN OTHERS THEN RETURN SQLSTATE; END;")
    commands = ["BEGIN;", "CREATE FUNCTION pg_temp.existence_analysis(query TEXT) "
                "RETURNS TEXT LANGUAGE plpgsql AS " + sql_literal(body) + ";"]
    commands += ["SELECT pg_temp.existence_analysis(" + sql_literal(sql) + ");"
                 for sql, _, _ in analysis_boundaries()]
    commands.append("ROLLBACK;")
    return "\n".join(commands), [state for _, _, state in analysis_boundaries()]


def boundaries():
    for sql, status, _ in analysis_boundaries():
        assert_report(["--assurance", "contract", sql], status, "contract")
    unsupported = [
        "SELECT unknown_function() ?& ARRAY['a']",
    ]
    promoted = [
        ("SELECT (SELECT '{}'::JSONB) ? 'a'", (('?column?', 'bool', True),)),
    ]
    for sql, columns in promoted:
        assert_report(["--assurance", "contract", sql], "valid", "contract", columns)
    for sql in unsupported:
        assert_report(["--assurance", "contract", sql], "unsupported", "contract")
    malformed = [
        "SELECT '{}'::JSONB ?", "SELECT ?| ARRAY['a']", "SELECT ?& ARRAY['a']",
        "SELECT '{}'::JSONB ?- 'a'", "SELECT '{}'::JSONB ?! 'a'",
        "SELECT '{}'::JSONB ?|| 'a'", "SELECT '{}'::JSONB ?&& ARRAY['a']",
        "SELECT ?1", "SELECT ?::JSONB ? $1", "SELECT $1 ? ?",
    ]
    for sql in malformed:
        result = invoke(["--render-assurance", "identity"], stdin=sql)
        report = json.loads(result.stdout)
        assert (result.returncode, report["status"], report["diagnostic"]["code"]) == (
            1, "invalid", "input.parse"), (sql, report)
    assert_report(["--assurance", "checked", "SELECT '{}'::JSONB ? 'a'"], "rejected", "checked")
    return len(analysis_boundaries()) + len(unsupported) + len(malformed) + 1 + len(promoted)


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
        rendered = replay("postgres", row["sql"])["sql"]
        assert question_parameters(rendered) == rendered
        canonical.append(rendered)
        reject_sqlite(row)
    registry = source_registry()
    for source in sources:
        if source["id"] in registry:
            assert_report(["--assurance", "contract", source["sql"]], "valid", "contract",
                          registry[source["id"]])
        for profile in ("identity", "postgres"):
            replay(profile, source["sql"])
    errors, labels = runtime_cases(), label_cases()
    error_rendered, label_rendered = [], []
    for population, rendered in ((errors, error_rendered), (labels, label_rendered)):
        for case in population:
            validity(case)
            rendered.append(replay("postgres", case["sql"])["sql"])
    boundary_count = boundaries()
    values_sql, values = database_script(rows, canonical)
    null_sql, nulls = null_script(rows, canonical)
    metadata_sql, metadata = describe_script(rows + labels, canonical + label_rendered)
    errors_sql, error_states = error_script(errors, error_rendered)
    operators_sql, operators = operator_script()
    analysis_sql, analysis_states = boundary_script()
    with connection(args) as psql:
        for script, expected in ((values_sql, values), (null_sql, nulls), (errors_sql, error_states)):
            result = run([*psql, "-X", "-q", "-v", "ON_ERROR_STOP=1"], input=script, timeout=120)
            validate_results(parse_results(result.stdout), expected)
        for script, expected in ((metadata_sql, metadata), (operators_sql, operators), (analysis_sql, analysis_states)):
            result = run([*psql, "-X", "-qAt", "-v", "ON_ERROR_STOP=1"], input=script, timeout=120)
            assert result.stdout.splitlines() == expected, (result.stdout.splitlines(), expected)
        version = run([*psql, "-X", "-At", "-c", "SHOW server_version;"]).stdout.strip()
    print("PASS: 50 synthetic full-query certificates; 50 source renderings and 44 closed-registry source certificates")
    print(f"PASS: {boundary_count} boundaries; SQLite: 25 operator exclusions and 25 earlier input boundaries")
    print(f"PASS: PostgreSQL {version}: {len(values)} value/OID observations, {len(nulls)} SQL NULL observations, "
          f"{len(metadata)} exact descriptors, {len(error_states)} expected errors")
    print(f"PASS: {len(operators)} native declarations including POINT ambiguity; {len(analysis_states)} analysis outcomes")
    print("Scope: exact JSONB signatures and finite authored executions; concrete source SQL is never executed.")


if __name__ == "__main__":
    main()
