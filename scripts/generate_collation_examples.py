#!/usr/bin/env python3
"""Authored COLLATE cases with explicit catalog declarations and row expectations."""
import argparse
import json
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
FIXTURES = ROOT / "fixtures/collations"
STATES = ("empty", "words_only", "labels_only", "both")
DATA = {"words": [["a"], ["b"], ["q"]], "labels": [["b"], ["b"], ["z"]]}
NATIVE = {
    "text": ("TEXT", "text"), "name": ("NAME", "name"), "int32": ("INTEGER", "integer"),
    "varchar(3)": ("VARCHAR(3)", "character varying(3)"), "char(3)": ("CHAR(3)", "character(3)"),
    "numeric(6,2)": ("NUMERIC(6,2)", "numeric(6,2)"),
    "double precision": ("DOUBLE PRECISION", "double precision"), "text[]": ("TEXT[]", "text[]"),
}

# Earlier SQLite parser/rendering boundaries take precedence over COLLATE.
# These are fixed registrations for the authored syntax, not checker output.
SQLITE_PARSE_SHAPES = frozenset({
    "substring", "left", "array-element", "array-result", "array-index", "array-slice",
})
SQLITE_FUNCTION_SHAPES = frozenset({"greatest", "least", "function-input", "variadic-function"})


def sqlite_boundary(shape):
    if shape in SQLITE_PARSE_SHAPES:
        return "parse_invalid", "input.parse"
    if shape in SQLITE_FUNCTION_SHAPES:
        return "render_unsupported", "coverage.sqlite.scalar-function-signatures"
    if shape == "recursive-name":
        return "render_unsupported", "coverage.sqlite.PostgreSQL-type"
    return "render_unsupported", "coverage.sqlite.collation"


def population(state):
    assert state in STATES
    return {table: rows if state in ("both", table + "_only") else [] for table, rows in DATA.items()}


def schema():
    def entry(id_, schema_, name):
        return {"id": id_, "schema": schema_, "name": name, "encoding": None,
                "deterministic": True, "exposeUnqualified": True}
    return {
        "tables": [
            {"name": "words", "schema": "public", "exposeUnqualified": True,
             "columns": [{"name": "value", "type": "text", "nullable": False}],
             "columnCollations": [{"column": "value", "collation": "C"}]},
            {"name": "labels", "schema": "public", "exposeUnqualified": True,
             "columns": [{"name": "value", "type": "text", "nullable": False}]},
        ],
        "collations": {"encoding": "UTF8", "entries": [
            entry("default", "pg_catalog", "default"),
            entry("C", "pg_catalog", "C"),
            entry("POSIX", "pg_catalog", "POSIX"),
            entry("custom:c_order", "fixture", "c_order"),
        ]},
    }


def column(type_="text", collation="C", nullable=False, name="v"):
    native, display = NATIVE[type_]
    return {"name": name, "type": type_, "nullable": nullable, "collation": collation,
            "postgres_type": native, "postgres_display_type": display}


def cases(data=DATA):
    result = []

    def add(shape, sql, rows, *, type_="text", collation="C", nullable=False,
            types="", values=None, ordered=False):
        sqlite_mode, sqlite_diagnostic = sqlite_boundary(shape)
        result.append({
            "id": f"collation-{len(result)+1:03d}", "source_kind": "synthetic", "shape": shape,
            "sql": sql + ";", "sqlite_sql": sql.replace("$", "?") + ";",
            "catalogFile": "fixtures/collations/schema.json", "parameter_types": types,
            "parameter_values": [] if values is None else values,
            "output_columns": [column(type_, collation, nullable)],
            "expected_rows": rows, "ordered": ordered,
            "sqlite_mode": sqlite_mode, "sqlite_diagnostic": sqlite_diagnostic,
        })

    def expression(shape, expr, value, **options):
        add(shape, f"SELECT {expr} AS v", [[value]], **options)

    expression("literal-c", "'a' COLLATE \"C\"", "a")
    expression("literal-posix", "'a' COLLATE \"POSIX\"", "a", collation="POSIX")
    expression("outer-posix-overrides", "('a' COLLATE \"C\") COLLATE \"POSIX\"", "a", collation="POSIX")
    expression("outer-c-overrides", "('a' COLLATE \"POSIX\") COLLATE \"C\"", "a")
    expression("qualified-c", "'a' COLLATE pg_catalog.\"C\"", "a")
    expression("quoted-qualified-posix", "'a' COLLATE \"pg_catalog\".\"POSIX\"", "a", collation="POSIX")
    expression("typed-text", "CAST('a' AS TEXT) COLLATE \"C\"", "a")
    expression("varchar-modifier", "CAST('a' AS VARCHAR(3)) COLLATE \"C\"", "a", type_="varchar(3)")
    expression("char-modifier", "CAST('a' AS CHAR(3)) COLLATE \"C\"", "a  ", type_="char(3)")
    expression("name-posix", "CAST('a' AS NAME) COLLATE \"POSIX\"", "a", type_="name", collation="POSIX")
    expression("override-name-derived-text", "CAST(CAST('a' AS NAME) AS TEXT) COLLATE \"default\"",
               "a", collation="default")
    expression("unknown-to-integer", "CAST('1' COLLATE \"C\" AS INTEGER)", 1, type_="int32", collation=None)
    expression("known-text-to-integer", "CAST(CAST(CAST('1' AS NAME) AS TEXT) COLLATE \"C\" AS INTEGER)",
               1, type_="int32", collation=None)
    expression("unknown-to-numeric-modifier", "CAST('1.25' COLLATE \"C\" AS NUMERIC(6,2))",
               "1.25", type_="numeric(6,2)", collation=None)
    expression("unknown-to-float", "CAST('1.5' COLLATE \"C\" AS DOUBLE PRECISION)",
               "1.5", type_="double precision", collation=None)
    expression("unknown-null", "NULL COLLATE \"C\"", None, nullable=True)
    expression("typed-null", "CAST(NULL AS TEXT) COLLATE \"POSIX\"", None, nullable=True, collation="POSIX")
    expression("case-one-explicit-result", "CASE WHEN TRUE THEN 'x' COLLATE \"C\" ELSE 'y' END", "x")
    expression("case-condition-separate", "CASE WHEN 'a' COLLATE \"POSIX\"='a' "
               "THEN 'x' COLLATE \"C\" ELSE 'y' END", "x")
    expression("coalesce-explicit-null", "COALESCE(NULL COLLATE \"C\",'a')", "a")
    expression("nullif", "NULLIF('a' COLLATE \"C\",'b')", "a", nullable=True)
    expression("greatest", "GREATEST('a' COLLATE \"C\",'b')", "b")
    expression("least", "LEAST('a' COLLATE \"C\",'b')", "a")
    expression("function-input", "LOWER('X' COLLATE \"C\")", "x")
    expression("variadic-function", "CONCAT('a' COLLATE \"C\",'b')", "ab")
    expression("substring", "SUBSTRING('abc' COLLATE \"C\" FROM 2 FOR 1)", "b")
    expression("left", "LEFT('abc' COLLATE \"C\",2)", "ab")
    expression("concatenation", "'a' COLLATE \"C\" || 'b'", "ab")
    expression("array-element", "ARRAY['a' COLLATE \"C\",'b']", "{a,b}", type_="text[]")
    expression("array-result", "ARRAY['a','b'] COLLATE \"POSIX\"", "{a,b}", type_="text[]", collation="POSIX")
    expression("array-index", "(ARRAY['a' COLLATE \"C\",'b'])[1]", "a", nullable=True)
    expression("array-slice", "(ARRAY['a' COLLATE \"C\",'b'])[1:1]", "{a}", type_="text[]", nullable=True)
    add("derived-boundary", "SELECT v FROM (SELECT 'a' COLLATE \"C\" AS v) d", [["a"]])
    add("cte-boundary", "WITH c(v) AS (SELECT 'a' COLLATE \"C\") SELECT v FROM c", [["a"]])
    add("union-all", "SELECT 'a' COLLATE \"C\" AS v UNION ALL SELECT 'b'", [["a"], ["b"]])
    add("union-distinct", "SELECT 'a' COLLATE \"C\" AS v UNION SELECT 'b'", [["a"], ["b"]])
    add("intersect", "SELECT 'a' COLLATE \"C\" AS v INTERSECT SELECT 'a'", [["a"]])
    add("except", "SELECT 'a' COLLATE \"C\" AS v EXCEPT SELECT 'b'", [["a"]])
    add("override-indeterminate-set-result", "SELECT v COLLATE \"default\" AS v FROM "
        "(SELECT v FROM (SELECT 'a' COLLATE \"C\" AS v) a UNION ALL "
        "SELECT v FROM (SELECT 'b' COLLATE \"POSIX\" AS v) b) d",
        [["a"], ["b"]], collation="default")
    add("ordering-does-not-change-output", "SELECT v FROM "
        "(SELECT 'b' AS v UNION ALL SELECT 'A' UNION ALL SELECT 'a') d ORDER BY v COLLATE \"C\"",
        [["A"], ["a"], ["b"]], collation="default", ordered=True)
    expression("typed-parameter", "$1 COLLATE \"C\"", "z", types="text", values=["z"])
    expression("numbered-parameter-order", "$2 COLLATE \"C\" || $1 COLLATE \"C\"",
               "ab", types="text,text", values=["b", "a"])
    expression("nullable-anonymous-parameters", "COALESCE(? COLLATE \"C\",? COLLATE \"C\")",
               "x", types="text?,text", values=[None, "x"])
    add("recursive-text", "WITH RECURSIVE t(v) AS (SELECT 'a' COLLATE \"C\" UNION ALL "
        "SELECT v||'x' FROM t WHERE LENGTH(v)<3) SELECT v FROM t",
        [["a"], ["ax"], ["axx"]], nullable=True)
    add("recursive-name", "WITH RECURSIVE t(v) AS (SELECT CAST('a' AS NAME) UNION ALL "
        "SELECT CAST(v||'x' AS NAME) COLLATE \"C\" FROM t WHERE LENGTH(v)<3) SELECT v FROM t",
        [["a"], ["ax"], ["axx"]], type_="name", nullable=True)
    add("base-override", "SELECT value COLLATE \"POSIX\" AS v FROM words",
        data["words"], collation="POSIX")
    add("qualified-custom-object", "SELECT value COLLATE fixture.c_order AS v FROM words",
        data["words"], collation="custom:c_order")
    add("using-join", "SELECT value COLLATE \"C\" AS v FROM words JOIN labels USING(value)",
        [[a] for (a,) in data["words"] for (b,) in data["labels"] if a == b])
    add("nullable-side-custom-object", "SELECT l.value COLLATE c_order AS v FROM words w "
        "LEFT JOIN labels l ON w.value=l.value",
        [[v] for (a,) in data["words"] for v in ([b for (b,) in data["labels"] if a == b] or [None])],
        collation="custom:c_order", nullable=True)
    add("recursive-base-collation", "WITH RECURSIVE t(v) AS "
        "(SELECT value COLLATE \"C\" FROM words UNION ALL "
        "SELECT v||'x' FROM t WHERE LENGTH(v)<2) SELECT v FROM t",
        [*data["words"], *[[value + "x"] for (value,) in data["words"] if len(value) < 2]], nullable=True)
    assert len(result) == len({r["shape"] for r in result}) == len({r["sql"] for r in result}) == 50
    return result


def all_cases():
    rows = cases()
    for row in rows:
        row["expected_rows_by_state"] = {}
    for state in STATES:
        for row, modeled in zip(rows, cases(population(state))):
            assert row["id"] == modeled["id"] and row["output_columns"] == modeled["output_columns"]
            row["expected_rows_by_state"][state] = modeled["expected_rows"]
    return rows


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--check", action="store_true")
    args = parser.parse_args()
    for name, value in (("synthetic.json", all_cases()), ("schema.json", schema())):
        path = FIXTURES / name
        content = json.dumps(value, indent=2) + "\n"
        if args.check:
            assert path.read_text() == content, f"stale {path}"
        else:
            FIXTURES.mkdir(parents=True, exist_ok=True)
            path.write_text(content)
    print("PASS: 50 authored COLLATE queries with exact declared identities and four data populations")


if __name__ == "__main__":
    main()
