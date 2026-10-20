#!/usr/bin/env python3
"""Fifty authored CTE queries with independent row and descriptor expectations."""
import argparse
import json
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
FIXTURES = ROOT / "fixtures/cte_contract"
STATES = ("empty", "items_only", "labels_only", "both")
TABLES = {
    "items": [("id", "int", False), ("score", "int", True), ("name", "text", False)],
    "labels": [("id", "int", False), ("category", "text", False)],
}
DATA = {
    "items": [[1, 10, "Ada"], [2, None, "Bea"], [3, 10, "Cy"], [4, 40, "Di"]],
    "labels": [[1, "A"], [1, "B"], [3, "C"], [5, "E"]],
}
NATIVE = {
    "int32": ("INTEGER", "integer"), "text": ("TEXT", "text"),
    "bool": ("BOOLEAN", "boolean"), "varchar(3)": ("VARCHAR(3)", "character varying(3)"),
    "numeric(6,2)": ("NUMERIC(6,2)", "numeric(6,2)"),
    "integer[]": ("INTEGER[]", "integer[]"),
}


def population(state):
    assert state in STATES
    return {name: rows if state in ("both", name + "_only") else [] for name, rows in DATA.items()}


def schema():
    return {"tables": [
        {"name": name, "schema": "public", "exposeUnqualified": True,
         "columns": [{"name": field, "type": type_, "nullable": nullable}
                     for field, type_, nullable in columns]}
        for name, columns in TABLES.items()
    ]}


def col(name, type_="int32", nullable=False):
    native, display = NATIVE[type_]
    return {"name": name, "type": type_, "nullable": nullable,
            "postgres_type": native, "postgres_display_type": display}


def cases(data=DATA):
    result = []

    def add(shape, sql, output, rows, *, types="", values=None, sqlite_mode="execute",
            sqlite_error=None, sqlite_code=None, sqlite_names=None, sqlite_rows=None):
        result.append({
            "id": f"cte-{len(result)+1:02d}-{shape}", "source_kind": "synthetic",
            "shape": shape, "sql": sql + ";", "sqlite_sql": sql.replace("$", "?") + ";",
            "catalogFile": "fixtures/cte_contract/schema.json",
            "parameter_types": types, "parameter_values": values or [],
            "output_columns": output, "expected_rows": rows,
            "sqlite_mode": sqlite_mode, "sqlite_error": sqlite_error,
            "sqlite_diagnostic": sqlite_code,
            "sqlite_output_names": sqlite_names or [c["name"] for c in output],
            "sqlite_expected_rows": rows if sqlite_rows is None else sqlite_rows,
        })

    add("integer", "WITH c AS (SELECT 1 AS x) SELECT x FROM c", [col("x")], [[1]])
    add("unknown-text", "WITH c AS (SELECT 'abc' AS x) SELECT x || x AS doubled FROM c",
        [col("doubled", "text")], [["abcabc"]])
    add("unknown-null", "WITH c AS (SELECT NULL AS x) SELECT x FROM c",
        [col("x", "text", True)], [[None]])
    add("typed-null", "WITH c AS (SELECT CAST(NULL AS INTEGER) AS x) SELECT x FROM c",
        [col("x", nullable=True)], [[None]])
    add("full-aliases", "WITH c(a,b) AS (SELECT 1 AS x, 'z' AS y) SELECT c.* FROM c",
        [col("a"), col("b", "text")], [[1, "z"]])
    add("prefix-alias", "WITH c(a) AS (SELECT 1 AS x, 'z' AS y) SELECT a,y FROM c",
        [col("a"), col("y", "text")], [[1, "z"]], sqlite_mode="analysis_error",
        sqlite_error="table c has 2 values for 1 columns")
    add("duplicate-labels", "WITH c AS (SELECT 1 AS x, 2 AS x) SELECT * FROM c",
        [col("x"), col("x")], [[1, 2]], sqlite_names=["x", "x:1"])
    add("duplicate-aliases", "WITH c(x,x) AS (SELECT 1, 2) SELECT c.* FROM c",
        [col("x"), col("x")], [[1, 2]], sqlite_names=["x", "x:1"])
    add("unused-parameter", "WITH unused AS (SELECT ? AS x) SELECT ? AS y",
        [col("y")], [[9]], types="int,int", values=[7, 9])
    add("repeated-reference", "WITH c AS (SELECT ? AS x) SELECT a.x,b.x FROM c a CROSS JOIN c b",
        [col("x"), col("x")], [[7, 7]], types="int", values=[7])
    add("sequential", "WITH a AS (SELECT 1 AS x), b AS (SELECT x+1 AS y FROM a) SELECT y FROM b",
        [col("y")], [[2]])
    add("three-siblings", "WITH a AS (SELECT 1 AS x), b AS (SELECT x+1 AS x FROM a), "
        "c AS (SELECT x+1 AS x FROM b) SELECT x FROM c", [col("x")], [[3]])
    add("inherited-derived", "WITH c AS (SELECT 1 AS x) SELECT d.x FROM (SELECT x FROM c) d",
        [col("x")], [[1]])
    add("nested-shadow", "WITH c AS (SELECT 1 AS x) SELECT d.x FROM "
        "(WITH c AS (SELECT 2 AS x) SELECT x FROM c) d", [col("x")], [[2]])
    add("own-body-outer", "WITH c AS (SELECT 1 AS x) SELECT d.x FROM "
        "(WITH c AS (SELECT x+1 AS x FROM c) SELECT x FROM c) d",
        [col("x")], [[2]], sqlite_mode="analysis_error", sqlite_error="circular reference: c")
    add("later-name-outer", "WITH c AS (SELECT 1 AS x) SELECT d.x FROM "
        "(WITH a AS (SELECT x+1 AS x FROM c), c AS (SELECT 2 AS x) SELECT x FROM a) d",
        [col("x")], [[2]], sqlite_rows=[[3]])
    add("inner-with", "WITH c AS (WITH a AS (SELECT 1 AS x) SELECT x+1 AS x FROM a) SELECT x FROM c",
        [col("x")], [[2]])
    add("quoted-dot", 'WITH "c.dot" AS (SELECT 1 AS x) SELECT "c.dot".x FROM "c.dot"',
        [col("x")], [[1]])
    add("reference-alias", "WITH c AS (SELECT 1 AS x, 'z' AS y) SELECT d.a,d.y FROM c AS d(a)",
        [col("a"), col("y", "text")], [[1, "z"]], sqlite_mode="render_unsupported",
        sqlite_code="coverage.sqlite.relation-column-aliases")
    add("ordered-body", "WITH c AS (SELECT 1 AS x ORDER BY x LIMIT 1 OFFSET 0) SELECT x FROM c",
        [col("x")], [[1]])
    add("empty-body", "WITH c AS (SELECT 1 AS x WHERE FALSE) SELECT x FROM c", [col("x")], [])
    add("unknown-null-test", "WITH c AS (SELECT NULL AS x) SELECT x IS NULL AS missing FROM c",
        [col("missing", "bool")], [[True]])
    add("null-distinct", "WITH c AS (SELECT CAST(NULL AS INTEGER) AS x) "
        "SELECT x IS NOT DISTINCT FROM NULL AS same FROM c", [col("same", "bool")], [[True]])
    add("lexical-parameters", "WITH unused AS (SELECT ? AS x), c AS (SELECT ? AS x) "
        "SELECT ? AS marker,c.x FROM c WHERE c.x > ? ORDER BY c.x LIMIT ? OFFSET ?",
        [col("marker"), col("x")], [[9, 7]], types="int,int,int,int,int,int",
        values=[100, 7, 9, 0, 1, 0])
    add("reordered-numbered", "WITH a AS (SELECT $2 AS x), b AS (SELECT $1 AS y) "
        "SELECT x,y FROM a CROSS JOIN b", [col("x"), col("y")], [[7, 9]],
        types="int,int", values=[9, 7])
    add("varchar-modifier", "WITH c AS (SELECT CAST('abcd' AS VARCHAR(3)) AS x) SELECT x FROM c",
        [col("x", "varchar(3)")], [["abc"]], sqlite_rows=[["abcd"]])
    add("numeric-modifier", "WITH c AS (SELECT CAST(1.234 AS NUMERIC(6,2)) AS x) SELECT x FROM c",
        [col("x", "numeric(6,2)")], [["1.23"]], sqlite_rows=[[1.234]])
    add("array-null-element", "WITH c AS (SELECT ARRAY[1,NULL] AS x) SELECT x FROM c",
        [col("x", "integer[]")], [["{1,NULL}"]], sqlite_mode="input_excluded",
        sqlite_code="input.parse")
    add("cte-only-lock", "WITH c AS (SELECT DISTINCT 1 AS x) SELECT x FROM c FOR UPDATE",
        [col("x")], [[1]], sqlite_mode="input_excluded", sqlite_code="input.parse")
    add("nullable-cte-lock", "WITH a AS (SELECT 1 AS x), b AS (SELECT 2 AS y) "
        "SELECT a.x,b.y FROM a LEFT JOIN b ON FALSE FOR SHARE",
        [col("x"), col("y", nullable=True)], [[1, None]], sqlite_mode="input_excluded",
        sqlite_code="input.parse")
    assert len(result) == 30

    for minimum in (0, 3):
        items = [r for r in data["items"] if r[0] >= minimum]
        body = f"SELECT id,score,name FROM items WHERE id >= {minimum}"
        output = [col("id"), col("score", nullable=True), col("name", "text")]
        add(f"base-{minimum}", f"WITH c AS ({body}) SELECT c.* FROM c", output, items)
        add(f"coalesced-chain-{minimum}", f"WITH c AS ({body}), "
            "d AS (SELECT id,COALESCE(score,0) AS points FROM c) SELECT id,points FROM d",
            [col("id"), col("points")], [[i, score or 0] for i, score, _ in items])
        add(f"base-shadow-{minimum}", f"WITH items AS ({body}) SELECT * FROM items", output, items,
            sqlite_mode="analysis_error", sqlite_error="circular reference: items")
        add(f"qualified-bypass-{minimum}", "WITH items AS (SELECT 99 AS id) "
            f"SELECT id,score,name FROM public.items WHERE id >= {minimum}", output, items,
            sqlite_mode="render_unsupported", sqlite_code="coverage.sqlite.schema-qualification")
        joined = [[i, category] for i, _, _ in items
                  for category in ([row[1] for row in data["labels"] if row[0] == i] or [None])]
        add(f"left-on-{minimum}", f"WITH c AS ({body}) SELECT c.id,l.category FROM c "
            "LEFT JOIN labels l ON c.id=l.id",
            [col("id"), col("category", "text", True)], joined)
        add(f"natural-{minimum}", f"WITH c AS ({body}) SELECT c.*,l.category FROM c NATURAL LEFT JOIN labels l",
            [*output, col("category", "text", True)],
            [[i, score, name, category] for i, score, name in items
             for category in ([row[1] for row in data["labels"] if row[0] == i] or [None])])
        full = [[i, i, category] for i, _, _ in items
                for category in ([row[1] for row in data["labels"] if row[0] == i] or [None])]
        full += [[i, None, category] for i, category in data["labels"] if not any(r[0] == i for r in items)]
        add(f"full-using-{minimum}", f"WITH c AS ({body}) SELECT id AS merged_id,c.id AS original_id,l.category "
            "FROM c FULL JOIN labels l USING(id)",
            [col("merged_id"), col("original_id", nullable=True), col("category", "text", True)], full)
        scores = sorted({row[1] for row in items}, key=lambda v: (v is None, v))[:2]
        add(f"distinct-page-{minimum}", "WITH c AS "
            f"(SELECT DISTINCT score FROM items WHERE id >= {minimum} ORDER BY score NULLS LAST LIMIT 2) "
            "SELECT score FROM c WHERE score IS NOT NULL", [col("score", nullable=True)],
            [[score] for score in scores if score is not None])
        add(f"body-lock-{minimum}", f"WITH c AS ({body} FOR KEY SHARE) SELECT id FROM c",
            [col("id")], [[i] for i, _, _ in items], sqlite_mode="input_excluded",
            sqlite_code="input.parse")
        add(f"base-target-lock-{minimum}", f"WITH c AS ({body}) SELECT c.id,l.category FROM c "
            "JOIN labels l ON c.id=l.id FOR UPDATE OF l",
            [col("id"), col("category", "text")],
            [[i, category] for i, _, _ in items for key, category in data["labels"] if key == i],
            sqlite_mode="input_excluded", sqlite_code="input.parse")
    assert len(result) == len({row["sql"] for row in result}) == 50
    return result


def all_cases():
    result = cases()
    for row in result:
        row["expected_rows_by_state"] = {}
        row["sqlite_expected_rows_by_state"] = {}
    for state in STATES:
        for row, modeled in zip(result, cases(population(state))):
            assert row["id"] == modeled["id"] and row["output_columns"] == modeled["output_columns"]
            row["expected_rows_by_state"][state] = modeled["expected_rows"]
            row["sqlite_expected_rows_by_state"][state] = modeled["sqlite_expected_rows"]
    return result


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--check", action="store_true")
    args = parser.parse_args()
    for name, value in (("synthetic.json", all_cases()), ("schema.json", schema())):
        text = json.dumps(value, indent=2) + "\n"
        path = FIXTURES / name
        if args.check:
            assert path.read_text() == text, f"stale {path}"
        else:
            FIXTURES.mkdir(parents=True, exist_ok=True)
            path.write_text(text)
    print("PASS: 50 authored nonrecursive CTE queries and four independent table populations")


if __name__ == "__main__":
    main()
