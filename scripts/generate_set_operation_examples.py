#!/usr/bin/env python3
"""Fifty independent authored examples for each PostgreSQL set operation."""
import argparse
from collections import Counter
import json
from pathlib import Path

from generate_cte_contract_examples import DATA, STATES, TABLES, population, schema

ROOT = Path(__file__).resolve().parents[1]
FIXTURES = ROOT / "fixtures/set_operations"
FACTORS = ("union", "intersect", "except")
NATIVE = {
    "int32": ("INTEGER", "integer"), "bigint": ("BIGINT", "bigint"),
    "text": ("TEXT", "text"), "bool": ("BOOLEAN", "boolean"),
    "real": ("REAL", "real"), "double precision": ("DOUBLE PRECISION", "double precision"),
    "numeric": ("NUMERIC", "numeric"),
    "numeric(6,2)": ("NUMERIC(6,2)", "numeric(6,2)"),
    "varchar": ("VARCHAR", "character varying"),
    "varchar(3)": ("VARCHAR(3)", "character varying(3)"),
    "char(3)": ("CHAR(3)", "character(3)"),
    "bpchar": ("BPCHAR", "bpchar"),
    "timestamp(2)": ("TIMESTAMP(2)", "timestamp(2) without time zone"),
    "timestamp": ("TIMESTAMP", "timestamp without time zone"),
    "bigint[]": ("BIGINT[]", "bigint[]"),
    "integer[]": ("INTEGER[]", "integer[]"),
}


def col(name="v", type_="int32", nullable=False):
    native, display = NATIVE[type_]
    return {"name": name, "type": type_, "nullable": nullable,
            "postgres_type": native, "postgres_display_type": display}


def combine(factor, all_, left, right):
    """Independent multiset model; NULL values compare equal for set membership."""
    assert factor in FACTORS and type(all_) is bool
    a, b = Counter(map(tuple, left)), Counter(map(tuple, right))
    if factor == "union":
        counts = a + b
    elif factor == "intersect":
        counts = a & b
    else:
        counts = a - b if all_ else Counter({key: 1 for key in a if key not in b})
    if not all_:
        counts = Counter({key: 1 for key in counts})
    return [list(key) for key, count in counts.items() for _ in range(count)]


def cases(data=DATA):
    result = []
    for factor in FACTORS:
        start = len(result)

        def add(shape, left, right, output, lrows, rrows, *, all_=False,
                prefix="", suffix="", types="", values=None, sqlite_mode="execute",
                sqlite_code=None, sqlite_left=None, sqlite_right=None, sqlite_names=None,
                sql=None, rows=None, sqlite_sql=None, sqlite_rows=None, ordered=False,
                sqlite_source_error=None):
            operator = factor.upper() + (" ALL" if all_ else "")
            statement = sql or f"{prefix}{left} {operator} {right}{suffix}"
            wanted = combine(factor, all_, lrows, rrows) if rows is None else rows
            swanted = combine(factor, all_,
                              lrows if sqlite_left is None else sqlite_left,
                              rrows if sqlite_right is None else sqlite_right)
            if all_ and factor != "union" and sqlite_mode != "input_excluded":
                sqlite_mode, sqlite_code = "input_excluded", "input.parse"
            result.append({
                "id": f"set-{factor}-{len(result)-start+1:03d}", "factor": factor,
                "source_kind": "synthetic", "shape": shape, "all": all_,
                "sql": statement + ";", "sqlite_sql": (sqlite_sql or statement).replace("$", "?") + ";",
                "catalogFile": "fixtures/set_operations/schema.json",
                "parameter_types": types, "parameter_values": [] if values is None else values,
                "output_columns": output, "expected_rows": wanted,
                "ordered": ordered, "sqlite_mode": sqlite_mode,
                "sqlite_source_error": sqlite_source_error,
                "sqlite_diagnostic": sqlite_code,
                "sqlite_output_names": sqlite_names or [c["name"] for c in output],
                "sqlite_expected_rows": swanted if sqlite_rows is None else sqlite_rows,
            })

        add("disjoint", "SELECT 1 AS v", "SELECT 2", [col()], [[1]], [[2]])
        add("duplicate-all", "SELECT 1 AS v", "SELECT 1", [col()], [[1]], [[1]], all_=True)
        add("empty-left", "SELECT 1 AS v WHERE FALSE", "SELECT 2", [col()], [], [[2]])
        add("empty-right-all", "SELECT 1 AS v", "SELECT 2 WHERE FALSE", [col()], [[1]], [], all_=True)
        add("unknown-null", "SELECT NULL AS v", "SELECT NULL", [col(type_="text", nullable=True)],
            [[None]], [[None]])
        add("contextual-null", "SELECT NULL AS v", "SELECT 1", [col(nullable=True)],
            [[None]], [[1]], all_=True)
        add("contextual-string", "SELECT '1' AS v", "SELECT 1", [col()], [[1]], [[1]],
            sqlite_left=[["1"]])
        add("unknown-text-all", "SELECT 'a' AS v", "SELECT 'b'", [col(type_="text")],
            [["a"]], [["b"]], all_=True)
        add("boolean", "SELECT TRUE AS v", "SELECT FALSE", [col(type_="bool")],
            [[True]], [[False]], sqlite_left=[[1]], sqlite_right=[[0]])
        add("smallint-integer", "SELECT CAST(1 AS SMALLINT) AS v", "SELECT 2", [col()],
            [[1]], [[2]], all_=True)
        add("integer-bigint", "SELECT 1 AS v", "SELECT CAST(2 AS BIGINT)", [col(type_="bigint")],
            [[1]], [[2]])
        add("integer-numeric", "SELECT 1 AS v", "SELECT 2.5", [col(type_="numeric")],
            [["1"]], [["2.5"]], all_=True, sqlite_left=[[1]], sqlite_right=[[2.5]])
        add("integer-real", "SELECT 1 AS v", "SELECT CAST(2 AS REAL)", [col(type_="real")],
            [["1"]], [["2"]], sqlite_left=[[1]], sqlite_right=[[2.0]])
        add("double-integer", "SELECT CAST(1 AS DOUBLE PRECISION) AS v", "SELECT 2",
            [col(type_="double precision")], [["1"]], [["2"]], all_=True,
            sqlite_left=[[1.0]], sqlite_right=[[2]])
        add("same-varchar-modifier", "SELECT CAST('abcd' AS VARCHAR(3)) AS v",
            "SELECT CAST('xyz' AS VARCHAR(3))", [col(type_="varchar(3)")],
            [["abc"]], [["xyz"]], sqlite_left=[["abcd"]])
        add("different-varchar-modifier", "SELECT CAST('abcd' AS VARCHAR(3)) AS v",
            "SELECT CAST('xy' AS VARCHAR(2))", [col(type_="varchar")],
            [["abc"]], [["xy"]], all_=True, sqlite_left=[["abcd"]])
        add("same-numeric-modifier", "SELECT CAST(1.234 AS NUMERIC(6,2)) AS v",
            "SELECT CAST(2.345 AS NUMERIC(6,2))", [col(type_="numeric(6,2)")],
            [["1.23"]], [["2.35"]], sqlite_left=[[1.234]], sqlite_right=[[2.345]])
        add("different-numeric-modifier", "SELECT CAST(1.234 AS NUMERIC(6,2)) AS v",
            "SELECT CAST(2.345 AS NUMERIC(7,3))", [col(type_="numeric")],
            [["1.23"]], [["2.345"]], all_=True, sqlite_left=[[1.234]], sqlite_right=[[2.345]])
        add("same-timestamp-modifier", "SELECT CAST('2000-01-01 00:00:00.125' AS TIMESTAMP(2)) AS v",
            "SELECT CAST('2000-01-02' AS TIMESTAMP(2))", [col(type_="timestamp(2)")],
            [["2000-01-01 00:00:00.13"]], [["2000-01-02 00:00:00"]],
            sqlite_mode="render_unsupported", sqlite_code="coverage.sqlite.PostgreSQL-type")
        add("date-timestamp", "SELECT CAST('2000-01-01' AS DATE) AS v",
            "SELECT CAST('2000-01-02' AS TIMESTAMP(2))", [col(type_="timestamp")],
            [["2000-01-01 00:00:00"]], [["2000-01-02 00:00:00"]], all_=True,
            sqlite_mode="render_unsupported", sqlite_code="coverage.sqlite.PostgreSQL-type")
        add("array-widening", "SELECT ARRAY[1] AS v", "SELECT ARRAY[CAST(2 AS BIGINT)]",
            [col(type_="bigint[]")], [["{1}"]], [["{2}"]],
            sqlite_mode="input_excluded", sqlite_code="input.parse")
        add("array-contextual-null", "SELECT NULL AS v", "SELECT ARRAY[1,NULL]",
            [col(type_="integer[]", nullable=True)], [[None]], [["{1,NULL}"]], all_=True,
            sqlite_mode="input_excluded", sqlite_code="input.parse")
        add("same-char-modifier", "SELECT CAST('a' AS CHAR(3)) AS v", "SELECT CAST('a  ' AS CHAR(3))",
            [col(type_="char(3)")], [["a  "]], [["a  "]], sqlite_left=[["a"]])
        add("char-text", "SELECT CAST('a' AS CHAR(3)) AS v", "SELECT CAST('b' AS TEXT)",
            [col(type_="bpchar")], [["a  "]], [["b"]], all_=True, sqlite_left=[["a"]])
        add("case-coalesce", "SELECT CASE WHEN TRUE THEN 7 ELSE NULL END AS v",
            "SELECT COALESCE(NULL,7)", [col(nullable=True)], [[7]], [[7]])
        add("left-labels", "SELECT 1 AS x,'a' AS y", "SELECT 2 AS y,'b' AS x",
            [col("x"), col("y", "text")], [[1, "a"]], [[2, "b"]], all_=True)
        add("derived-wildcard", "SELECT d.* FROM (SELECT 1 AS v) d",
            "SELECT d.* FROM (SELECT 1 AS v) d", [col()], [[1]], [[1]])
        add("enclosing-cte", "SELECT x AS v FROM c", "SELECT x+1 FROM c", [col()],
            [[1]], [[2]], all_=True, prefix="WITH c AS (SELECT 1 AS x) ")
        add("sequential-cte", "SELECT x AS v FROM a", "SELECT y FROM b", [col()],
            [[1]], [[2]], prefix="WITH a AS (SELECT 1 AS x), b AS (SELECT x+1 AS y FROM a) ")
        add("branch-local-cte", "(WITH c AS (SELECT 1 AS x) SELECT x AS v FROM c)",
            "(WITH c AS (SELECT 2 AS x) SELECT x FROM c)", [col()], [[1]], [[2]], all_=True,
            sqlite_mode="input_excluded", sqlite_code="input.parse")
        add("cte-shadow", "(WITH c AS (SELECT x+1 AS x FROM c) SELECT x AS v FROM c)",
            "SELECT x FROM c", [col()], [[2]], [[1]], prefix="WITH c AS (SELECT 1 AS x) ",
            sqlite_mode="render_unsupported", sqlite_code="coverage.sqlite.operand-local-clauses")
        operator = factor.upper() + " ALL"
        add("derived-set", "", "", [col()], [[1]], [[1]], all_=True,
            sql=f"SELECT d.v FROM (SELECT 1 AS v {operator} SELECT 1) d")
        nested_right = combine("union", True, [[1]], [[2]])
        add("right-nested", "SELECT 1 AS v", "(SELECT 1 UNION ALL SELECT 2)",
            [col()], [[1]], nested_right,
            sqlite_mode="input_excluded", sqlite_code="input.parse")
        nested_left = combine("except", False, [[1]], [[2]])
        add("left-nested-all", "(SELECT 1 AS v EXCEPT SELECT 2)", "SELECT 1", [col()],
            nested_left, [[1]], all_=True, sqlite_source_error='near "(": syntax error')
        # PostgreSQL INTERSECT binds tighter; the SQLite source intentionally has
        # the same bytes and its independently modeled left association differs.
        pg_rows = (combine("union", False, [[1]], combine("intersect", False, [[2]], [[2]]))
                   if factor == "intersect" else
                   combine(factor, False, combine("union", False, [[1]], [[2]]), [[2]]))
        sqlite_rows = combine(factor, False, combine("union", False, [[1]], [[2]]), [[2]])
        add("precedence", "", "", [col()], [], [],
            sql=f"SELECT 1 AS v UNION SELECT 2 {factor.upper()} SELECT 2",
            rows=pg_rows, sqlite_rows=sqlite_rows)
        add("sort-one-unknown-slot", "(SELECT NULL AS a,NULL AS b ORDER BY a)",
            "SELECT CAST(NULL AS TEXT),1", [col("a", "text", True), col("b", nullable=True)],
            [[None, None]], [[None, 1]], all_=True,
            sqlite_mode="render_unsupported", sqlite_code="coverage.sqlite.operand-local-clauses")
        add("distinct-arm", "SELECT DISTINCT 1 AS v", "SELECT 1", [col()], [[1]], [[1]])
        add("limit-preserves-unknown", "(SELECT NULL AS v LIMIT 1)", "SELECT 1",
            [col(nullable=True)], [[None]], [[1]], all_=True,
            sqlite_mode="render_unsupported", sqlite_code="coverage.sqlite.operand-local-clauses")
        add("expression-sort-preserves-unknown", "(SELECT NULL AS v ORDER BY +1)", "SELECT 1",
            [col(nullable=True)], [[None]], [[1]],
            sqlite_mode="render_unsupported", sqlite_code="coverage.sqlite.operand-local-clauses")
        add("identical-duplicate-label-sort", "(SELECT NULL AS x,NULL AS x ORDER BY x)",
            "SELECT CAST(NULL AS TEXT),1", [col("x", "text", True), col("x", nullable=True)],
            [[None, None]], [[None, 1]], all_=True,
            sqlite_mode="render_unsupported", sqlite_code="coverage.sqlite.operand-local-clauses")
        items, labels = data["items"], data["labels"]
        ids, lids = [[r[0]] for r in items], [[r[0]] for r in labels]
        add("base-identifiers", "SELECT id AS v FROM items", "SELECT id FROM labels", [col()], ids, lids)
        scores = [[r[1]] for r in items]
        add("base-null-duplicate-bags", "SELECT score AS v FROM items", "SELECT id FROM labels",
            [col(nullable=True)], scores, lids, all_=True)
        add("two-column-null-bags", "SELECT id AS k,score AS v FROM items",
            "SELECT id,CAST(NULL AS INTEGER) FROM labels", [col("k"), col("v", nullable=True)],
            [[r[0], r[1]] for r in items], [[r[0], None] for r in labels])
        joined = [[i] for i, _, _ in items for key, _ in labels if key == i]
        add("using-join-bags", "SELECT id AS v FROM items JOIN labels USING(id)",
            "SELECT id FROM items", [col()], joined, ids, all_=True)
        add("cte-repeated-bags", "SELECT id AS v FROM c", "SELECT id FROM c", [col()], lids, lids,
            prefix="WITH c AS (SELECT id FROM labels) ")
        descending = sorted(combine(factor, True, scores, lids), key=lambda row: (row[0] is None, -(row[0] or 0)))
        add("ordered-null-last", "SELECT score AS v FROM items", "SELECT id FROM labels",
            [col(nullable=True)], scores, lids, all_=True, suffix=" ORDER BY v DESC NULLS LAST",
            rows=descending, sqlite_rows=descending, ordered=True)
        page = sorted(combine(factor, False, ids, lids)) [1:3]
        add("ordinal-pagination", "SELECT id AS v FROM items", "SELECT id FROM labels", [col()],
            ids, lids, suffix=" ORDER BY 1 LIMIT 2 OFFSET 1", rows=page, sqlite_rows=page, ordered=True)
        lexical = combine(factor, True, [[7]], [[9]])
        lexical = sorted(lexical)[:2]
        add("anonymous-parameters", "SELECT ? AS v FROM c WHERE x > ?", "SELECT ?",
            [col()], [[7]], [[9]], all_=True,
            prefix="WITH c AS (SELECT ? AS x) ", suffix=" ORDER BY v LIMIT ? OFFSET ?",
            types="int,int,int,int,int,int", values=[1, 7, 0, 9, 2, 0],
            rows=lexical, sqlite_rows=lexical, ordered=True)
        add("numbered-parameters", "SELECT $2 AS v", "SELECT $1+$1", [col()],
            [[6]], [[6]], types="int,int", values=[3, 6])
        add("nested-row-lock", "SELECT d.id AS v FROM (SELECT id FROM items FOR KEY SHARE) d",
            "SELECT id FROM labels", [col()], ids, lids, all_=True,
            sqlite_mode="input_excluded", sqlite_code="input.parse")
        assert len(result) - start == 50
    assert len(result) == len({r["id"] for r in result}) == len({r["sql"] for r in result}) == 150
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
        content = json.dumps(value, indent=2) + "\n"
        path = FIXTURES / name
        if args.check:
            assert path.read_text() == content, f"stale {path}"
        else:
            FIXTURES.mkdir(parents=True, exist_ok=True)
            path.write_text(content)
    print("PASS: 50 authored queries per UNION/INTERSECT/EXCEPT; four independent populations")


if __name__ == "__main__":
    main()
