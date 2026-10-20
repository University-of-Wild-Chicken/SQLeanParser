#!/usr/bin/env python3
"""Fifty authored recursive SELECTs with finite, independent row expectations."""
import argparse
import json
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
FIXTURES = ROOT / "fixtures/recursive_contract"
STATES = ("empty", "nodes_only", "edges_only", "both")
TABLES = {
    "nodes": [("id", "int", False), ("parent", "int", True), ("label", "text", False)],
    "edges": [("src", "int", False), ("dst", "int", False), ("weight", "int", False)],
}
DATA = {
    "nodes": [[1, None, "root"], [2, 1, "left"], [3, 1, "right"],
              [4, 2, "leaf"], [5, 9, "orphan"]],
    "edges": [[1, 2, 10], [1, 3, 20], [2, 4, 30], [3, 4, 40], [4, 5, 50]],
}
NATIVE = {
    "int32": ("INTEGER", "integer"), "bigint": ("BIGINT", "bigint"),
    "smallint": ("SMALLINT", "smallint"), "real": ("REAL", "real"),
    "double precision": ("DOUBLE PRECISION", "double precision"),
    "text": ("TEXT", "text"), "bool": ("BOOLEAN", "boolean"),
    "varchar(3)": ("VARCHAR(3)", "character varying(3)"),
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
        for name, columns in TABLES.items()]}


def col(name="n", type_="int32", nullable=True):
    native, display = NATIVE[type_]
    return {"name": name, "type": type_, "nullable": nullable,
            "postgres_type": native, "postgres_display_type": display}


def closure(seed, expand, *, distinct=False):
    """Finite fixture model. Each round reads only the preceding frontier."""
    frontier = [list(row) for row in seed]
    output, seen = [], set()
    for _ in range(30):
        if distinct:
            fresh = []
            for row in frontier:
                key = tuple(row)
                if key not in seen:
                    seen.add(key)
                    fresh.append(row)
            frontier = fresh
        if not frontier:
            return output
        output.extend(frontier)
        frontier = [list(child) for row in frontier for child in expand(row)]
    raise ValueError("authored fixture model did not terminate within thirty rounds")


def cases(data=DATA):
    result = []

    def add(shape, sql, output, rows, *, types="", values=None, sqlite_mode="execute",
            sqlite_code=None, sqlite_error=None, sqlite_rows=None, ordered=False):
        result.append({
            "id": f"recursive-{len(result)+1:03d}", "source_kind": "synthetic", "shape": shape,
            "sql": sql + ";", "sqlite_sql": sql.replace("$", "?") + ";",
            "catalogFile": "fixtures/recursive_contract/schema.json",
            "parameter_types": types, "parameter_values": values or [],
            "output_columns": output, "expected_rows": rows, "ordered": ordered,
            "sqlite_mode": sqlite_mode, "sqlite_diagnostic": sqlite_code, "sqlite_error": sqlite_error,
            "sqlite_output_names": [c["name"] for c in output],
            "sqlite_expected_rows": rows if sqlite_rows is None else sqlite_rows,
        })

    def basic(shape, anchor, step, rows, *, type_="int32", all_=True, **options):
        operator = "UNION ALL" if all_ else "UNION"
        add(shape, f"WITH RECURSIVE t(n) AS ({anchor} {operator} {step}) SELECT n FROM t",
            [col(type_=type_)], rows, **options)

    ints = lambda values: [[n] for n in values]
    basic("ascending-all", "SELECT 1", "SELECT n+1 FROM t WHERE n<4", ints(range(1, 5)))
    basic("ascending-distinct", "SELECT 1", "SELECT n+1 FROM t WHERE n<4", ints(range(1, 5)), all_=False)
    basic("descending", "SELECT 5", "SELECT n-1 FROM t WHERE n>1", ints(range(5, 0, -1)))
    basic("negative-sequence", "SELECT -3", "SELECT n+1 FROM t WHERE n<0", ints(range(-3, 1)))
    basic("empty-anchor", "SELECT 1 WHERE FALSE", "SELECT n+1 FROM t WHERE n<4", [])
    basic("empty-step", "SELECT 1", "SELECT n+1 FROM t WHERE FALSE", [[1]])
    basic("typed-null-anchor", "SELECT CAST(NULL AS INTEGER)", "SELECT n FROM t WHERE FALSE", [[None]])
    basic("unknown-null-anchor", "SELECT NULL", "SELECT n FROM t WHERE FALSE", [[None]], type_="text")
    basic("text-growth", "SELECT 'a'", "SELECT n||'x' FROM t WHERE LENGTH(n)<3",
          [["a"], ["ax"], ["axx"]], type_="text",
          sqlite_mode="render_unsupported", sqlite_code="coverage.sqlite.scalar-function-signatures")
    basic("varchar-modifier", "SELECT CAST('a' AS VARCHAR(3))",
          "SELECT CAST(n||'x' AS VARCHAR(3)) FROM t WHERE LENGTH(n)<3",
          [["a"], ["ax"], ["axx"]], type_="varchar(3)",
          sqlite_mode="render_unsupported", sqlite_code="coverage.sqlite.scalar-function-signatures")
    basic("numeric-modifier", "SELECT CAST(1 AS NUMERIC(6,2))",
          "SELECT CAST(n+0.5 AS NUMERIC(6,2)) FROM t WHERE n<2",
          [["1.00"], ["1.50"], ["2.00"]], type_="numeric(6,2)", sqlite_rows=[[1], [1.5], [2]])
    basic("bigint-range", "SELECT CAST(2147483647 AS BIGINT)",
          "SELECT n+1 FROM t WHERE n<2147483649", ints(range(2147483647, 2147483650)), type_="bigint")
    basic("real-sequence", "SELECT CAST(1 AS REAL)",
          "SELECT n+CAST(0.5 AS REAL) FROM t WHERE n<2", [["1"], ["1.5"], ["2"]],
          type_="real", sqlite_rows=[[1.0], [1.5], [2.0]])
    basic("double-sequence", "SELECT CAST(1 AS DOUBLE PRECISION)",
          "SELECT n+1 FROM t WHERE n<3", [["1"], ["2"], ["3"]],
          type_="double precision", sqlite_rows=[[1.0], [2.0], [3.0]])
    basic("smallint-sequence", "SELECT CAST(1 AS SMALLINT)",
          "SELECT CAST(n+1 AS SMALLINT) FROM t WHERE n<3", [[1], [2], [3]], type_="smallint")
    basic("boolean-toggle", "SELECT FALSE", "SELECT NOT n FROM t WHERE n=FALSE",
          [[False], [True]], type_="bool", sqlite_rows=[[0], [1]])
    basic("array-growth", "SELECT ARRAY[1]", "SELECT n||2 FROM t WHERE n[2] IS NULL",
          [["{1}"], ["{1,2}"]], type_="integer[]",
          sqlite_mode="input_excluded", sqlite_code="input.parse")
    basic("null-array-element", "SELECT ARRAY[CAST(NULL AS INTEGER)]",
          "SELECT n||1 FROM t WHERE n[2] IS NULL", [["{NULL}"], ["{NULL,1}"]], type_="integer[]",
          sqlite_mode="input_excluded", sqlite_code="input.parse")
    basic("array-deduplication", "SELECT ARRAY[1]", "SELECT n FROM t",
          [["{1}"]], type_="integer[]", all_=False,
          sqlite_mode="input_excluded", sqlite_code="input.parse")
    basic("integer-deduplication", "SELECT 1", "SELECT n FROM t", [[1]], all_=False)
    add("bounded-depth", "WITH RECURSIVE t(n,depth) AS "
        "(SELECT 1,0 UNION ALL SELECT n,depth+1 FROM t WHERE depth<3) SELECT n,depth FROM t",
        [col(), col("depth")], [[1, i] for i in range(4)])
    add("fibonacci", "WITH RECURSIVE t(a,b) AS "
        "(SELECT 0,1 UNION ALL SELECT b,a+b FROM t WHERE a<3) SELECT a,b FROM t",
        [col("a"), col("b")], [[0, 1], [1, 1], [1, 2], [2, 3], [3, 5]])
    add("earlier-nonrecursive-definition", "WITH RECURSIVE seed AS (SELECT 2 AS x), "
        "t(n) AS (SELECT x FROM seed UNION ALL SELECT n+2 FROM t WHERE n<6) SELECT n FROM t",
        [col()], [[2], [4], [6]])
    add("later-nonrecursive-definition", "WITH RECURSIVE t(n) AS "
        "(SELECT 1 UNION ALL SELECT n+1 FROM t WHERE n<3), result AS (SELECT n+10 AS x FROM t) "
        "SELECT x FROM result", [col("x")], [[11], [12], [13]])
    add("two-independent-recursions", "WITH RECURSIVE a(n) AS "
        "(SELECT 1 UNION ALL SELECT n+1 FROM a WHERE n<3), b(m) AS "
        "(SELECT 1 UNION ALL SELECT m+1 FROM b WHERE m<2) SELECT n,m FROM a CROSS JOIN b",
        [col(), col("m")], [[n, m] for n in (1, 2, 3) for m in (1, 2)])
    basic("nested-derived-reference", "SELECT 1",
          "SELECT d.n+1 FROM (SELECT n FROM t) d WHERE d.n<3", [[1], [2], [3]],
          sqlite_mode="analysis_error", sqlite_error="circular reference: t")
    basic("nested-cte-reference", "SELECT 1",
          "(WITH c AS (SELECT n FROM t) SELECT n+1 FROM c WHERE n<3)", [[1], [2], [3]],
          sqlite_mode="input_excluded", sqlite_code="input.parse")
    basic("derived-anchor", "SELECT x FROM (SELECT 1 AS x) seed",
          "SELECT n+1 FROM t WHERE n<3", [[1], [2], [3]])
    basic("operand-local-pagination", "SELECT 1",
          "(SELECT n+1 FROM t WHERE n<3 ORDER BY n LIMIT 1)", [[1], [2], [3]],
          sqlite_mode="input_excluded", sqlite_code="input.parse")
    basic("unused-inner-reference", "SELECT 1",
          "(WITH unused AS (SELECT n FROM t) SELECT 2)", [[1], [2]], all_=False,
          sqlite_mode="input_excluded", sqlite_code="input.parse")
    add("anonymous-parameters", "WITH RECURSIVE t(n) AS "
        "(SELECT ? UNION ALL SELECT n+? FROM t WHERE n<?) SELECT n FROM t ORDER BY n LIMIT ? OFFSET ?",
        [col()], [[3], [5]], types="int,int,int,int,int", values=[1, 2, 6, 2, 1], ordered=True)
    basic("numbered-parameters", "SELECT $2",
          "SELECT n+$1 FROM t WHERE n<$3", [[1], [3], [5]], types="int,int,int", values=[2, 1, 5])
    add("unused-definition-parameters", "WITH RECURSIVE unused AS (SELECT ? AS x), t(n) AS "
        "(SELECT ? UNION ALL SELECT n+? FROM t WHERE n<?) SELECT ? AS marker,n FROM t",
        [col("marker", nullable=False), col()], [[7, 1], [7, 2], [7, 3]],
        types="int,int,int,int,int", values=[99, 1, 1, 3, 7])
    add("quoted-dot-identities", 'WITH RECURSIVE "r.dot"("v.dot") AS '
        '(SELECT 1 UNION ALL SELECT "v.dot"+1 FROM "r.dot" WHERE "v.dot"<3) SELECT "v.dot" FROM "r.dot"',
        [col("v.dot")], [[1], [2], [3]])
    add("prefix-column-alias", "WITH RECURSIVE t(n) AS "
        "(SELECT 1 AS x,10 AS y UNION ALL SELECT n+1,y+2 FROM t WHERE n<3) SELECT n,y FROM t",
        [col(), col("y")], [[1, 10], [2, 12], [3, 14]],
        sqlite_mode="analysis_error", sqlite_error="table t has 2 values for 1 columns")
    add("nonnullable-outer-expression", "WITH RECURSIVE t(n) AS "
        "(SELECT 1 UNION ALL SELECT n+1 FROM t WHERE n<3) SELECT n IS NULL AS missing FROM t",
        [col("missing", "bool", False)], [[False], [False], [False]], sqlite_rows=[[0], [0], [0]])
    add("recursive-derived-source", "SELECT d.n FROM (WITH RECURSIVE t(n) AS "
        "(SELECT 1 UNION ALL SELECT n+1 FROM t WHERE n<3) SELECT n FROM t) d",
        [col()], [[1], [2], [3]])
    add("recursive-inside-ordinary-cte", "WITH c AS (WITH RECURSIVE t(n) AS "
        "(SELECT 1 UNION ALL SELECT n+1 FROM t WHERE n<3) SELECT n FROM t) SELECT n FROM c",
        [col()], [[1], [2], [3]])
    basic("distinct-recursive-arm", "SELECT 1",
          "SELECT DISTINCT n+1 FROM t WHERE n<3", [[1], [2], [3]])
    basic("intersect-recursive-arm", "SELECT 1",
          "(SELECT n+1 FROM t WHERE n<3 INTERSECT SELECT 2)", [[1], [2]],
          sqlite_mode="input_excluded", sqlite_code="input.parse")
    assert len(result) == 40

    nodes, edges = data["nodes"], data["edges"]
    roots = [[n] for n, parent, _ in nodes if parent is None]
    descendants = closure(roots, lambda row: [[n] for n, parent, _ in nodes if parent == row[0]])
    for all_ in (True, False):
        operator = "UNION ALL" if all_ else "UNION"
        add("hierarchy-all" if all_ else "hierarchy-distinct",
            "WITH RECURSIVE t(id) AS (SELECT id FROM nodes WHERE parent IS NULL "
            f"{operator} SELECT n.id FROM nodes n JOIN t ON n.parent=t.id) SELECT id FROM t",
            [col("id")], descendants)
    ancestors = closure([[n] for n, _, _ in nodes if n == 4],
                        lambda row: [[parent] for n, parent, _ in nodes if n == row[0] and parent is not None])
    add("ancestors", "WITH RECURSIVE t(id) AS (SELECT id FROM nodes WHERE id=4 UNION ALL "
        "SELECT n.parent FROM nodes n JOIN t ON n.id=t.id WHERE n.parent IS NOT NULL) SELECT id FROM t",
        [col("id")], ancestors)
    depth_rows = closure([[n, 0] for n, parent, _ in nodes if parent is None],
                         lambda row: [[n, row[1]+1] for n, parent, _ in nodes if parent == row[0]])
    add("hierarchy-depth", "WITH RECURSIVE t(id,depth) AS (SELECT id,0 FROM nodes WHERE parent IS NULL UNION ALL "
        "SELECT n.id,t.depth+1 FROM nodes n JOIN t ON n.parent=t.id) SELECT id,depth FROM t",
        [col("id"), col("depth")], depth_rows)
    graph_step = lambda row: [[dst] for src, dst, _ in edges if src == row[0]]
    paths = closure([[1]], graph_step)
    reachable = closure([[1]], graph_step, distinct=True)
    for all_, rows in ((True, paths), (False, reachable)):
        operator = "UNION ALL" if all_ else "UNION"
        add("graph-path-bags" if all_ else "graph-reachability",
            f"WITH RECURSIVE t(id) AS (SELECT 1 {operator} "
            "SELECT e.dst FROM t JOIN edges e ON t.id=e.src) SELECT id FROM t",
            [col("id")], rows)
    weighted = closure([[1, 0]], lambda row: [[dst, row[1]+weight] for src, dst, weight in edges if src == row[0]])
    add("weighted-paths", "WITH RECURSIVE t(id,total) AS (SELECT 1,0 UNION ALL "
        "SELECT e.dst,t.total+e.weight FROM t JOIN edges e ON t.id=e.src) SELECT id,total FROM t",
        [col("id"), col("total")], weighted)
    visible_paths = closure(roots, lambda row: [[dst] for src, dst, _ in edges if src == row[0]
                                              for n, _, _ in nodes if n == dst])
    add("catalog-visible-paths", "WITH RECURSIVE t(id) AS (SELECT id FROM nodes WHERE parent IS NULL UNION ALL "
        "SELECT e.dst FROM t JOIN edges e ON t.id=e.src JOIN nodes n ON n.id=e.dst) SELECT id FROM t",
        [col("id")], visible_paths)
    common = [[row[0]] for row in paths for n, _, _ in nodes if n == row[0]]
    graph = "WITH RECURSIVE t(id) AS (SELECT 1 UNION ALL SELECT e.dst FROM t JOIN edges e ON t.id=e.src) "
    add("using-outer-result", graph + "SELECT t.id FROM t JOIN nodes USING(id)", [col("id")], common)
    outer = [[n, matched] for n, _, _ in nodes
             for matched in ([row[0] for row in paths if row[0] == n] or [None])]
    add("outer-join-result", graph + "SELECT n.id,t.id AS reachable FROM nodes n LEFT JOIN t ON n.id=t.id",
        [col("id", nullable=False), col("reachable")], outer)
    assert len(result) == len({r["id"] for r in result}) == len({r["sql"] for r in result}) == 50
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
    print("PASS: 50 authored recursive SELECTs with four independent finite data populations")


if __name__ == "__main__":
    main()
