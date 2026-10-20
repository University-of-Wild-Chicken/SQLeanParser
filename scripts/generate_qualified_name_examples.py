#!/usr/bin/env python3
"""Generate 50 independently expected schema-qualified SELECT examples."""
import argparse
import json
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
DIRECTORY = ROOT / "fixtures/qualified_names"
TABLES = {
    ("qa", "users"): [("id", "int", False), ("name", "text", False), ("active", "bool", False)],
    ("qb", "users"): [("id", "int", False), ("title", "text", True)],
    ("qa", "orders"): [("id", "int", False), ("user_id", "int", False), ("amount", "int", False)],
    ("qa", "users.dot"): [("id", "int", False), ("label", "text", False)],
    ("schema.dot", "table.dot"): [("id", "int", False), ("column.dot", "text", False)],
    ("qa", "select"): [("id", "int", False), ("from", "text", False)],
    ("Case Schema", "Case Table"): [("Case ID", "int", False), ("Case Name", "text", False)],
}
DATA = {
    ("qa", "users"): [[1, "Ada", True], [2, "Bea", False]],
    ("qb", "users"): [[1, "Bee"], [3, None]],
    ("qa", "orders"): [[11, 1, 5], [12, 1, 7], [13, 4, 9]],
    ("qa", "users.dot"): [[8, "dot"]],
    ("schema.dot", "table.dot"): [[9, "literal.dot"]],
    ("qa", "select"): [[10, "keyword"]],
    ("Case Schema", "Case Table"): [[12, "Case"]],
}


def schema():
    return {"tables": [
        {"schema": namespace, "name": name,
         "exposeUnqualified": namespace == "qa",
         "columns": [{"name": field, "type": kind, "nullable": nullable}
                     for field, kind, nullable in fields]}
        for (namespace, name), fields in TABLES.items()
    ]}


def col(name, kind="int32", nullable=False):
    return {"name": name, "type": kind, "nullable": nullable}


def cases():
    result = []
    ids = [[1], [2]]
    user_cols = [col("id"), col("name", "text"), col("active", "bool")]

    def add(shape, sql, columns, rows, types="", values=None):
        result.append({
            "id": "qualified-names-" + shape, "source_kind": "synthetic", "shape": shape,
            "sql": sql + ";", "sqlite_sql": sql.replace("$", "?") + ";",
            "catalogFile": "fixtures/qualified_names/schema.json",
            "parameter_types": types, "parameter_values": values or [],
            "output_columns": columns, "expected_rows": rows,
        })

    add("from", "SELECT id FROM qa.users", [col("id")], ids)
    add("column", "SELECT qa.users.id FROM qa.users", [col("id")], ids)
    add("basename", "SELECT users.id FROM qa.users", [col("id")], ids)
    add("alias", "SELECT u.id FROM qa.users AS u", [col("id")], ids)
    add("dotted-alias", 'SELECT "u.dot".id FROM qa.users AS "u.dot"', [col("id")], ids)
    add("quoted-parts", 'SELECT "qa"."users"."name" FROM "qa"."users"', [col("name", "text")],
        [["Ada"], ["Bea"]])
    add("schema-star", "SELECT qa.users.* FROM qa.users", user_cols, DATA[("qa", "users")])
    add("basename-star", "SELECT users.* FROM qa.users", user_cols, DATA[("qa", "users")])
    add("unqualified-star", "SELECT * FROM qa.users", user_cols, DATA[("qa", "users")])
    add("column-aliases", "SELECT u.key, u.label, u.enabled FROM qa.users AS u(key, label, enabled)",
        [col("key"), col("label", "text"), col("enabled", "bool")], DATA[("qa", "users")])
    add("partial-aliases", "SELECT u.key, u.name FROM qa.users AS u(key)",
        [col("key"), col("name", "text")], [[1, "Ada"], [2, "Bea"]])
    add("resolved-unqualified-origin", "SELECT qa.users.id FROM users", [col("id")], ids)
    add("dotted-table", 'SELECT qa."users.dot".label FROM qa."users.dot"',
        [col("label", "text")], [["dot"]])
    add("literal-dots", 'SELECT "schema.dot"."table.dot"."column.dot" FROM "schema.dot"."table.dot"',
        [col("column.dot", "text")], [["literal.dot"]])
    add("case-and-spaces", 'SELECT "Case Schema"."Case Table"."Case ID" FROM "Case Schema"."Case Table"',
        [col("Case ID")], [[12]])
    add("reserved-components", "SELECT qa.select.from FROM qa.select",
        [col("from", "text")], [["keyword"]])
    add("duplicate-labels", "SELECT qa.users.id AS x, qa.users.name AS x FROM qa.users",
        [col("x"), col("x", "text")], [[1, "Ada"], [2, "Bea"]])
    add("star-plus-expression", "SELECT qa.users.*, qa.users.id + 1 AS next FROM qa.users",
        [*user_cols, col("next")], [[1, "Ada", True, 2], [2, "Bea", False, 3]])
    add("numbered-parameter", "SELECT qa.users.id FROM qa.users WHERE qa.users.id >= $1",
        [col("id")], [[2]], "int", [2])
    add("nullable-parameter", "SELECT COALESCE(qb.users.title, $1) AS label FROM qb.users",
        [col("label", "text", True)], [["Bee"], [None]], "text?", [None])

    for kind, rows in [
        ("INNER", [[1, 1]]), ("LEFT", [[1, 1], [2, None]]),
        ("RIGHT", [[1, 1], [None, 3]]), ("FULL", [[1, 1], [2, None], [None, 3]]),
    ]:
        add(kind.lower() + "-same-basename",
            f"SELECT qa.users.id AS a, qb.users.id AS b FROM qa.users {kind} JOIN qb.users ON qa.users.id = qb.users.id",
            [col("a", nullable=kind in ("RIGHT", "FULL")), col("b", nullable=kind in ("LEFT", "FULL"))], rows)
    add("cross-same-basename", "SELECT qa.users.id AS a, qb.users.id AS b FROM qa.users CROSS JOIN qb.users",
        [col("a"), col("b")], [[1, 1], [1, 3], [2, 1], [2, 3]])
    add("using-same-basename", "SELECT id, qa.users.name, qb.users.title FROM qa.users FULL JOIN qb.users USING (id)",
        [col("id"), col("name", "text", True), col("title", "text", True)],
        [[1, "Ada", "Bee"], [2, "Bea", None], [3, None, None]])
    add("natural-same-basename", "SELECT * FROM qa.users NATURAL JOIN qb.users",
        [*user_cols, col("title", "text", True)], [[1, "Ada", True, "Bee"]])
    add("aliased-schemas", "SELECT a.id, b.title FROM qa.users a JOIN qb.users b ON a.id = b.id",
        [col("id"), col("title", "text", True)], [[1, "Bee"]])
    add("self-join", "SELECT a.id, b.name FROM qa.users a JOIN qa.users b ON a.id = b.id",
        [col("id"), col("name", "text")], [[1, "Ada"], [2, "Bea"]])
    add("mixed-visibility", "SELECT qa.users.id, qb.users.title FROM users JOIN qb.users ON qa.users.id = qb.users.id",
        [col("id"), col("title", "text", True)], [[1, "Bee"]])
    add("alias-and-base", "SELECT qa.users.id, u.name FROM qa.users JOIN qa.users u ON qa.users.id = u.id",
        [col("id"), col("name", "text")], [[1, "Ada"], [2, "Bea"]])
    add("derived", "SELECT d.id FROM (SELECT qa.users.id FROM qa.users) d", [col("id")], ids)
    add("nested-derived", "SELECT d.id, qb.users.title FROM (SELECT x.id FROM (SELECT qa.users.id FROM qa.users) x) d JOIN qb.users ON d.id = qb.users.id",
        [col("id"), col("title", "text", True)], [[1, "Bee"]])
    add("derived-basename-alias", "SELECT users.id FROM (SELECT qa.users.id FROM qa.users) users", [col("id")], ids)
    add("reserved-star", "SELECT qa.select.* FROM qa.select", [col("id"), col("from", "text")], [[10, "keyword"]])
    add("on-parameter", "SELECT qa.users.id, qa.orders.amount FROM qa.users JOIN qa.orders ON qa.users.id = qa.orders.user_id AND qa.orders.amount >= $1",
        [col("id"), col("amount")], [[1, 7]], "int", [7])
    add("anonymous-order", "SELECT ? + qa.users.id AS shifted, qa.orders.amount FROM qa.users JOIN qa.orders ON qa.users.id = qa.orders.user_id AND qa.orders.amount >= ? WHERE qa.users.id >= ?",
        [col("shifted"), col("amount")], [[11, 7]], "int,int,int", [10, 7, 1])
    add("repeated-parameter", "SELECT qa.users.id + $1 AS n FROM qa.users WHERE qa.users.id >= $1",
        [col("n")], [[2], [3]], "int", [1])
    add("reordered-parameter", "SELECT qa.users.id + $2 AS n FROM qa.users WHERE qa.users.id >= $1",
        [col("n")], [[12]], "int,int", [2, 10])
    add("distinct", "SELECT DISTINCT qa.users.id FROM qa.users JOIN qa.orders ON qa.users.id = qa.orders.user_id",
        [col("id")], [[1]])
    add("ordering", "SELECT qa.users.name FROM qa.users ORDER BY qa.users.id DESC",
        [col("name", "text")], [["Bea"], ["Ada"]])
    add("pagination", "SELECT qa.users.id FROM qa.users ORDER BY qa.users.id LIMIT $2 OFFSET $1",
        [col("id")], [[2]], "int,int", [1, 1])
    add("is-null", "SELECT qb.users.id, qb.users.title IS NULL AS missing FROM qb.users",
        [col("id"), col("missing", "bool")], [[1, False], [3, True]])
    add("substring", "SELECT SUBSTRING(qa.users.name FROM 2 FOR 2) AS part FROM qa.users",
        [col("part", "text")], [["da"], ["ea"]])
    add("case", "SELECT CASE WHEN qa.users.active THEN qa.users.name ELSE 'inactive' END AS label FROM qa.users",
        [col("label", "text")], [["Ada"], ["inactive"]])
    add("coalesce-outer", "SELECT qa.users.id, COALESCE(qb.users.title, 'none') AS label FROM qa.users LEFT JOIN qb.users ON qa.users.id = qb.users.id",
        [col("id"), col("label", "text")], [[1, "Bee"], [2, "none"]])
    add("locking", "SELECT qa.users.id FROM qa.users FOR UPDATE", [col("id")], ids)
    add("locking-first-inner", "SELECT qa.users.id FROM qa.users JOIN qb.users ON qa.users.id = qb.users.id FOR UPDATE OF users",
        [col("id")], [[1]])
    add("locking-first-left", "SELECT qa.users.id FROM qa.users LEFT JOIN qb.users ON qa.users.id = qb.users.id FOR UPDATE OF users",
        [col("id")], ids)
    add("locking-first-reversed", "SELECT qb.users.id FROM qb.users LEFT JOIN qa.users ON qa.users.id = qb.users.id FOR UPDATE OF users",
        [col("id")], [[1], [3]])
    assert len(result) == len({c["id"] for c in result}) == len({c["sql"] for c in result}) == 50
    return result


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--check", action="store_true")
    args = parser.parse_args()
    for name, value in (("schema.json", schema()), ("synthetic.json", cases())):
        path = DIRECTORY / name
        content = json.dumps(value, indent=2) + "\n"
        if args.check:
            assert path.read_text() == content, f"stale {path}"
        else:
            DIRECTORY.mkdir(parents=True, exist_ok=True)
            path.write_text(content)
    print("PASS: 50 schema-qualified SELECT examples with explicit relation visibility")


if __name__ == "__main__":
    main()
