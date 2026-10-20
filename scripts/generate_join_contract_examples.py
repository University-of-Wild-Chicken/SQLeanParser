#!/usr/bin/env python3
"""Generate 50 SELECTs for independent base-table JOIN contracts."""
import argparse
import json
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
DIRECTORY = ROOT / "fixtures/join_contract"
USERS = [[1, 24, "Ada"], [2, 17, "Bea"], [3, 38, "Cy"]]
ORDERS = [[11, 1, 5], [12, 1, 7], [13, 4, 9]]
REGIONS = [[1, "North"], [3, "West"]]
KINDS = ("CROSS", "INNER", "LEFT", "RIGHT", "FULL")
TABLES = {
    "users": [("id", "int"), ("age", "int"), ("name", "text")],
    "orders": [("id", "int"), ("user_id", "int"), ("amount", "int")],
    "regions": [("id", "int"), ("label", "text")],
}
DATA = {"users": USERS, "orders": ORDERS, "regions": REGIONS}


def schema():
    return {"tables": [
        {"name": name, "columns": [
            {"name": field, "type": kind, "nullable": False} for field, kind in fields]}
        for name, fields in TABLES.items()]}


def cell(row, index):
    return row[index] if row is not None else None


def pairs(kind, minimum=None):
    result, right_matched = [], set()
    for user in USERS:
        matches = [(index, order) for index, order in enumerate(ORDERS)
                   if kind == "CROSS" or
                   (user[0] == order[1] and (minimum is None or order[2] >= minimum))]
        result += [(user, order) for _, order in matches]
        right_matched.update(index for index, _ in matches)
        if not matches and kind in ("LEFT", "FULL"):
            result.append((user, None))
    if kind in ("RIGHT", "FULL"):
        result += [(None, order) for index, order in enumerate(ORDERS) if index not in right_matched]
    return result


def ordered(rows):
    return sorted(rows, key=lambda row: tuple((value is None, value) for value in row))


def cases():
    result = []
    for kind in KINDS:
        nullable_left = kind in ("RIGHT", "FULL")
        nullable_right = kind in ("LEFT", "FULL")
        source = f"users AS u {kind} JOIN orders AS o"
        if kind != "CROSS":
            source += " ON u.id = o.user_id"
        joined = pairs(kind)

        def col(name, type_="int32", nullable=False):
            return {"name": name, "type": type_, "nullable": nullable}

        def add(shape, projection, columns, rows, suffix="", types="", values=None, from_sql=None):
            sql = f"SELECT {projection} FROM {from_sql or source}{suffix};"
            result.append({
                "id": f"join-{kind.lower()}-{shape}",
                "source_kind": "synthetic", "join_kind": kind.lower(), "shape": shape,
                "sql": sql, "sqlite_sql": sql.replace("$", "?"),
                "catalogFile": "fixtures/join_contract/schema.json",
                "parameter_types": types, "parameter_values": values or [],
                "output_columns": columns, "expected_rows": ordered(rows),
            })

        ids = [col("user_id", nullable=nullable_left), col("order_id", nullable=nullable_right)]
        add("identity", "u.id AS user_id, o.id AS order_id", ids,
            [[cell(u, 0), cell(o, 0)] for u, o in joined])
        add("text-and-amount", "u.name AS name, o.amount AS amount",
            [col("name", "text", nullable_left), col("amount", nullable=nullable_right)],
            [[cell(u, 2), cell(o, 2)] for u, o in joined])
        add("post-join-filter", "u.id AS user_id, o.id AS order_id", ids,
            [[cell(u, 0), o[0]] for u, o in joined if o is not None and o[2] >= 7],
            " WHERE o.amount >= $1", "int", [7])
        add("coalesced", "COALESCE(u.id, 0) AS user_id, COALESCE(o.amount, 0) AS amount",
            [col("user_id"), col("amount")],
            [[cell(u, 0) or 0, cell(o, 2) or 0] for u, o in joined])
        parameter_source = source if kind == "CROSS" else source + " AND o.amount >= ?"
        selected = joined if kind == "CROSS" else pairs(kind, 7)
        # Projection parameters precede ON, which precedes WHERE in source order.
        where = " WHERE o.amount >= ? AND COALESCE(u.age, 0) >= ?" if kind == "CROSS" \
            else " WHERE COALESCE(u.age, 0) >= ?"
        rows = [[10 + (cell(u, 0) or 0), cell(o, 0)] for u, o in selected
                if (cell(u, 1) or 0) >= 18 and
                (kind != "CROSS" or (o is not None and o[2] >= 7))]
        add("anonymous-source-order", "? + COALESCE(u.id, 0) AS shifted, o.id AS order_id",
            [col("shifted"), col("order_id", nullable=nullable_right)], rows,
            where, "int,int,int", [10, 7, 18], parameter_source)
        add("nullable-boolean", "u.id IS NULL AS missing_user, o.id IS NULL AS missing_order",
            [col("missing_user", "bool"), col("missing_order", "bool")],
            [[u is None, o is None] for u, o in joined])
        add("distinct", "DISTINCT u.id AS user_id", [col("user_id", nullable=nullable_left)],
            [[value] for value in {cell(u, 0) for u, _ in joined}])
        id_rows = ordered([[cell(u, 0), cell(o, 0)] for u, o in joined])
        add("ordered-pagination", "u.id AS user_id, o.id AS order_id", ids, id_rows[1:3],
            " ORDER BY user_id NULLS LAST, order_id NULLS LAST LIMIT $2 OFFSET $1",
            "int,int", [1, 2])
        add("qualified-wildcard", "u.*, o.amount AS amount",
            [col("id", nullable=nullable_left), col("age", nullable=nullable_left),
             col("name", "text", nullable_left), col("amount", nullable=nullable_right)],
            [[cell(u, 0), cell(u, 1), cell(u, 2), cell(o, 2)] for u, o in joined])
        nested_source = source + " LEFT JOIN regions AS r ON u.id = r.id AND r.id >= $2"
        nested_rows = []
        for u, o in joined:
            matches = [r for r in REGIONS if u is not None and r[0] == u[0] and r[0] >= 1]
            nested_rows += [[cell(u, 0), cell(o, 0), (r[1] if r else None), 3]
                            for r in (matches or [None])]
        add("nested-outer", "u.id AS user_id, o.id AS order_id, r.label AS region, $1 AS marker",
            [*ids, col("region", "text", True), col("marker")], nested_rows,
            types="int,int", values=[3, 1], from_sql=nested_source)
    assert len(result) == len({row["id"] for row in result}) == len({row["sql"] for row in result}) == 50
    return result


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--check", action="store_true")
    args = parser.parse_args()
    for name, value in (("schema.json", schema()), ("synthetic.json", cases())):
        content = json.dumps(value, indent=2) + "\n"
        path = DIRECTORY / name
        if args.check:
            assert path.read_text() == content, f"stale {path}"
        else:
            DIRECTORY.mkdir(parents=True, exist_ok=True)
            path.write_text(content)
    print("PASS: 50 JOIN contract examples, ten for each of five join kinds")


if __name__ == "__main__":
    main()
