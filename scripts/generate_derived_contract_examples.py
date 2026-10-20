#!/usr/bin/env python3
"""Generate 50 derived-source queries with independent finite row expectations."""
import argparse
import json
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
DIRECTORY = ROOT / "fixtures/derived_contract"
TABLES = {
    "items": [("id", "int", False), ("score", "int", True), ("name", "text", False)],
    "labels": [("id", "int", False), ("category", "text", False)],
}
DATA = {
    "items": [[1, 10, "Ada"], [2, None, "Bea"], [3, 10, "Cy"], [4, 40, "Di"]],
    "labels": [[1, "A"], [1, "B"], [3, "C"], [5, "E"]],
}
STATES = ("empty", "items_only", "labels_only", "both")


def population(state):
    assert state in STATES
    return {name: rows if state in ("both", name + "_only") else [] for name, rows in DATA.items()}


def schema():
    return {"tables": [
        {"name": name, "columns": [{"name": field, "type": type_, "nullable": nullable}
                                  for field, type_, nullable in columns]}
        for name, columns in TABLES.items()]}


def col(name, type_="int32", nullable=False):
    return {"name": name, "type": type_, "nullable": nullable}


def ordered(rows):
    return sorted(rows, key=lambda row: tuple((v is None, v) for v in row))


def cases(data=DATA):
    result = []
    for minimum in range(5):
        items = [row for row in data["items"] if row[0] >= minimum]
        labels = [row for row in data["labels"] if row[0] >= minimum]
        child = f"SELECT id, score, name FROM items WHERE id >= {minimum}"
        columns = [col("id"), col("score", nullable=True), col("name", "text")]

        def add(shape, sql, output, rows, types="", values=None, sqlite_supported=True):
            result.append({
                "id": f"derived-{minimum}-{shape}", "source_kind": "synthetic",
                "shape": shape, "minimum": minimum, "sql": sql + ";",
                "sqlite_sql": sql.replace("$", "?") + ";",
                "sqlite_supported": sqlite_supported,
                "catalogFile": "fixtures/derived_contract/schema.json",
                "parameter_types": types, "parameter_values": values or [],
                "output_columns": output, "expected_rows": ordered(rows),
            })

        add("projection", f"SELECT d.id, d.score, d.name FROM ({child}) AS d", columns, items)
        add("nested", "SELECT d.id, d.points + 1 AS adjusted FROM "
            f"(SELECT x.id, COALESCE(x.score, 0) AS points FROM ({child}) AS x) AS d",
            [col("id"), col("adjusted")], [[i, (score or 0) + 1] for i, score, _ in items])
        add("prefix-alias", f"SELECT d.key_id, d.score, d.name FROM ({child}) AS d(key_id)",
            [col("key_id"), *columns[1:]], items, sqlite_supported=False)
        add("full-alias", f"SELECT d.* FROM ({child}) AS d(key_id, points, label)",
            [col("key_id"), col("points", nullable=True), col("label", "text")],
            items, sqlite_supported=False)
        add("anonymous-order", "SELECT ? AS marker, d.id, d.score FROM "
            f"({child} AND id >= ?) AS d WHERE COALESCE(d.score, 0) >= ? "
            "ORDER BY d.id LIMIT ? OFFSET ?",
            [col("marker"), col("id"), col("score", nullable=True)],
            [[7, i, score] for i, score, _ in items if i >= 1 and (score or 0) >= 0][:2],
            "int,int,int,int,int", [7, 1, 0, 2, 0])
        left_rows = [[i, category] for i, _, _ in items
                     for category in ([label[1] for label in data["labels"] if label[0] == i] or [None])]
        add("left-join", f"SELECT d.id, l.category FROM ({child}) AS d LEFT JOIN labels AS l ON d.id = l.id",
            [col("id"), col("category", "text", True)], left_rows)
        full_rows = []
        for i, _, _ in data["items"]:
            matches = [label for label in labels if label[0] == i]
            full_rows += [[i, i, category] for _, category in matches] if matches else [[i, i, None]]
        full_rows += [[i, None, category] for i, category in labels
                      if not any(item[0] == i for item in data["items"])]
        add("full-using", "SELECT id AS merged_id, i.id AS original_id, d.category FROM items AS i "
            f"FULL JOIN (SELECT id, category FROM labels WHERE id >= {minimum}) AS d USING (id)",
            [col("merged_id"), col("original_id", nullable=True), col("category", "text", True)],
            full_rows)
        add("two-derived", f"SELECT d.id, p.marker FROM ({child}) AS d CROSS JOIN (SELECT $1 AS marker) AS p",
            [col("id"), col("marker")], [[i, 9] for i, _, _ in items], "int", [9])
        scores = sorted({row[1] for row in items}, key=lambda v: (v is None, v))[:2]
        add("child-distinct-pagination", "SELECT d.score FROM "
            f"(SELECT DISTINCT score FROM items WHERE id >= {minimum} "
            "ORDER BY score NULLS LAST LIMIT 2) AS d WHERE d.score IS NOT NULL",
            [col("score", nullable=True)], [[score] for score in scores if score is not None])
        natural_rows = [[i, score, name, category] for i, score, name in items
                        for category in ([label[1] for label in data["labels"] if label[0] == i] or [None])]
        add("natural-qualified-star", f"SELECT d.*, l.category FROM ({child}) AS d NATURAL LEFT JOIN labels AS l",
            [*columns, col("category", "text", True)], natural_rows)
    assert len(result) == len({case["sql"] for case in result}) == 50
    return result


def all_cases():
    result = cases()
    for case in result:
        case["expected_rows_by_state"] = {}
    for state in STATES:
        for case, observed in zip(result, cases(population(state))):
            assert case["id"] == observed["id"] and case["output_columns"] == observed["output_columns"]
            case["expected_rows_by_state"][state] = observed["expected_rows"]
    return result


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--check", action="store_true")
    args = parser.parse_args()
    for name, value in (("schema.json", schema()), ("synthetic.json", all_cases())):
        path = DIRECTORY / name
        content = json.dumps(value, indent=2) + "\n"
        if args.check:
            assert path.read_text() == content, f"stale {path}"
        else:
            DIRECTORY.mkdir(parents=True, exist_ok=True)
            path.write_text(content)
    print("PASS: 50 derived-source examples, ten forms with five inner filter boundaries")


if __name__ == "__main__":
    main()
