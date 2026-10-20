#!/usr/bin/env python3
"""Generate 50 bounded synthetic row-locking SELECT witnesses."""
import argparse
import json
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
DESTINATION = ROOT / "fixtures/locking/synthetic.json"
USERS = [
    [1, 24, "Alice", "Paris"], [2, 17, "Bob", "Paris"],
    [3, 38, "Carol", "Rome"], [4, 71, "Dora", "Rome"],
    [5, 33, "O'Brien", ""], [6, 40, "Fran", "Paris"],
]
STRENGTHS = ("UPDATE", "NO KEY UPDATE", "SHARE", "KEY SHARE")
POLICIES = ("", "NOWAIT", "SKIP LOCKED")


def column(name, type_):
    return {"name": name, "type": type_, "nullable": False}


def cases():
    result = []

    def add(sql, types, values, columns, rows, shape):
        result.append({
            "id": f"locking-synthetic-{len(result) + 1:02}", "source_kind": "synthetic",
            "sql": sql, "catalogFile": "fixtures/schema.json", "shape": shape,
            # Only fixed templates above contain dollars, always as $N markers.
            "sqlite_sql": sql.replace("$", "?"),
            "parameter_types": types, "parameter_values": values,
            "output_columns": columns, "expected_rows": rows,
        })

    for strength in STRENGTHS:
        for policy in POLICIES:
            suffix = " " + policy if policy else ""
            add(f"SELECT id FROM users WHERE age >= 18 ORDER BY id FOR {strength}{suffix};",
                "", [], [column("id", "int32")],
                [[1], [3], [4], [5], [6]], "filtered-base-table")
            add("SELECT u.id AS user_id, u.name AS user_name FROM users AS u "
                f"WHERE u.city = $1 ORDER BY u.id FOR {strength} OF u{suffix};",
                "text", ["Paris"], [column("user_id", "int32"), column("user_name", "text")],
                [[1, "Alice"], [2, "Bob"], [6, "Fran"]], "alias-and-text-parameter")
            add("SELECT id, age FROM users WHERE age >= $3 ORDER BY id "
                f"OFFSET $2 LIMIT $1 FOR {strength}{suffix};",
                "int,int,int", [2, 1, 18], [column("id", "int32"), column("age", "int32")],
                [[3, 38], [4, 71]], "numbered-offset-first")
            add("SELECT u.id AS id, (u.age + ?) AS next_age FROM users AS u "
                f"WHERE u.id >= ? ORDER BY u.id FOR {strength} OF u{suffix} OFFSET ? LIMIT ?;",
                "int,int,int,int", [5, 2, 1, 2],
                [column("id", "int32"), column("next_age", "int32")],
                [[3, 43], [4, 76]], "anonymous-leading-lock-offset-first")
    add("SELECT id, age >= 18 AS adult FROM users WHERE id <= 3 ORDER BY id "
        "FOR SHARE OF users NOWAIT FOR UPDATE OF users SKIP LOCKED;",
        "", [], [column("id", "int32"), column("adult", "bool")],
        [[1, True], [2, False], [3, True]], "multiple-strengths-and-policies")
    add("SELECT u.name AS name FROM users AS u WHERE u.id >= $1 ORDER BY u.id "
        "LIMIT $2 OFFSET $3 FOR NO KEY UPDATE OF u FOR KEY SHARE OF u NOWAIT;",
        "int,int,int", [4, 2, 0], [column("name", "text")],
        [["Dora"], ["O'Brien"]], "multiple-clauses-aliased-text")
    assert len(result) == len({case["sql"] for case in result}) == 50
    return result


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--check", action="store_true")
    args = parser.parse_args()
    content = json.dumps(cases(), indent=2) + "\n"
    if args.check:
        assert DESTINATION.read_text() == content, "stale locking examples"
    else:
        DESTINATION.parent.mkdir(parents=True, exist_ok=True)
        DESTINATION.write_text(content)
    print("PASS: 50 distinct locking SELECTs with exact schemas and authored row expectations")


if __name__ == "__main__":
    main()
