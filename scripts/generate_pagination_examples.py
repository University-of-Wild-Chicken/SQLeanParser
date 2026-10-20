#!/usr/bin/env python3
"""Fifty deterministic expression-pagination witnesses, with independent slices."""
import argparse
import json
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
DESTINATION = ROOT / "fixtures/pagination"

# (LIMIT, OFFSET, separate parameter values, declared types, expected take, skip).
# Expected bounds are written explicitly, not evaluated from the SQL text.
BOUNDS = [
    ("$1", None, [2], "int", 2, 0),
    ("?", None, [3], "int", 3, 0),
    ("$1", "$2", [2, 1], "int,int", 2, 1),
    ("?", "?", [2, 2], "int,int", 2, 2),
    ("$2", "$1", [1, 3], "int,int", 3, 1),
    ("($1 + 1)", None, [2], "int", 3, 0),
    ("($1 - 1)", None, [3], "int", 2, 0),
    ("($1 * 2)", None, [2], "int", 4, 0),
    ("($1 / 2)", None, [5], "int", 2, 0),
    ("(2 + $1)", "1", [1], "int", 3, 1),
    ("(8 - $1)", "2", [5], "int", 3, 2),
    ("(2 * $1)", "($1 - 1)", [2], "int", 4, 1),
    ("(8 / $1)", None, [2], "int", 4, 0),
    ("+$1", "+$2", [2, 1], "int,int", 2, 1),
    ("-(-$1)", "-(-$2)", [2, 1], "int,int", 2, 1),
    ("(-$1 + 5)", None, [2], "int", 3, 0),
    ("(($1 + 1) * 2)", None, [1], "int", 4, 0),
    ("($1 + (2 * $2))", None, [1, 1], "int,int", 3, 0),
    ("(($1 + $2) / 2)", None, [3, 4], "int,int", 3, 0),
    ("($1 + $1)", "($1 - 1)", [2], "int", 4, 1),
    ("CAST($1 AS INTEGER)", None, [3], "int", 3, 0),
    ("$1::INTEGER", "$2::INTEGER", [2, 1], "int,int", 2, 1),
    ("CAST('3' AS INTEGER)", None, [], "", 3, 0),
    ("CAST($1 AS INTEGER)", "CAST($2 AS INTEGER)", ["2", "1"], "text,text", 2, 1),
    ("CAST(TRUE AS INTEGER)", None, [], "", 1, 0),
    ("CAST(FALSE AS INTEGER)", None, [], "", 0, 0),
    ("CAST(CAST($1 AS BOOLEAN) AS INTEGER)", None, [True], "bool", 1, 0),
    ("CAST(CAST($1 AS TEXT) AS INTEGER)", None, [2], "int", 2, 0),
    ("(CAST($1 AS INTEGER) + 1)", None, ["2"], "text", 3, 0),
    ("(CAST(? AS INTEGER) * 2)", "CAST(? AS INTEGER)", ["2", "1"], "text,text", 4, 1),
    ("NULL", None, [], "", None, 0),
    ("CAST(NULL AS INTEGER)", None, [], "", None, 0),
    ("($1 * 1)", None, [None], "int?", None, 0),
    ("(1 + $1)", None, [None], "int?", None, 0),
    ("2", "NULL", [], "", 2, 0),
    ("2", "CAST(NULL AS INTEGER)", [], "", 2, 0),
    ("2", "$1", [None], "int?", 2, 0),
    ("($1 + 0)", "($2 + 0)", [None, None], "int?,int?", None, 0),
    ("(? + 0)", "?", [None, 2], "int?,int", None, 2),
    ("(CAST($1 AS INTEGER) + NULL)", None, [None], "text?", None, 0),
    ("(1 + 2)", "(1 + 1)", [], "", 3, 2),
    ("(7 - 4)", "(3 - 2)", [], "", 3, 1),
    ("(2 * 2)", "(4 / 2)", [], "", 4, 2),
    ("((2 + 3) / 2)", "(2 * 1)", [], "", 2, 2),
    ("0", "($1 + 1)", [2], "int", 0, 3),
    ("$1", "6", [3], "int", 3, 6),
    ("10", "($1 * 2)", [2], "int", 10, 4),
    ("CAST('2' AS INTEGER)", "CAST('3' AS INTEGER)", [], "", 2, 3),
    ("($2 - $1)", "($1 + 1)", [1, 4], "int,int", 3, 2),
    ("(? + ?)", "(? - ?)", [1, 2, 3, 2], "int,int,int,int", 3, 1),
]


def cases():
    result = []
    for i, (limit, offset, values, types, take, skip) in enumerate(BOUNDS, 1):
        source = "SELECT id FROM page_rows ORDER BY id LIMIT " + limit
        if offset is not None:
            source += " OFFSET " + offset
        source += ";"
        # Deliberate dialect fixture, not a scraped statement transformation.
        # The finite templates contain dollar signs only in binding markers.
        sqlite_source = source.replace("$", "?")
        if i == 22:
            sqlite_source = ("SELECT id FROM page_rows ORDER BY id "
                             "LIMIT CAST(?1 AS INTEGER) OFFSET CAST(?2 AS INTEGER);")
        rows = [[n] for n in range(1, 7)][skip:]
        if take is not None:
            rows = rows[:take]
        result.append({
            "id": f"pagination-synthetic-{i:02}",
            "source_kind": "synthetic",
            "sql": source,
            "sqlite_sql": sqlite_source,
            "parameter_types": types,
            "parameter_values": values,
            "expected_rows": rows,
            "sqlite_null_bound": take is None or (
                offset is not None and ("NULL" in offset or
                (i in {37, 38}))),
        })
    assert len(result) == len({r["sql"] for r in result}) == 50
    return result


SCHEMA = {
    "tables": [{"name": "page_rows", "columns": [
        {"name": "id", "type": "int", "nullable": False},
    ]}]
}


def main():
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument("--check", action="store_true")
    args = ap.parse_args()
    artifacts = {
        "synthetic.json": json.dumps(cases(), indent=2) + "\n",
        "schema.json": json.dumps(SCHEMA, indent=2) + "\n",
    }
    for name, content in artifacts.items():
        path = DESTINATION / name
        if args.check:
            if not path.is_file() or path.read_text() != content:
                raise SystemExit(f"stale pagination fixture: {path}")
        else:
            path.parent.mkdir(parents=True, exist_ok=True)
            path.write_text(content)
    print("PASS: 50 distinct synthetic pagination cases")


if __name__ == "__main__":
    main()
