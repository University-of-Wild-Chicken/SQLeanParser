#!/usr/bin/env python3
"""Generate 50 deterministic SELECT examples for each new dialect feature.

Expected observations are authored from explicit operands and fixture rows,
without invoking SQLean or a database. --check verifies all committed outputs.
"""

from __future__ import annotations

import argparse
from decimal import Decimal
import json
from pathlib import Path


ROOT = Path(__file__).resolve().parents[1]
DESTINATION = ROOT / "fixtures/dialects"
SQLITE_ROWS = [(1, "a"), (2, "b"), (2, "b"), (3, None), (4, "d"), (5, "e"), (6, "f"), (7, "g")]


def case(sql, rows, columns, parameters=(), *, comparison="ordered"):
    return {
        "sql": sql + ";", "parameters": list(parameters),
        "columns": columns, "rows": rows, "comparison": comparison,
    }


def numbered_examples():
    result = []
    for n in range(1, 6):
        result.extend([
            case(f"SELECT ?2 + {n} AS second, ?1 AS first, ?2 AS repeated",
                 [[20 + n, 10, 20]], ["second", "first", "repeated"], [10, 20]),
            case(f"SELECT ?3 + {n} AS third, ?1 AS first",
                 [[30 + n, 10]], ["third", "first"], [10, 999, 30]),
            case(f"SELECT ?1 BETWEEN ?2 AND ?3 + {n} AS within",
                 [[1]], ["within"], [3, 1, 2]),
            case(f"SELECT ?1 AS absent, ?2 AS marker, '?{n}' AS quoted",
                 [[None, "NULL", f"?{n}"]], ["absent", "marker", "quoted"], [None, "NULL"]),
            case(f"WITH x(value) AS (SELECT ?2 + {n}) SELECT ?1 AS first, value AS second FROM x",
                 [[10, 20 + n]], ["first", "second"], [10, 20]),
            case(f"SELECT (SELECT ?2 + {n}) AS nested, ?1 AS first",
                 [[20 + n, 10]], ["nested", "first"], [10, 20]),
            case(f"SELECT ?1 IN (?2, ?3 + {n}) AS member, ?1 IS NULL AS absent",
                 [[1, 0]], ["member", "absent"], [2, 2, 8]),
            case(f"SELECT ?2 * {n} AS value WHERE ?1",
                 [[20 * n]], ["value"], [True, 20]),
            case(f"SELECT ?2 + {n} AS value UNION ALL SELECT ?1",
                 [[20 + n], [10]], ["value"], [10, 20], comparison="bag"),
            case(f"SELECT COUNT(*) FILTER (WHERE id >= ?2 + {n}) AS count FROM dialect_rows WHERE id <= ?1",
                 [[sum(1 for row in SQLITE_ROWS if row[0] <= 7 and row[0] >= 1 + n)]],
                 ["count"], [7, 1]),
        ])
    return result


def compound_examples():
    result = []
    for n in range(1, 6):
        result.extend([
            case(f"SELECT {n} AS value UNION SELECT {n + 1}", [[n], [n + 1]], ["value"], comparison="bag"),
            case(f"SELECT {n} AS value UNION ALL SELECT {n}", [[n], [n]], ["value"], comparison="bag"),
            case(f"SELECT {n} AS value INTERSECT SELECT {n}", [[n]], ["value"], comparison="bag"),
            case(f"SELECT {n} AS value EXCEPT SELECT {n + 1}", [[n]], ["value"], comparison="bag"),
            # SQLite associates all compound operators left-to-right. PostgreSQL
            # gives INTERSECT higher precedence and produces a different result.
            case(f"SELECT {n} AS value UNION SELECT {n + 1} INTERSECT SELECT {n + 1}",
                 [[n + 1]], ["value"], comparison="bag"),
            case(f"SELECT {n} AS value EXCEPT SELECT {n + 1} UNION ALL SELECT {n}",
                 [[n], [n]], ["value"], comparison="bag"),
            case(f"SELECT {n} AS value UNION ALL SELECT {n} INTERSECT SELECT {n}",
                 [[n]], ["value"], comparison="bag"),
            case(f"SELECT NULL AS absent_{n} UNION SELECT NULL", [[None]], [f"absent_{n}"], comparison="bag"),
            case(f"SELECT NULL AS value UNION ALL SELECT NULL EXCEPT SELECT {n}",
                 [[None]], ["value"], comparison="bag"),
            case(f"WITH x(value) AS (SELECT {n} UNION ALL SELECT {n + 1}) "
                 f"SELECT value FROM x EXCEPT SELECT {n}",
                 [[n + 1]], ["value"], comparison="bag"),
        ])
    return result


def comma_limit_examples():
    result = []
    for index in range(50):
        offset, count = index % 10, index // 10
        template = index % 5
        if template == 0:
            select = "SELECT id AS value FROM dialect_rows ORDER BY id"
            rows, names = [[row[0]] for row in SQLITE_ROWS], ["value"]
        elif template == 1:
            select = "SELECT id AS value FROM dialect_rows WHERE id >= 3 ORDER BY id DESC"
            rows, names = [[row[0]] for row in reversed(SQLITE_ROWS) if row[0] >= 3], ["value"]
        elif template == 2:
            select = "SELECT DISTINCT id AS value FROM dialect_rows ORDER BY id"
            rows, names = [[value] for value in sorted({row[0] for row in SQLITE_ROWS})], ["value"]
        elif template == 3:
            select = "SELECT id AS value, label AS text FROM dialect_rows ORDER BY id"
            rows, names = [list(row) for row in SQLITE_ROWS], ["value", "text"]
        else:
            select = "SELECT id + 10 AS shifted FROM dialect_rows ORDER BY id DESC"
            rows, names = [[row[0] + 10] for row in reversed(SQLITE_ROWS)], ["shifted"]
        result.append(case(f"{select} LIMIT {offset}, {count}", rows[offset:offset + count], names))
    return result


def numeric_scale_examples():
    result = []
    for precision in range(1, 6):
        scale = precision + 2
        unit = Decimal(1).scaleb(-scale)
        value = Decimal(precision) * unit
        text = format(value, "f")
        rounded = lambda number: format(number.quantize(unit), "f")
        type_ = f"NUMERIC({precision},{scale})"
        result.extend([
            case(f"SELECT CAST({text} AS {type_}) AS value", [[rounded(value)]], ["value"]),
            case(f"SELECT CAST('{text}' AS {type_}) AS value", [[rounded(value)]], ["value"]),
            case(f"SELECT CAST(0 AS {type_}) AS value", [[rounded(Decimal(0))]], ["value"]),
            case(f"SELECT CAST(NULL AS {type_}) AS absent", [[None]], ["absent"]),
            case(f"SELECT CAST(-{text} AS {type_}) AS value", [[rounded(-value)]], ["value"]),
            case(f"SELECT CAST({text} + {text} AS {type_}) AS value", [[rounded(value + value)]], ["value"]),
            case(f"SELECT {format(value + unit * Decimal('0.6'), 'f')}::{type_} AS rounded",
                 [[rounded(value + unit)]], ["rounded"]),
            case(f"SELECT CAST(CAST({text} AS NUMERIC({precision + 1},{scale + 1})) AS {type_}) AS nested",
                 [[rounded(value)]], ["nested"]),
            case(f"SELECT CAST({text} AS {type_}) = CAST('{text}' AS {type_}) AS equal",
                 [["t"]], ["equal"]),
            case(f"SELECT CAST($1 AS {type_}) AS a, CAST($1 AS {type_}) AS b, CAST($2 AS {type_}) AS c",
                 [[rounded(value), rounded(value), None]], ["a", "b", "c"], [text, None]),
        ])
    return result


def outputs():
    classes = {
        "sqlite_numbered_parameters": numbered_examples(),
        "sqlite_compound_queries": compound_examples(),
        "sqlite_limit_comma": comma_limit_examples(),
        "postgres_numeric_scale": numeric_scale_examples(),
    }
    for name, cases in classes.items():
        assert len(cases) == len({entry["sql"] for entry in cases}) == 50, name
        assert all("\n" not in entry["sql"] for entry in cases), name
    files = {f"{name}.sql": "\n".join(entry["sql"] for entry in cases) + "\n"
             for name, cases in classes.items()}
    files["cases.json"] = json.dumps(classes, ensure_ascii=False, indent=2) + "\n"
    return files


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--check", action="store_true")
    args = parser.parse_args()
    if not args.check:
        DESTINATION.mkdir(parents=True, exist_ok=True)
    for name, content in outputs().items():
        path = DESTINATION / name
        if args.check:
            if not path.is_file() or path.read_text() != content:
                raise SystemExit(f"Stale or missing fixture: {path.relative_to(ROOT)}")
        else:
            path.write_text(content)
    print("PASS: 200 dialect examples, 50 per new feature class" + (" match generated fixtures" if args.check else " generated"))


if __name__ == "__main__":
    main()
