#!/usr/bin/env python3
"""Author 50 scalar concatenation examples and independent native expectations."""
import argparse
import json
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
DESTINATION = ROOT / "fixtures/concatenation/synthetic.json"


def cases():
    rows = []

    def add(shape, expression, value, *, type_="text", nullable=False, types="", values=(),
            sqlite=False, sqlite_value=None, sqlite_override=False, portable=False, predicate=""):
        sql = f"SELECT {expression} AS v{predicate};"
        rows.append({
            "id": f"concatenation-{len(rows)+1:02}-{shape}", "source_kind": "synthetic",
            "shape": shape, "sql": sql,
            "parameter_types": types, "parameter_values": list(values),
            "output_columns": [{"name": "v", "type": type_, "nullable": nullable}],
            "postgres_type": type_, "postgres_display_type": type_, "expected_value": value,
            "sqlite_supported": sqlite, "sqlite_input": sql.replace("$", "?"),
            "sqlite_sql": sql.replace("$", "?") if portable else None,
            "sqlite_value": sqlite_value if sqlite_override else value,
        })

    add("two-strings", "'a' || 'b'", "ab", sqlite=True, portable=True)
    add("empty-string", "'' || 'x'", "x", sqlite=True, portable=True)
    add("quoted-text", "'it''s ' || 'SQL'", "it's SQL", sqlite=True, portable=True)
    add("two-null", "NULL || NULL", None, nullable=True, sqlite=True, portable=True)
    add("unknown-null", "NULL || 'x'", None, nullable=True, sqlite=True, portable=True)
    add("typed-null", "CAST(NULL AS TEXT) || 'x'::TEXT", None, nullable=True, sqlite=True)
    add("text-integer", "'x'::TEXT || 7", "x7", sqlite=True)
    add("integer-text", "7 || 'x'::TEXT", "7x", sqlite=True)
    add("varchar-length", "'abcd'::VARCHAR(2) || 'x'", "abx", sqlite=True,
        sqlite_value="abcdx", sqlite_override=True)
    add("character-padding", "'a'::CHAR(3) || 'b'", "ab", sqlite=True)
    add("unknown-integer", "'x' || 1", "x1", sqlite=True, portable=True)
    add("integer-unknown", "1 || 'x'", "1x", sqlite=True, portable=True)
    add("boolean-text", "TRUE || 'x'::TEXT", "truex", sqlite=True,
        sqlite_value="1x", sqlite_override=True)
    add("text-boolean", "'x'::TEXT || FALSE", "xfalse", sqlite=True,
        sqlite_value="x0", sqlite_override=True)
    add("numeric-modifier", "1.234::NUMERIC(6,2) || 'x'", "1.23x", sqlite=True,
        sqlite_value="1.234x", sqlite_override=True)
    add("real", "1.5::REAL || 'x'", "1.5x", sqlite=True)
    add("double", "1.25::DOUBLE PRECISION || 'x'", "1.25x", sqlite=True)
    add("date", "DATE '2024-01-01' || 'x'", "2024-01-01x")
    add("timestamp", "TIMESTAMP '2024-01-01 01:02:03' || 'x'", "2024-01-01 01:02:03x")
    add("time-zone", "TIME WITH TIME ZONE '12:00+00' || 'x'", "12:00:00+00x")
    add("interval", "INTERVAL '1 day' || 'x'", "1 dayx")
    add("uuid", "'00000000-0000-0000-0000-000000000001'::UUID || 'x'",
        "00000000-0000-0000-0000-000000000001x")
    add("json-text", """'{"a":1}'::JSON || 'x'::TEXT""", '{"a":1}x')
    add("jsonb-text", """'{"a":1}'::JSONB || 'x'::TEXT""", '{"a": 1}x')
    add("text-jsonb", """'x'::TEXT || '{"a":1}'::JSONB""", 'x{"a": 1}')
    add("bytea-text", r"'\x6162'::BYTEA || 'x'::TEXT", r"\x6162x")
    add("text-bytea", r"'x'::TEXT || '\x6162'::BYTEA", r"x\x6162")
    add("jsonb-objects", """'{"a":1}'::JSONB || '{"b":2}'::JSONB""", '{"a": 1, "b": 2}', type_="jsonb")
    add("jsonb-override", """'{"a":1}'::JSONB || '{"a":2}'::JSONB""", '{"a": 2}', type_="jsonb")
    add("jsonb-arrays", "'[1,2]'::JSONB || '[3]'::JSONB", "[1, 2, 3]", type_="jsonb")
    add("jsonb-scalars", "'1'::JSONB || '2'::JSONB", "[1, 2]", type_="jsonb")
    add("jsonb-object-array", """'{"a":1}'::JSONB || '[2]'::JSONB""", '[{"a": 1}, 2]', type_="jsonb")
    add("unknown-jsonb", """'{}' || '{"b":2}'::JSONB""", '{"b": 2}', type_="jsonb")
    add("jsonb-unknown", "'[1]'::JSONB || '[2]'", "[1, 2]", type_="jsonb")
    add("jsonb-sql-null", "NULL::JSONB || '{}'::JSONB", None, type_="jsonb", nullable=True)
    add("jsonb-json-null", "'null'::JSONB || '1'::JSONB", "[null, 1]", type_="jsonb")
    add("bytea", r"'\x6162'::BYTEA || '\x6364'::BYTEA", r"\x61626364", type_="bytea")
    add("empty-bytea", r"'\x'::BYTEA || '\x6162'::BYTEA", r"\x6162", type_="bytea")
    add("unknown-bytea", r"'\x61' || '\x62'::BYTEA", r"\x6162", type_="bytea")
    add("bytea-unknown", r"'\x61'::BYTEA || '\x62'", r"\x6162", type_="bytea")
    add("null-bytea", r"NULL::BYTEA || '\x61'::BYTEA", None, type_="bytea", nullable=True)
    add("anonymous-order", "? || ?", "ab", types="text,text", values=["a","b"],
        sqlite=True, portable=True)
    add("reordered-repeat", "$2 || $1 || $2", "x1x", types="int,text", values=[1,"x"],
        sqlite=True, portable=True)
    add("nullable-binding", "$1 || $2", None, types="text?,text", values=[None,"x"],
        nullable=True, sqlite=True, portable=True)
    add("jsonb-binding", """$1 || '{"b":2}'""", '{"a": 1, "b": 2}', type_="jsonb",
        types="jsonb", values=['{"a":1}'], sqlite=True, portable=True,
        sqlite_value='{"a":1}{"b":2}', sqlite_override=True)
    add("bytea-binding", r"$1 || ($2 || '\x'::BYTEA)", r"\x6162", type_="bytea",
        types="bytea,bytea", values=[r"\x61",r"\x62"])
    add("precedence", "'x' || 1 + 2 * 3", "x7", sqlite=True, portable=True,
        sqlite_value=6, sqlite_override=True)
    add("parenthesized-arithmetic", "(1 + 2) || 'x'", "3x", sqlite=True, portable=True)
    add("conditional", "COALESCE(NULL,'x') || CASE WHEN TRUE THEN 'y' ELSE 'z' END", "xy",
        sqlite=True, portable=True)
    add("predicate", "$1 || 'x'", "ax", types="text", values=["a"], sqlite=True, portable=True,
        predicate=" WHERE ($1 || 'x') = 'ax'")
    assert len(rows) == len({row["sql"] for row in rows}) == 50
    return rows


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--check", action="store_true")
    args = parser.parse_args()
    content = json.dumps(cases(), indent=2) + "\n"
    if args.check:
        assert DESTINATION.read_text() == content, "stale concatenation fixtures"
    else:
        DESTINATION.parent.mkdir(parents=True, exist_ok=True)
        DESTINATION.write_text(content)
    print("PASS: 50 scalar concatenation cases with exact result and dialect expectations")


if __name__ == "__main__":
    main()
