#!/usr/bin/env python3
"""Fifty exact-type SQL witnesses with authored PostgreSQL value/type oracles."""
import argparse
import json
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
DESTINATION = ROOT / "fixtures/extended_types/synthetic.json"

# expression, metadata declarations, separately bound values, contract type,
# PostgreSQL pg_typeof name, expected textual result, nullable output.
EXAMPLES = [
    ("SMALLINT '7'", "", [], "smallint", "smallint", "7", False),
    ("CAST($1 AS SMALLINT)", "smallint", [23], "smallint", "smallint", "23", False),
    ("CAST('32767' AS INT2)", "", [], "smallint", "smallint", "32767", False),
    ("SMALLINT '2' + SMALLINT '3'", "", [], "smallint", "smallint", "5", False),
    ("2147483648", "", [], "bigint", "bigint", "2147483648", False),
    ("-9223372036854775808", "", [], "bigint", "bigint", "-9223372036854775808", False),
    ("CAST($1 AS BIGINT) + 1", "bigint", [2147483648], "bigint", "bigint", "2147483649", False),
    ("CAST('12.3456' AS NUMERIC(8,3))", "", [], "numeric(8,3)", "numeric", "12.346", False),
    ("1.2500", "", [], "numeric", "numeric", "1.2500", False),
    ("CAST($1 AS NUMERIC(10,2))", "numeric(10,2)", ["2.50"], "numeric(10,2)", "numeric", "2.50", False),
    ("CAST('1.5' AS REAL)", "", [], "real", "real", "1.5", False),
    ("CAST('1.5' AS REAL) + CAST('2.5' AS REAL)", "", [], "real", "real", "4", False),
    ("CAST('1.5' AS REAL) + 2", "", [], "double precision", "double precision", "3.5", False),
    ("CAST($1 AS FLOAT8)", "double precision", ["2.5"], "double precision", "double precision", "2.5", False),
    ("CAST('abcdef' AS VARCHAR(3))", "", [], "varchar(3)", "character varying", "abc", False),
    ("CAST($1 AS CHARACTER VARYING(5))", "varchar(5)", ["hello"], "varchar(5)", "character varying", "hello", False),
    ("CAST('abcdef' AS CHAR(3))", "", [], "char(3)", "character", "abc", False),
    ("CAST('abc' AS CHARACTER)", "", [], "char(1)", "character", "a", False),
    ("DATE '2024-02-29'", "", [], "date", "date", "2024-02-29", False),
    ("CAST($1 AS DATE)", "date", ["2024-02-29"], "date", "date", "2024-02-29", False),
    ("DATE '2024-02-28' + 2", "", [], "date", "date", "2024-03-01", False),
    ("DATE '2024-03-01' - DATE '2024-02-28'", "", [], "int32", "integer", "2", False),
    ("TIME '12:34:56'", "", [], "time", "time without time zone", "12:34:56", False),
    ("TIME(3) '12:34:56.123456'", "", [], "time(3)", "time without time zone", "12:34:56.123", False),
    ("CAST($1 AS TIME(6))", "time(6)", ["01:02:03.456789"], "time(6)", "time without time zone", "01:02:03.456789", False),
    ("TIME WITH TIME ZONE '12:34:56+02'", "", [], "time with time zone", "time with time zone", "12:34:56+02", False),
    ("CAST($1 AS TIMETZ(3))", "timetz(3)", ["01:02:03.456+02"], "time(3) with time zone", "time with time zone", "01:02:03.456+02", False),
    ("TIMESTAMP '2024-02-29 12:34:56'", "", [], "timestamp", "timestamp without time zone", "2024-02-29 12:34:56", False),
    ("TIMESTAMP(2) '2024-02-29 12:34:56.123'", "", [], "timestamp(2)", "timestamp without time zone", "2024-02-29 12:34:56.12", False),
    ("CAST($1 AS TIMESTAMP(3))", "timestamp(3)", ["2024-02-29 12:34:56.123"], "timestamp(3)", "timestamp without time zone", "2024-02-29 12:34:56.123", False),
    ("TIMESTAMP WITH TIME ZONE '2024-02-29 12:34:56+02'", "", [], "timestamp with time zone", "timestamp with time zone", "2024-02-29 10:34:56+00", False),
    ("CAST($1 AS TIMESTAMPTZ(3))", "timestamptz(3)", ["2024-02-29 12:34:56.123+02"], "timestamp(3) with time zone", "timestamp with time zone", "2024-02-29 10:34:56.123+00", False),
    ("INTERVAL '2 days'", "", [], "interval", "interval", "2 days", False),
    ("CAST($1 AS INTERVAL(3))", "interval(3)", ["1 day 02:03:04.123"], "interval(3)", "interval", "1 day 02:03:04.123", False),
    ("DATE '2024-02-29' + INTERVAL '1 day'", "", [], "timestamp", "timestamp without time zone", "2024-03-01 00:00:00", False),
    ("TIMESTAMP '2024-03-01 12:00:00' - INTERVAL '2 hours'", "", [], "timestamp", "timestamp without time zone", "2024-03-01 10:00:00", False),
    ("UUID '00000000-0000-0000-0000-000000000001'", "", [], "uuid", "uuid", "00000000-0000-0000-0000-000000000001", False),
    ("CAST($1 AS UUID)", "uuid", ["A0EEBC99-9C0B-4EF8-BB6D-6BB9BD380A11"], "uuid", "uuid", "a0eebc99-9c0b-4ef8-bb6d-6bb9bd380a11", False),
    ("JSON '{\"b\":2,\"a\":1}'", "", [], "json", "json", '{"b":2,"a":1}', False),
    ("CAST($1 AS JSON)", "json", ['{"value":3}'], "json", "json", '{"value":3}', False),
    ("JSONB '{\"b\":2,\"a\":1}'", "", [], "jsonb", "jsonb", '{"a": 1, "b": 2}', False),
    ("CAST($1 AS JSONB)", "jsonb", ['{"value":3}'], "jsonb", "jsonb", '{"value": 3}', False),
    ("JSONB '{\"a\":1}' = JSONB '{\"a\":1}'", "", [], "bool", "boolean", "true", False),
    ("BYTEA '\\x00ff'", "", [], "bytea", "bytea", "\\x00ff", False),
    ("CAST($1 AS BYTEA)", "bytea", ["\\xdeadbeef"], "bytea", "bytea", "\\xdeadbeef", False),
    ("CAST('abc' AS BYTEA) LIKE CAST('a%' AS BYTEA)", "", [], "bool", "boolean", "true", False),
    ("CAST(NULL AS DATE)", "", [], "date", "date", None, True),
    ("CAST($1 AS TIMESTAMP(6))", "timestamp(6)?", [None], "timestamp(6)", "timestamp without time zone", None, True),
    ("CAST(NULL AS NUMERIC(12,4))", "", [], "numeric(12,4)", "numeric", None, True),
    ("-2147483648", "", [], "int32", "integer", "-2147483648", False),
]


def cases():
    result = [
        dict(id=f"extended-types-synthetic-{index:02}", source_kind="synthetic",
             sql=f"SELECT {expression} AS v;", parameter_types=types, parameter_values=values,
             contract_type=contract, postgres_type=postgres, expected_value=value, nullable=nullable)
        for index, (expression, types, values, contract, postgres, value, nullable)
        in enumerate(EXAMPLES, 1)
    ]
    assert len(result) == len({case["sql"] for case in result}) == 50
    return result


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--check", action="store_true")
    args = parser.parse_args()
    content = json.dumps(cases(), indent=2) + "\n"
    if args.check:
        assert DESTINATION.read_text() == content, "stale extended type examples"
    else:
        DESTINATION.parent.mkdir(parents=True, exist_ok=True)
        DESTINATION.write_text(content)
    print("PASS: 50 distinct exact-type synthetic SELECTs")


if __name__ == "__main__":
    main()
