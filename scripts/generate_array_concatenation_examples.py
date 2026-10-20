#!/usr/bin/env python3
"""Author 50 array concatenation cases with independent value/type expectations."""
import argparse
import json
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
DESTINATION = ROOT / "fixtures/array_concatenation/synthetic.json"


def cases():
    rows = []

    def add(shape, expression, value, *, type_="integer[]", postgres=None, display=None, nullable=False,
            types="", values=(), predicate=""):
        sql = f"SELECT {expression} AS v{predicate};"
        rows.append({
            "id": f"array-concatenation-{len(rows)+1:02}-{shape}",
            "source_kind": "synthetic", "shape": shape, "sql": sql,
            "parameter_types": types, "parameter_values": list(values),
            "output_columns": [{"name": "v", "type": type_, "nullable": nullable}],
            "postgres_type": postgres or type_, "postgres_display_type": display or postgres or type_,
            "expected_value": value, "sqlite_supported": False,
            "sqlite_input": sql.replace("$", "?"),
        })

    add("cat", "ARRAY[1,2] || ARRAY[3,4]", "{1,2,3,4}")
    add("append", "ARRAY[1,2] || 3", "{1,2,3}")
    add("prepend", "0 || ARRAY[1,2]", "{0,1,2}")
    add("unknown-right-array", "ARRAY[1] || '{2,3}'", "{1,2,3}")
    add("unknown-left-array", "'{0}' || ARRAY[1,2]", "{0,1,2}")
    add("unknown-null-right", "ARRAY[1] || NULL", "{1}")
    add("unknown-null-left", "NULL || ARRAY[1]", "{1}")
    add("both-null-arrays", "NULL::INTEGER[] || NULL::INTEGER[]", None, nullable=True)
    add("null-left-array", "NULL::INTEGER[] || ARRAY[1,NULL]", "{1,NULL}")
    add("null-right-array", "ARRAY[1,NULL] || NULL::INTEGER[]", "{1,NULL}")
    add("append-null-to-null", "NULL::INTEGER[] || NULL::INTEGER", "{NULL}")
    add("prepend-null-to-null", "NULL::INTEGER || NULL::INTEGER[]", "{NULL}")
    add("append-known-null", "ARRAY[1] || NULL::INTEGER", "{1,NULL}")
    add("prepend-null-to-empty", "NULL::INTEGER || ARRAY[]::INTEGER[]", "{NULL}")
    add("null-members", "ARRAY[1,NULL] || ARRAY[2,NULL]", "{1,NULL,2,NULL}")
    add("two-dimensional-cat", "ARRAY[[1,2]] || ARRAY[[3,4]]", "{{1,2},{3,4}}")
    add("rank-down", "ARRAY[[1,2],[3,4]] || ARRAY[5,6]", "{{1,2},{3,4},{5,6}}")
    add("rank-up", "ARRAY[1,2] || ARRAY[[3,4],[5,6]]", "{{1,2},{3,4},{5,6}}")
    add("lower-bounds-cat", "'[0:1]={1,2}'::INTEGER[] || '[9:10]={3,4}'::INTEGER[]",
        "[0:3]={1,2,3,4}")
    add("lower-bounds-append", "'[0:1]={1,2}'::INTEGER[] || 3", "[0:2]={1,2,3}")
    add("lower-bounds-prepend", "0 || '[0:1]={1,2}'::INTEGER[]", "[0:2]={0,1,2}")
    add("numeric-modifiers-erased",
        "ARRAY[1.234::NUMERIC(6,2)] || ARRAY[2.345::NUMERIC(6,2)]",
        "{1.23,2.35}", type_="numeric[]")
    add("varchar-modifiers-erased", "ARRAY['abcd'::VARCHAR(2)] || ARRAY['xyz'::VARCHAR(2)]",
        "{ab,xy}", type_="varchar[]", postgres="character varying[]")
    add("char-left-common-type", "ARRAY['a'::CHAR(3)] || ARRAY['b'::TEXT]",
        '{"a  ",b}', type_="bpchar[]", postgres="character[]", display="bpchar[]")
    add("text-left-common-type", "ARRAY['a'::TEXT] || ARRAY['b'::CHAR(3)]",
        "{a,b}", type_="text[]")
    add("smallint-bigint", "ARRAY[1::SMALLINT] || ARRAY[2147483648::BIGINT]",
        "{1,2147483648}", type_="bigint[]")
    add("integer-numeric", "ARRAY[1] || 2.5::NUMERIC", "{1,2.5}", type_="numeric[]")
    add("real-double", "1.25::REAL || ARRAY[2.5::DOUBLE PRECISION]",
        "{1.25,2.5}", type_="double precision[]")
    add("date-timestamp", "ARRAY[DATE '2024-01-01'] || TIMESTAMP '2024-01-02 12:00'",
        '{"2024-01-01 00:00:00","2024-01-02 12:00:00"}',
        type_="timestamp[]", postgres="timestamp without time zone[]")
    add("json-cat-no-equality", "ARRAY['1'::JSON] || ARRAY['null'::JSON]",
        '{1,"null"}', type_="json[]")
    add("json-append-no-equality", "ARRAY['1'::JSON] || 'null'::JSON",
        '{1,"null"}', type_="json[]")
    add("json-prepend-no-equality", "'null'::JSON || ARRAY['1'::JSON]",
        '{"null",1}', type_="json[]")
    add("jsonb-json-null-and-sql-null", "ARRAY['null'::JSONB,NULL] || ARRAY['1'::JSONB]",
        '{"null",NULL,1}', type_="jsonb[]")
    add("bytea-append", r"ARRAY['\x00'::BYTEA] || '\x61ff'::BYTEA",
        r'{"\\x00","\\x61ff"}', type_="bytea[]")
    add("uuid-prepend", "'00000000-0000-0000-0000-000000000001'::UUID || ARRAY[NULL::UUID]",
        "{00000000-0000-0000-0000-000000000001,NULL}", type_="uuid[]")
    add("boolean-cat", "ARRAY[TRUE,NULL] || ARRAY[FALSE]", "{t,NULL,f}", type_="boolean[]",
        postgres="boolean[]")
    add("timestamp-modifiers-erased",
        "ARRAY[TIMESTAMP(2) '2024-01-01 01:02:03.1234'] || TIMESTAMP(2) '2024-01-02 01:02:03.5678'",
        '{"2024-01-01 01:02:03.12","2024-01-02 01:02:03.57"}',
        type_="timestamp[]", postgres="timestamp without time zone[]")
    add("time-append", "ARRAY[TIME '12:00'] || TIME '13:30'",
        "{12:00:00,13:30:00}", type_="time[]", postgres="time without time zone[]")
    add("interval-cat", "ARRAY[INTERVAL '1 day'] || ARRAY[INTERVAL '2 hours']",
        '{"1 day",02:00:00}', type_="interval[]")
    add("nested-left-association", "ARRAY[1] || 2 || ARRAY[3] || 4", "{1,2,3,4}")
    add("nullable-case-with-empty",
        "(CASE WHEN FALSE THEN ARRAY[1] END) || ARRAY[]::INTEGER[]", "{}")
    add("coalesce-before-append", "COALESCE(NULL::INTEGER[],ARRAY[1]) || 2", "{1,2}")
    add("anonymous-arrays", "CAST(? AS INTEGER[]) || CAST(? AS INTEGER[])",
        "{1,2,3}", types="integer[],integer[]", values=["{1,2}", "{3}"])
    add("reordered-repeated-slots",
        "CAST($2 AS INTEGER[]) || CAST($1 AS INTEGER[]) || CAST($2 AS INTEGER[])",
        "{2,1,2}", types="integer[],integer[]", values=["{1}", "{2}"])
    add("nullable-append-bindings", "CAST($1 AS INTEGER[]) || $2", "{NULL}",
        types="integer[]?,integer?", values=[None, None])
    add("nullable-prepend-bindings", "$2 || CAST($1 AS INTEGER[])", "{NULL}",
        types="integer[]?,integer?", values=[None, None])
    add("nullable-cat-bindings", "CAST($1 AS INTEGER[]) || CAST($2 AS INTEGER[])",
        None, nullable=True, types="integer[]?,integer[]?", values=[None, None])
    add("binding-modifier-erasure", "CAST($1 AS NUMERIC(6,2)[]) || $2",
        "{1.23,2.345}", type_="numeric[]", types="numeric(6,2)[],numeric(6,2)",
        values=["{1.234}", "2.345"])
    add("known-text-element", "ARRAY['a'] || 'b'::TEXT", "{a,b}", type_="text[]")
    add("known-text-prepend", "'b'::TEXT || ARRAY['a']", "{b,a}", type_="text[]")
    assert len(rows) == len({row["id"] for row in rows}) == len({row["sql"] for row in rows}) == 50
    return rows


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--check", action="store_true")
    args = parser.parse_args()
    content = json.dumps(cases(), indent=2) + "\n"
    if args.check:
        assert DESTINATION.read_text() == content, "stale array concatenation examples"
    else:
        DESTINATION.parent.mkdir(parents=True, exist_ok=True)
        DESTINATION.write_text(content)
    print("PASS: 50 authored array cat/append/prepend cases with independent native expectations")


if __name__ == "__main__":
    main()
