#!/usr/bin/env python3
"""Generate ARRAY constructor examples with independently authored native results."""
import argparse
import json
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
DESTINATION = ROOT / "fixtures/array_constructors/synthetic.json"


def cases():
    result = []

    def add(shape, expr, type_, value, types="", values=(), display=None, postgres=None, query=None):
        sql = query or f"SELECT {expr} AS v;"
        result.append({
            "id": f"array-constructors-{len(result) + 1:02}-{shape}",
            "source_kind": "synthetic", "shape": shape, "sql": sql,
            "sqlite_sql": sql.replace("$", "?"),
            "parameter_types": types, "parameter_values": list(values),
            "output_columns": [{"name": "v", "type": type_, "nullable": False}],
            "postgres_type": postgres or type_,
            "postgres_display_type": display or postgres or type_,
            "expected_value": value,
        })

    add("integers", "ARRAY[1,2,3]", "integer[]", "{1,2,3}")
    add("arithmetic", "ARRAY[1+2,9/3,-4]", "integer[]", "{3,3,-4}")
    add("numeric-promotion", "ARRAY[1,2.5,NULL]", "numeric[]", "{1,2.5,NULL}")
    add("bigint-promotion", "ARRAY[1,2147483648]", "bigint[]", "{1,2147483648}")
    add("double", "ARRAY[1::DOUBLE PRECISION,2.5]", "double precision[]", "{1,2.5}")
    add("unknown-strings", "ARRAY['a,b','NULL','quote''d']", "text[]", '{"a,b","NULL",quote\'d}')
    add("unknown-nulls", "ARRAY[NULL,NULL]", "text[]", "{NULL,NULL}")
    add("booleans", "ARRAY[TRUE,NULL,FALSE]", "boolean[]", "{t,NULL,f}")
    add("dates", "ARRAY[DATE '2024-01-02',NULL,DATE '2024-02-29']", "date[]",
        "{2024-01-02,NULL,2024-02-29}")
    add("timestamp-modifier", "ARRAY['2024-01-02 03:04:05.1234'::TIMESTAMP(2)]",
        "timestamp(2)[]", '{"2024-01-02 03:04:05.12"}',
        postgres="timestamp without time zone[]", display="timestamp(2) without time zone[]")
    add("equal-numeric-modifiers", "ARRAY[1.234::NUMERIC(6,2),2.345::NUMERIC(6,2)]",
        "numeric(6,2)[]", "{1.23,2.35}", postgres="numeric[]", display="numeric(6,2)[]")
    add("unequal-numeric-modifiers", "ARRAY[1.234::NUMERIC(6,2),2.345::NUMERIC(7,3)]",
        "numeric[]", "{1.23,2.345}")
    add("equal-varchar-modifiers", "ARRAY['abcd'::VARCHAR(2),'efg'::VARCHAR(2)]",
        "varchar(2)[]", "{ab,ef}", postgres="character varying[]", display="character varying(2)[]")
    add("unequal-varchar-modifiers", "ARRAY['abcd'::VARCHAR(2),'efg'::VARCHAR(3)]",
        "varchar[]", "{ab,efg}", postgres="character varying[]")
    add("characters", "ARRAY['a'::CHAR(2),'bc'::CHAR(2)]", "char(2)[]", '{"a ",bc}',
        postgres="character[]", display="character(2)[]")
    add("uuid", "ARRAY['00000000-0000-0000-0000-000000000001'::UUID,NULL]", "uuid[]",
        "{00000000-0000-0000-0000-000000000001,NULL}")
    add("jsonb", """ARRAY['{"a":1}'::JSONB,'null'::JSONB,NULL]""", "jsonb[]",
        r'{"{\"a\": 1}","null",NULL}')
    add("bytea", r"ARRAY['\x00'::BYTEA,NULL,'\x6162'::BYTEA]", "bytea[]",
        r'{"\\x00",NULL,"\\x6162"}')
    add("real", "ARRAY[1.5::REAL,2::REAL]", "real[]", "{1.5,2}")
    add("interval", "ARRAY['1 day'::INTERVAL,NULL]", "interval[]", '{"1 day",NULL}')
    add("empty-integer", "ARRAY[]::INTEGER[]", "integer[]", "{}")
    add("empty-text", "CAST(ARRAY[] AS TEXT[])", "text[]", "{}")
    add("empty-nested-modifier", "ARRAY[[],[]]::NUMERIC(6,2)[][]", "numeric(6,2)[]", "{}",
        postgres="numeric[]", display="numeric(6,2)[]")
    add("empty-explicit-nested", "ARRAY[ARRAY[],ARRAY[]]::INTEGER[]", "integer[]", "{}")
    add("contextual-boolean-integer", "ARRAY[1,TRUE]::INTEGER[]", "integer[]", "{1,1}")
    add("contextual-text-integer", "ARRAY['12'::TEXT,NULL,'3']::INTEGER[]", "integer[]", "{12,NULL,3}")
    add("contextual-numeric-modifier", "ARRAY[1.234,2.345]::NUMERIC(6,2)[]",
        "numeric(6,2)[]", "{1.23,2.35}", postgres="numeric[]", display="numeric(6,2)[]")
    add("contextual-varchar-modifier", "ARRAY['abcd','efgh']::VARCHAR(2)[]",
        "varchar(2)[]", "{ab,ef}", postgres="character varying[]", display="character varying(2)[]")
    add("contextual-jsonb-integer", """ARRAY['1'::JSONB,NULL,'2'::JSONB]::INTEGER[]""",
        "integer[]", "{1,NULL,2}")
    add("constructor-to-text", "CAST(ARRAY[1,2] AS TEXT)", "text", "{1,2}")
    add("nested-shorthand", "ARRAY[[1,2],[3,4]]", "integer[]", "{{1,2},{3,4}}")
    add("nested-explicit", "ARRAY[ARRAY[1,2],ARRAY[3,4]]", "integer[]", "{{1,2},{3,4}}")
    add("three-dimensional", "ARRAY[[[1],[2]],[[3],[4]]]", "integer[]", "{{{1},{2}},{{3},{4}}}")
    add("nested-promotion", "ARRAY[ARRAY[1,2],ARRAY[3.5,4.5]]", "numeric[]", "{{1,2},{3.5,4.5}}")
    add("nested-contextual", "ARRAY[[1,TRUE],[FALSE,2]]::INTEGER[]", "integer[]", "{{1,1},{0,2}}")
    add("nested-text", "ARRAY[['a','b'],['c',NULL]]", "text[]", "{{a,b},{c,NULL}}")
    add("array-and-unknown", "ARRAY[ARRAY[1],'{2}']", "integer[]", "{{1},{2}}")
    add("coalesce-promotion", "COALESCE(ARRAY[1],ARRAY[2147483648])", "bigint[]", "{1}")
    add("case", "CASE WHEN FALSE THEN ARRAY[1] ELSE ARRAY[2,3] END", "integer[]", "{2,3}")
    add("array-equality", "ARRAY[1,NULL] = ARRAY[1,NULL]", "bool", "true", postgres="boolean")
    add("parameter-modifier-erasure", "ARRAY[$1,NULL]", "numeric[]", "{1.234,NULL}",
        "numeric(6,2)", ["1.234"])
    add("parameter-explicit-modifier", "ARRAY[CAST($1 AS NUMERIC(6,2)),NULL]", "numeric[]",
        "{1.23,NULL}", "numeric(6,2)", ["1.234"])
    add("anonymous-order", "ARRAY[[?,?],[?,?]]", "integer[]", "{{1,2},{3,4}}",
        "int,int,int,int", [1,2,3,4])
    add("numbered-order", "ARRAY[$2,$1,$2]", "integer[]", "{20,10,20}", "int,int", [10,20])
    add("nullable-element", "ARRAY[$1,2]", "integer[]", "{NULL,2}", "int?", [None])
    add("array-parameters", "ARRAY[$1,$2]", "integer[]", "{{1,2},{3,4}}",
        "integer[],integer[]", ["{1,2}", "{3,4}"])
    add("nullable-array-fallback", "ARRAY[COALESCE($1,ARRAY[1]),ARRAY[2]]", "integer[]",
        "{{1},{2}}", "integer[]?", [None])
    add("empty-cast-chain", "CAST(ARRAY[]::NUMERIC[] AS NUMERIC(6,2)[])", "numeric(6,2)[]", "{}",
        postgres="numeric[]", display="numeric(6,2)[]")
    add("nested-typed-empty", "ARRAY[ARRAY[]::INTEGER[],ARRAY[]::INTEGER[]]", "integer[]", "{}")
    add("derived-parameters", "", "integer[]", "{7,8}", "int,int", [7,8],
        query="SELECT ARRAY[d.a,d.b] AS v FROM (SELECT $1 AS a,$2 AS b) d;")
    assert len(result) == len({case["sql"] for case in result}) == 50
    return result


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--check", action="store_true")
    args = parser.parse_args()
    content = json.dumps(cases(), indent=2) + "\n"
    if args.check:
        assert DESTINATION.read_text() == content, "stale ARRAY constructor examples"
    else:
        DESTINATION.parent.mkdir(parents=True, exist_ok=True)
        DESTINATION.write_text(content)
    print("PASS: 50 distinct ARRAY constructor examples with authored value/type metadata")


if __name__ == "__main__":
    main()
