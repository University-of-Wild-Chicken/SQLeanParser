#!/usr/bin/env python3
"""Author 50 array element/slice examples with independent native observations."""
import argparse
import json
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
DESTINATION = ROOT / "fixtures/array_subscripts/synthetic.json"


def cases():
    result = []

    def add(shape, expr, value, type_="int32", postgres="integer", display=None,
            types="", values=(), predicate=""):
        sql = f"SELECT {expr} AS v{predicate};"
        result.append({
            "id": f"array-subscripts-{len(result) + 1:02}-{shape}",
            "source_kind": "synthetic", "shape": shape, "sql": sql,
            "sqlite_sql": sql.replace("$", "?"),
            "parameter_types": types, "parameter_values": list(values),
            "output_columns": [{"name": "v", "type": type_, "nullable": True}],
            "postgres_type": postgres, "postgres_display_type": display or postgres,
            "expected_value": value,
        })

    add("element", "(ARRAY[11,22,33])[2]", "22")
    add("null-member", "(ARRAY[11,NULL,33])[2]", None)
    add("empty-array", "(ARRAY[]::INTEGER[])[1]", None)
    add("outside-bound", "(ARRAY[11,22,33])[8]", None)
    add("zero-bound", "(ARRAY[11,22,33])[0]", None)
    add("negative-bound", "(ARRAY[11,22,33])[-1]", None)
    add("null-array", "(NULL::INTEGER[])[1]", None)
    add("null-index", "(ARRAY[11,22,33])[NULL]", None)
    add("zero-lower-bound", "('[0:2]={11,22,33}'::INTEGER[])[0]", "11")
    add("negative-lower-bound", "('[-2:0]={11,22,33}'::INTEGER[])[-1]", "22")
    add("numeric-modifier", "(ARRAY[1.234,2.345]::NUMERIC(6,2)[])[2]", "2.35",
        "numeric(6,2)", "numeric", "numeric(6,2)")
    add("varchar-modifier", "(ARRAY['abcd']::VARCHAR(2)[])[1]", "ab",
        "varchar(2)", "character varying", "character varying(2)")
    add("character-modifier", "(ARRAY['abcd']::CHAR(3)[])[1]", "abc",
        "char(3)", "character", "character(3)")
    add("boolean", "(ARRAY[TRUE,FALSE])[2]", "false", "bool", "boolean")
    add("text-comma", "(ARRAY['a,b','NULL'])[1]", "a,b", "text", "text")
    add("date", "(ARRAY[DATE '2024-02-29'])[1]", "2024-02-29", "date", "date")
    add("timestamp-modifier", "(ARRAY['2024-01-02 03:04:05.1234'::TIMESTAMP(2)])[1]",
        "2024-01-02 03:04:05.12", "timestamp(2)", "timestamp without time zone",
        "timestamp(2) without time zone")
    add("jsonb", """(ARRAY['{"x":1}'::JSONB])[1]""", '{"x": 1}', "jsonb", "jsonb")
    add("bytea", r"(ARRAY['\x6162'::BYTEA])[1]", r"\x6162", "bytea", "bytea")
    add("uuid", "(ARRAY['00000000-0000-0000-0000-000000000001'::UUID])[1]",
        "00000000-0000-0000-0000-000000000001", "uuid", "uuid")
    add("integer-bound-parameter", "(ARRAY[11,22,33])[$1]", "22", types="int", values=[2])
    add("bigint-bound", "(ARRAY[11,22,33])[2::BIGINT]", "22")
    add("numeric-rounded-bound", "(ARRAY[11,22,33])[1.5]", "22")
    add("real-rounded-bound", "(ARRAY[11,22,33])[1.5::REAL]", "22")
    add("double-rounded-bound", "(ARRAY[11,22,33])[1.5::DOUBLE PRECISION]", "22")
    add("unknown-string-bound", "(ARRAY[11,22,33])['2']", "22")
    add("arithmetic-bound", "(ARRAY[11,22,33])[1+1]", "22")
    add("anonymous-base-and-bound", "(?)[?]", "22", types="integer[],int", values=["{11,22}",2])
    add("numbered-reorder-repeat", "($2)[$1+$1]", "22", types="int,integer[]", values=[1,"{11,22}"])
    add("parameter-modifier-erasure", "($1)[1]", "1.234", "numeric", "numeric",
        types="numeric(6,2)[]", values=["{1.234}"])
    array_args = ("integer[]", "integer[]")
    add("slice-closed", "(ARRAY[11,22,33])[1:2]", "{11,22}", *array_args)
    add("slice-open-lower", "(ARRAY[11,22,33])[:2]", "{11,22}", *array_args)
    add("slice-open-upper", "(ARRAY[11,22,33])[2:]", "{22,33}", *array_args)
    add("slice-open-both", "(ARRAY[11,22,33])[:]", "{11,22,33}", *array_args)
    add("slice-outside", "(ARRAY[11,22,33])[8:10]", "{}", *array_args)
    add("slice-reversed", "(ARRAY[11,22,33])[3:1]", "{}", *array_args)
    add("slice-null-lower", "(ARRAY[11,22,33])[NULL:2]", None, *array_args)
    add("slice-null-upper", "(ARRAY[11,22,33])[1:NULL]", None, *array_args)
    add("slice-null-array", "(NULL::INTEGER[])[:]", None, *array_args)
    add("slice-modifier", "(ARRAY[1.234,2.345]::NUMERIC(6,2)[])[1:1]", "{1.23}",
        "numeric(6,2)[]", "numeric[]", "numeric(6,2)[]")
    add("two-dimensional-element", "(ARRAY[[11,12],[21,22]])[1][2]", "12")
    add("insufficient-indices", "(ARRAY[[11,12],[21,22]])[1]", None)
    add("two-dimensional-slice", "(ARRAY[[11,12],[21,22]])[1:1][2:2]", "{{12}}", *array_args)
    add("element-then-slice", "(ARRAY[[11,12],[21,22]])[2][1:2]", "{{11,12},{21,22}}", *array_args)
    add("slice-then-element", "(ARRAY[[11,12],[21,22]])[2:2][2]", "{{21,22}}", *array_args)
    add("nested-slice-extraction", "((ARRAY[11,22,33])[1:2])[2]", "22")
    add("anonymous-slice-order", "(ARRAY[?,?,?])[?:?]", "{22,33}", *array_args,
        types="int,int,int,int,int", values=[11,22,33,2,3])
    add("six-dimensional", "(ARRAY[[[[[[77]]]]]])[1][1][1][1][1][1]", "77")
    add("nondefault-lower-slice", "('[0:2]={11,22,33}'::INTEGER[])[0:1]", "{11,22}", *array_args)
    add("predicate", "(ARRAY[$1,2])[1]", "1", types="int", values=[1],
        predicate=" WHERE (ARRAY[TRUE])[1]")
    assert len(result) == len({row["sql"] for row in result}) == 50
    return result


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--check", action="store_true")
    args = parser.parse_args()
    content = json.dumps(cases(), indent=2) + "\n"
    if args.check:
        assert DESTINATION.read_text() == content, "stale array subscript fixtures"
    else:
        DESTINATION.parent.mkdir(parents=True, exist_ok=True)
        DESTINATION.write_text(content)
    print("PASS: 50 distinct array element/slice examples with exact type and value metadata")


if __name__ == "__main__":
    main()
