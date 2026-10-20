#!/usr/bin/env python3
"""Author 50 containment and 50 overlap cases with explicit native expectations."""
import argparse
import json
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]


def record(factor, index, shape, expression, value, nullable=False, types="", values=()):
    sql = f"SELECT {expression} AS v;"
    return {
        "id": f"{factor.replace('_', '-')}-{index:02}-{shape}",
        "source_kind": "synthetic", "shape": shape, "sql": sql,
        "parameter_types": types, "parameter_values": list(values),
        "output_columns": [{"name": "v", "type": "bool", "nullable": nullable}],
        "postgres_type": "boolean", "postgres_display_type": "boolean",
        "expected_value": value, "sqlite_input": sql.replace("$", "?"),
        "sqlite_supported": False,
    }


def containment_cases():
    inputs = []

    def pair(shape, left, right, value, nullable=False, types="", values=(), anonymous=False):
        inputs.append((shape, left, right, value, nullable, types, list(values), anonymous))

    pair("empty", "ARRAY[]::INTEGER[]", "ARRAY[]::INTEGER[]", "true")
    pair("empty-right", "ARRAY[NULL,1]", "ARRAY[]::INTEGER[]", "true")
    pair("empty-left", "ARRAY[]::INTEGER[]", "ARRAY[1]", "false")
    pair("duplicates", "ARRAY[1]", "ARRAY[1,1]", "true")
    pair("missing", "ARRAY[1,2]", "ARRAY[2,3]", "false")
    pair("null-right-member", "ARRAY[1,NULL]", "ARRAY[NULL,1]", "false")
    pair("null-left-member", "ARRAY[NULL,1]", "ARRAY[1]", "true")
    pair("null-members", "ARRAY[NULL]::INTEGER[]", "ARRAY[NULL]::INTEGER[]", "false")
    pair("sql-null-left", "NULL::INTEGER[]", "ARRAY[1]", None, True)
    pair("sql-null-right", "ARRAY[1]", "NULL::INTEGER[]", None, True)
    pair("dimensions", "ARRAY[[1,2],[3,4]]", "ARRAY[4,1]", "true")
    pair("lower-bounds", "'[0:1]={1,2}'::INTEGER[]", "'[9:9]={2}'::INTEGER[]", "true")
    pair("unknown-right", "ARRAY[1,2]", "'{2,1}'", "true")
    pair("unknown-left", "'{1,2}'", "ARRAY[2]", "true")
    pair("numeric-modifiers", "ARRAY[1.20::NUMERIC(8,2)]", "ARRAY[1.2::NUMERIC(5,1)]", "true")
    pair("char-padding", "ARRAY['a'::CHAR(3)]", "ARRAY['a'::CHAR(5)]", "true")
    pair("jsonb-not-containment", """ARRAY['{"a":1,"b":2}'::JSONB]""",
         """ARRAY['{"a":1}'::JSONB]""", "false")
    pair("jsonb-equality", """ARRAY['{"a":1,"b":2}'::JSONB]""",
         """ARRAY['{"b":2,"a":1}'::JSONB]""", "true")
    pair("numeric-nan", "ARRAY['NaN'::NUMERIC]", "ARRAY['NaN'::NUMERIC]", "true")
    pair("float-nan", "ARRAY['NaN'::DOUBLE PRECISION]", "ARRAY['NaN'::DOUBLE PRECISION]", "true")
    pair("anonymous", "CAST(? AS INTEGER[])", "CAST(? AS INTEGER[])", "true",
         types="integer[],integer[]", values=["{1,2}", "{2}"], anonymous=True)
    pair("reordered", "$2", "$1", "true", types="integer[],integer[]", values=["{2}", "{1,2}"])
    pair("repeated", "CAST($1 AS INTEGER[])", "$1", "true", types="integer[]", values=["{1,2}"])
    pair("nullable-binding", "$1", "ARRAY[1]", None, True, "integer[]?", [None])
    pair("concat-coalesce", "COALESCE(NULL::INTEGER[],ARRAY[1]) || 2", "ARRAY[2]", "true")
    assert len(inputs) == 25
    rows = []
    for contained_by in (False, True):
        for shape, left, right, value, nullable, types, values, anonymous in inputs:
            if contained_by:
                left, right = right, left
                if anonymous:
                    values = list(reversed(values))
            operator = "<@" if contained_by else "@>"
            direction = "contained" if contained_by else "contains"
            rows.append(record("array_containment", len(rows) + 1, direction + "-" + shape,
                               f"({left}) {operator} ({right})", value, nullable, types, values))
    return rows


def overlap_cases():
    inputs = []

    def pair(shape, left, right, value, nullable=False, types="", values=()):
        inputs.append((shape, left, right, value, nullable, types, values))

    pair("empty-both", "ARRAY[]::INTEGER[]", "ARRAY[]::INTEGER[]", "false")
    pair("empty-left", "ARRAY[]::INTEGER[]", "ARRAY[1]", "false")
    pair("empty-right", "ARRAY[1]", "ARRAY[]::INTEGER[]", "false")
    pair("duplicates", "ARRAY[1,1]", "ARRAY[1,1,1]", "true")
    pair("disjoint", "ARRAY[1,2]", "ARRAY[3,4]", "false")
    pair("sql-null-left", "NULL::INTEGER[]", "ARRAY[1]", None, True)
    pair("sql-null-right", "ARRAY[1]", "NULL::INTEGER[]", None, True)
    pair("sql-null-both", "NULL::INTEGER[]", "NULL::INTEGER[]", None, True)
    pair("null-members", "ARRAY[NULL]::INTEGER[]", "ARRAY[NULL]::INTEGER[]", "false")
    pair("null-and-equal", "ARRAY[NULL,1]", "ARRAY[1,NULL]", "true")
    pair("null-and-disjoint", "ARRAY[NULL,1]", "ARRAY[2,NULL]", "false")
    pair("multidimensional", "ARRAY[[1,2],[3,4]]", "ARRAY[[4,5]]", "true")
    pair("rank-independent", "ARRAY[[1,2]]", "ARRAY[2]", "true")
    pair("lower-bounds", "'[-2:-1]={1,2}'::INTEGER[]", "'[9:9]={2}'::INTEGER[]", "true")
    pair("unknown-left", "'{1,2}'", "ARRAY[2]", "true")
    pair("unknown-right", "ARRAY[2]", "'{1,2}'", "true")
    pair("numeric-nan", "ARRAY['NaN'::NUMERIC]", "ARRAY['NaN'::NUMERIC]", "true")
    pair("float-nan", "ARRAY['NaN'::REAL]", "ARRAY['NaN'::REAL]", "true")
    pair("jsonb-equality", """ARRAY['{"a":1,"b":2}'::JSONB]""",
         """ARRAY['{"b":2,"a":1}'::JSONB]""", "true")
    pair("jsonb-not-containment", """ARRAY['{"a":1,"b":2}'::JSONB]""",
         """ARRAY['{"a":1}'::JSONB]""", "false")
    pair("char-padding", "ARRAY['a'::CHAR(3)]", "ARRAY['a'::CHAR(5)]", "true")
    pair("anonymous", "CAST(? AS INTEGER[])", "CAST(? AS INTEGER[])", "true",
         types="integer[],integer[]", values=["{1,2}", "{2,3}"])
    pair("reordered", "$2", "$1", "false", types="integer[],integer[]", values=["{3}", "{1,2}"])
    pair("repeated", "CAST($1 AS INTEGER[])", "$1", "true", types="integer[]", values=["{1,2}"])
    pair("nullable-binding", "$1", "ARRAY[1]", None, True, "integer[]?", [None])
    pair("coalesce", "COALESCE(NULL::INTEGER[],ARRAY[1])", "ARRAY[1]", "true")
    pair("concat", "ARRAY[1] || 2", "ARRAY[2]", "true")
    pair("slice", "(ARRAY[1,2,3])[2:3]", "ARRAY[3]", "true", True)
    pair("negative", "ARRAY[-2,-1]", "ARRAY[-1,0]", "true")
    pair("unknown-null", "ARRAY[1]", "NULL", None, True)
    pair("case-array", "CASE WHEN TRUE THEN ARRAY[1] ELSE NULL::INTEGER[] END",
         "ARRAY[1]", "true", True)
    assert len(inputs) == 31
    for name, declaration, value in [
        ("smallint", "SMALLINT", "2"), ("integer", "INTEGER", "2"),
        ("bigint", "BIGINT", "2"), ("numeric", "NUMERIC(8,2)", "1.25"),
        ("real", "REAL", "1.5"), ("double", "DOUBLE PRECISION", "1.5"),
        ("text", "TEXT", "'x'"), ("varchar", "VARCHAR(3)", "'x'"),
        ("char", "CHAR(3)", "'x'"), ("boolean", "BOOLEAN", "TRUE"),
        ("date", "DATE", "'2025-01-02'"), ("time", "TIME(3)", "'12:00:01.234'"),
        ("timetz", "TIME(3) WITH TIME ZONE", "'12:00:01.234+02'"),
        ("timestamp", "TIMESTAMP(3)", "'2025-01-02 12:00:01.234'"),
        ("timestamptz", "TIMESTAMP(3) WITH TIME ZONE", "'2025-01-02 12:00:01.234+02'"),
        ("interval", "INTERVAL(3)", "'1 day'"),
        ("uuid", "UUID", "'12345678-1234-1234-1234-123456789012'"),
        ("jsonb", "JSONB", "'null'"), ("bytea", "BYTEA", r"'\x00ff'"),
    ]:
        pair("element-" + name, f"ARRAY[{value}::{declaration}]",
             f"ARRAY[NULL::{declaration},{value}::{declaration}]", "true")
    return [record("array_overlap", index, shape, f"({left}) && ({right})",
                   value, nullable, types, values)
            for index, (shape, left, right, value, nullable, types, values) in enumerate(inputs, 1)]


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--check", action="store_true")
    args = parser.parse_args()
    for factor, rows in (("array_containment", containment_cases()), ("array_overlap", overlap_cases())):
        assert len(rows) == len({row["sql"] for row in rows}) == len({row["id"] for row in rows}) == 50
        destination = ROOT / "fixtures" / factor / "synthetic.json"
        content = json.dumps(rows, indent=2) + "\n"
        if args.check:
            assert destination.read_text() == content, f"stale {factor} fixtures"
        else:
            destination.parent.mkdir(parents=True, exist_ok=True)
            destination.write_text(content)
        print(f"PASS: 50 authored {factor} cases with exact Boolean/NULL expectations")


if __name__ == "__main__":
    main()
