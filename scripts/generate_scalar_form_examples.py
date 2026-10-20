#!/usr/bin/env python3
"""Deterministic function/conditional witnesses with authored native oracles."""
import argparse
import json
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]

# expression, exact output, native type, value, nullability, declarations, bindings
FUNCTIONS = [
    ("abs(-7)", "int32", "integer", "7", False, "", []),
    ("abs(SMALLINT '-7')", "smallint", "smallint", "7", False, "", []),
    ("abs(BIGINT '-2147483649')", "bigint", "bigint", "2147483649", False, "", []),
    ("abs(NUMERIC '-1.25')", "numeric", "numeric", "1.25", False, "", []),
    ("abs(REAL '-1.5')", "real", "real", "1.5", False, "", []),
    ("abs(CAST('-2.5' AS DOUBLE PRECISION))", "double precision", "double precision", "2.5", False, "", []),
    ("sign(NUMERIC '-9')", "numeric", "numeric", "-1", False, "", []),
    ("ceil(NUMERIC '1.2')", "numeric", "numeric", "2", False, "", []),
    ("floor(NUMERIC '-1.2')", "numeric", "numeric", "-2", False, "", []),
    ("round(NUMERIC '1.255', 2)", "numeric", "numeric", "1.26", False, "", []),
    ("trunc(NUMERIC '-1.259', 2)", "numeric", "numeric", "-1.25", False, "", []),
    ("CAST(sqrt(CAST(9 AS DOUBLE PRECISION)) AS INT)", "int32", "integer", "3", False, "", []),
    ("CAST(cbrt(CAST(27 AS DOUBLE PRECISION)) AS INT)", "int32", "integer", "3", False, "", []),
    ("CAST(power(NUMERIC '2', NUMERIC '5') AS INT)", "int32", "integer", "32", False, "", []),
    ("div(NUMERIC '17', NUMERIC '5')", "numeric", "numeric", "3", False, "", []),
    ("mod(17, 5)", "int32", "integer", "2", False, "", []),
    ("lower('HELLO')", "text", "text", "hello", False, "", []),
    ("upper('world')", "text", "text", "WORLD", False, "", []),
    ("length('hello')", "int32", "integer", "5", False, "", []),
    ("char_length('λ猫')", "int32", "integer", "2", False, "", []),
    ("character_length(CAST('abc' AS CHAR(5)))", "int32", "integer", "3", False, "", []),
    ("octet_length('λ猫')", "int32", "integer", "5", False, "", []),
    ("length(BYTEA '\\x0001ff')", "int32", "integer", "3", False, "", []),
    ("octet_length(CAST('abc' AS CHAR(5)))", "int32", "integer", "5", False, "", []),
    ("btrim('  middle  ')", "text", "text", "middle", False, "", []),
    ("ltrim('xyxyabc', 'xy')", "text", "text", "abc", False, "", []),
    ("rtrim('abcxyxy', 'xy')", "text", "text", "abc", False, "", []),
    ("replace('ababa', 'ba', 'X')", "text", "text", "aXX", False, "", []),
    ("substr('abcdef', 3)", "text", "text", "cdef", False, "", []),
    ("substr('abcdef', 2, 3)", "text", "text", "bcd", False, "", []),
    ("substr(BYTEA '\\x00112233', 2, 2)", "bytea", "bytea", "\\x1122", False, "", []),
    ("to_date('2024-02-29', 'YYYY-MM-DD')", "date", "date", "2024-02-29", False, "", []),
    ("to_timestamp(0)", "timestamp with time zone", "timestamp with time zone", "1970-01-01 00:00:00+00", False, "", []),
    ("json_typeof(JSON '[1,2]')", "text", "text", "array", False, "", []),
    ("jsonb_typeof(JSONB 'null')", "text", "text", "null", False, "", []),
    ("json_array_length(JSON '[1,null,3]')", "int32", "integer", "3", False, "", []),
    ("jsonb_array_length(JSONB '[]')", "int32", "integer", "0", False, "", []),
    ("concat('a', NULL, 2, true)", "text", "text", "a2t", False, "", []),
    ("concat_ws('|', 'a', NULL, 'b')", "text", "text", "a|b", False, "", []),
    ("num_nulls(NULL, 1, NULL)", "int32", "integer", "2", False, "", []),
    ("num_nonnulls(NULL, 1, 'x')", "int32", "integer", "2", False, "", []),
    ("abs($1)", "int32", "integer", "12", False, "int", [-12]),
    ("lower($1)", "text", "text", "abc", False, "text", ["ABC"]),
    ("upper(?)", "text", "text", "ABC", False, "text", ["abc"]),
    ("btrim($1, $2)", "text", "text", "inner", False, "text,text", ["xxinnerxx", "x"]),
    ("length($1)", "int32", "integer", None, True, "text?", [None]),
    ("concat_ws($1, $2, 'tail')", "text", "text", None, True, "text?,text", [None, "head"]),
    ("pg_catalog.upper('safe')", "text", "text", "SAFE", False, "", []),
    ("replace(lower('ABAB'), 'ab', 'x')", "text", "text", "xx", False, "", []),
    ("abs(CAST(NULL AS BIGINT))", "bigint", "bigint", None, True, "", []),
]

CONDITIONAL = [
    ("CASE WHEN true THEN 1 ELSE 2 END", "int32", "integer", "1", False, "", []),
    ("CASE WHEN false THEN 1 ELSE 2 END", "int32", "integer", "2", False, "", []),
    ("CASE WHEN NULL THEN 1 ELSE 2 END", "int32", "integer", "2", False, "", []),
    ("CASE WHEN false THEN 1 END", "int32", "integer", None, True, "", []),
    ("CASE WHEN true THEN 'yes' ELSE 'no' END", "text", "text", "yes", False, "", []),
    ("CASE WHEN false THEN 1 WHEN true THEN 2 ELSE 3 END", "int32", "integer", "2", False, "", []),
    ("CASE WHEN 1 < 2 THEN DATE '2024-02-29' ELSE DATE '2024-03-01' END", "date", "date", "2024-02-29", False, "", []),
    ("CASE WHEN $1 THEN $2 ELSE 3 END", "int32", "integer", "7", False, "bool,int", [True, 7]),
    ("CASE WHEN $1 THEN 1 ELSE 2 END", "int32", "integer", "2", False, "bool?", [None]),
    ("CASE WHEN true THEN CAST(NULL AS TEXT) ELSE 'x' END", "text", "text", None, True, "", []),
    ("CASE 2 WHEN 1 THEN 'one' WHEN 2 THEN 'two' ELSE 'other' END", "text", "text", "two", False, "", []),
    ("CASE 'b' WHEN 'a' THEN 1 WHEN 'b' THEN 2 ELSE 3 END", "int32", "integer", "2", False, "", []),
    ("CASE NULL WHEN NULL THEN 1 ELSE 2 END", "int32", "integer", "2", False, "", []),
    ("CASE $1 WHEN 10 THEN 'ten' ELSE 'other' END", "text", "text", "ten", False, "int", [10]),
    ("CASE DATE '2024-02-29' WHEN DATE '2024-02-29' THEN true ELSE false END", "bool", "boolean", "true", False, "", []),
    ("CASE 1 WHEN 1 THEN BIGINT '2147483648' ELSE 0 END", "bigint", "bigint", "2147483648", False, "", []),
    ("CASE 9 WHEN 1 THEN 'one' END", "text", "text", None, True, "", []),
    ("CASE true WHEN true THEN NUMERIC '1.25' ELSE NUMERIC '2.5' END", "numeric", "numeric", "1.25", False, "", []),
    ("COALESCE(NULL, 3)", "int32", "integer", "3", False, "", []),
    ("COALESCE(1, 2)", "int32", "integer", "1", False, "", []),
    ("COALESCE(NULL, NULL)", "text", "text", None, True, "", []),
    ("COALESCE(NULL, 'fallback')", "text", "text", "fallback", False, "", []),
    ("COALESCE($1, 'fallback')", "text", "text", "fallback", False, "text?", [None]),
    ("COALESCE($1, $2)", "int32", "integer", None, True, "int?,int?", [None, None]),
    ("COALESCE(CAST(NULL AS DATE), DATE '2024-02-29')", "date", "date", "2024-02-29", False, "", []),
    ("COALESCE(NULL, REAL '1.5', 2)", "real", "real", "1.5", False, "", []),
    ("NULLIF(1, 1)", "int32", "integer", None, True, "", []),
    ("NULLIF(1, 2)", "int32", "integer", "1", True, "", []),
    ("NULLIF('same', 'same')", "text", "text", None, True, "", []),
    ("NULLIF($1, 0)", "int32", "integer", "4", True, "int", [4]),
    ("NULLIF(NULL, 1)", "int32", "integer", None, True, "", []),
    ("NULLIF(1, NUMERIC '2.0')", "numeric", "numeric", "1", True, "", []),
    ("NULLIF(DATE '2024-02-29', DATE '2024-03-01')", "date", "date", "2024-02-29", True, "", []),
    ("NULLIF(JSONB '{\"x\":1}', JSONB '{\"x\":1}')", "jsonb", "jsonb", None, True, "", []),
    ("GREATEST(1, 3, 2)", "int32", "integer", "3", False, "", []),
    ("GREATEST(NULL, 2)", "int32", "integer", "2", False, "", []),
    ("GREATEST(NULL, NULL)", "text", "text", None, True, "", []),
    ("GREATEST(DATE '2024-02-28', DATE '2024-02-29')", "date", "date", "2024-02-29", False, "", []),
    ("GREATEST($1, $2)", "int32", "integer", "8", False, "int?,int", [None, 8]),
    ("GREATEST(NUMERIC '1.25', NUMERIC '1.5')", "numeric", "numeric", "1.5", False, "", []),
    ("LEAST(1, 3, 2)", "int32", "integer", "1", False, "", []),
    ("LEAST(NULL, 2)", "int32", "integer", "2", False, "", []),
    ("LEAST(NULL, NULL)", "text", "text", None, True, "", []),
    ("LEAST(DATE '2024-02-28', DATE '2024-02-29')", "date", "date", "2024-02-28", False, "", []),
    ("LEAST($1, $2)", "int32", "integer", None, True, "int?,int?", [None, None]),
    ("LEAST(BIGINT '2147483649', 7)", "bigint", "bigint", "7", False, "", []),
    ("COALESCE(NULLIF(2, 2), GREATEST(3, 4))", "int32", "integer", "4", False, "", []),
    ("CASE WHEN true THEN COALESCE(NULL, 2) ELSE LEAST(3, 4) END", "int32", "integer", "2", False, "", []),
    ("CASE WHEN COALESCE($1, false) THEN upper($2) ELSE lower($2) END", "text", "text", "mixed", False, "bool?,text", [None, "MiXeD"]),
    ("CASE 1 WHEN 1 THEN CASE WHEN false THEN 2 ELSE 3 END ELSE 4 END", "int32", "integer", "3", False, "", []),
]


def examples(factor):
    cases = FUNCTIONS if factor == "functions" else CONDITIONAL
    assert len(cases) == 50
    result = [
        {"id": f"{factor}-{i:03}", "source_kind": "synthetic", "factor": factor,
         "sql": f"SELECT {expr} AS v;", "parameter_types": params, "parameter_values": values,
         "contract_type": exact, "postgres_type": native, "expected_value": value,
         "nullable": nullable}
        for i, (expr, exact, native, value, nullable, params, values) in enumerate(cases, 1)
    ]
    assert len({row["sql"] for row in result}) == 50
    return result


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--check", action="store_true")
    args = parser.parse_args()
    for factor in ("functions", "conditional"):
        path = ROOT / "fixtures" / factor / "synthetic.json"
        content = json.dumps(examples(factor), ensure_ascii=False, indent=2) + "\n"
        if args.check:
            if not path.is_file() or path.read_text() != content:
                raise SystemExit(f"stale {path}")
        else:
            path.parent.mkdir(parents=True, exist_ok=True)
            path.write_text(content)
    print("PASS: 50 function and 50 conditional synthetic witnesses")


if __name__ == "__main__":
    main()
