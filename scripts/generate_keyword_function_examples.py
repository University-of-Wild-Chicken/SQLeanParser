#!/usr/bin/env python3
"""Author fifty LEFT/RIGHT witnesses with independently stated native results."""
import argparse
import json
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
DIRECTORY = ROOT / "fixtures/keyword_functions"
SIGNATURES = [{"name": name, "inputs": ["text", "integer"], "output": "text"}
              for name in ("left", "right")]


def cases():
    rows = []
    for function in ("left", "right"):
        left = function == "left"

        def add(shape, expression, value, nullable=False, types="", values=(),
                type_="text", native=None):
            rows.append({
                "id": f"keyword-functions-{len(rows)+1:02}-{function}-{shape}",
                "source_kind": "synthetic", "shape": function + "-" + shape,
                "sql": f"SELECT {expression} AS v;",
                "postgres_input": f"SELECT {native or expression} AS v;",
                "parameter_types": types, "parameter_values": list(values),
                "output_columns": [{"name": "v", "type": type_, "nullable": nullable}],
                "postgres_type": "boolean" if type_ == "bool" else type_,
                "postgres_display_type": "boolean" if type_ == "bool" else type_,
                "expected_value": value, "expected_sql_null": value is None,
                "sqlite_supported": False,
                "sqlite_input": f"SELECT {expression} AS v;".replace("$", "?"),
            })

        add("ascii", f"{function}('abcdef',2)", "ab" if left else "ef")
        add("zero", f"{function}('abcdef',0)", "")
        add("negative", f"{function}('abcdef',-2)", "abcd" if left else "cdef")
        add("int32-maximum", f"{function}('abcdef',2147483647)", "abcdef")
        add("empty", f"{function}('',2)", "")
        add("unicode", f"{function}('é😀abc',2)", "é😀" if left else "bc")
        add("combining-codepoints", f"{function}('e\u0301xy',1)", "e" if left else "y")
        add("char-padding", f"{function}('a  '::CHAR(4),2)", "a")
        add("varchar-padding", f"{function}('a  '::VARCHAR(4),2)", "a " if left else "  ")
        add("name-input", f"{function}('abcde'::NAME,2)", "ab" if left else "de")
        add("unknown-count", f"{function}('abcdef','2')", "ab" if left else "ef")
        add("smallint-count", f"{function}('abcdef',2::SMALLINT)", "ab" if left else "ef")
        add("numbered-reversed", f"{function}($2,$1)", "ab" if left else "ef",
            types="integer,text", values=[2, "abcdef"])
        add("anonymous", f"{function}(?,?)", "abc" if left else "def",
            types="text,integer", values=["abcdef", 3], native=f"{function}($1,$2)")
        add("nullable-text", f"{function}($1,$2)", None, True, "text?,integer", [None, 2])
        add("nullable-count", f"{function}($2,CAST($1 AS INTEGER))", None, True, "integer?,text", [None, "abc"])
        add("null-subject", f"{function}(NULL,2)", None, True)
        add("null-count", f"{function}('abc',NULL)", None, True)
        add("null-both", f"{function}(NULL,NULL)", None, True)
        add("explicit-numeric-conversion", f"{function}('abcdef',CAST(2.6 AS INTEGER))", "abc" if left else "def")
        add("count-expression", f"{function}('abcdef',1+1)", "ab" if left else "ef")
        add("nested-length", f"{function}('abcdef',length('ab'))", "ab" if left else "ef")
        add("coalesce", f"COALESCE({function}(NULL,2),{function}('abcdef',3))", "abc" if left else "def")
        add("qualified", f"pg_catalog.{function}('abcde',3)", "abc" if left else "cde")
        add("comparison", f"{function}('abc',1) = '{'a' if left else 'c'}'", "true", type_="bool")
    assert len(rows) == len({r["id"] for r in rows}) == len({r["sql"] for r in rows}) == 50
    return rows


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--check", action="store_true")
    args = parser.parse_args()
    for name, value in (("synthetic.json", cases()), ("function_signatures.json", SIGNATURES)):
        path = DIRECTORY / name
        content = json.dumps(value, ensure_ascii=False, indent=2) + "\n"
        if args.check:
            assert path.read_text() == content, f"stale {path}"
        else:
            DIRECTORY.mkdir(parents=True, exist_ok=True)
            path.write_text(content)
    print("PASS: 50 keyword-function queries and two exact TEXT/INTEGER declarations")


if __name__ == "__main__":
    main()
