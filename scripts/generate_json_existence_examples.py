#!/usr/bin/env python3
"""Author 50 JSONB existence queries with independent Boolean/NULL expectations."""
import argparse
import json
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
DIRECTORY = ROOT / "fixtures/json_existence"
SIGNATURES = [
    {"operator": "?", "left": "jsonb", "right": "text",
     "output": "boolean", "function": "jsonb_exists"},
    {"operator": "?|", "left": "jsonb", "right": "text[]",
     "output": "boolean", "function": "jsonb_exists_any"},
    {"operator": "?&", "left": "jsonb", "right": "text[]",
     "output": "boolean", "function": "jsonb_exists_all"},
]


def cases():
    result = []

    def add(kind, shape, left, right, value, nullable=False, types="", values=(),
            expression=None, native_expression=None):
        operator = {"key": "?", "any": "?|", "all": "?&"}[kind]
        sql = "SELECT " + (expression or f"({left}) {operator} ({right})") + " AS v;"
        result.append({
            "id": f"json-existence-{len(result)+1:02}-{kind}-{shape}",
            "source_kind": "synthetic", "operator_kind": kind, "shape": shape,
            "sql": sql, "postgres_input": "SELECT " + native_expression + " AS v;" if native_expression else sql,
            "parameter_types": types, "parameter_values": list(values),
            "output_columns": [{"name": "v", "type": "bool", "nullable": nullable}],
            "postgres_type": "boolean", "postgres_display_type": "boolean",
            "expected_value": value, "expected_sql_null": value is None,
            "sqlite_input": sql.replace("$", "?"), "sqlite_supported": False,
        })

    add("key", "object-key", """'{"a":1}'::JSONB""", "'a'", "true")
    add("key", "missing-key", """'{"a":1}'::JSONB""", "'b'", "false")
    add("key", "json-null-value", """'{"a":null}'::JSONB""", "'a'", "true")
    add("key", "top-level-only", """'{"nested":{"a":1}}'::JSONB""", "'a'", "false")
    add("key", "array-string", """'["a","b"]'::JSONB""", "'b'", "true")
    add("key", "array-numeric-not-string", "'[1,true,null]'::JSONB", "'1'", "false")
    add("key", "scalar-string", """'"a"'::JSONB""", "'a'", "true")
    add("key", "json-null-subject", "'null'::JSONB", "'null'", "false")
    add("key", "sql-null-subject", "NULL::JSONB", "'a'", None, True)
    add("key", "sql-null-key", """'{"a":1}'::JSONB""", "NULL", None, True)
    add("key", "unknown-both", """'{"a":1}'""", "'a'", "true")
    add("key", "varchar-key", """'{"a":1}'::JSONB""", "'a'::VARCHAR(4)", "true")
    add("key", "char-padding", """'{"a":1}'::JSONB""", "'a'::CHAR(4)", "true")
    add("key", "unicode-question-key", """'{"?表":1}'::JSONB""", "'?表'", "true")
    add("key", "empty-key", """'{"":1}'::JSONB""", "''", "true")
    add("key", "anonymous", "", "", "true", types="jsonb,text", values=['{"a":1}', "a"],
        expression="? ? ?", native_expression="$1 ? $2")
    add("key", "compact-anonymous", "", "", "true", types="jsonb,text", values=['{"a":1}', "a"],
        expression="CAST(? AS JSONB)??", native_expression="CAST($1 AS JSONB)?$2")
    add("key", "repeated-binding", "CAST($1 AS JSONB)", "$1", "false", types="text", values=['"a"'])
    add("key", "reordered-binding", "$2", "$1", "true", types="text,jsonb", values=["a", '{"a":1}'])
    add("key", "nested-extraction", """'{"nested":{"a":1}}'::JSONB -> 'nested'""", "'a'", "true", True)

    for kind in ("any", "all"):
        is_all = kind == "all"
        add(kind, "one-missing", """'{"a":1,"b":2}'::JSONB""", "ARRAY['a','missing']",
            "false" if is_all else "true")
        add(kind, "both-present", """'{"a":1,"b":2}'::JSONB""", "ARRAY['b','a']", "true")
        add(kind, "empty-keys", "'{}'::JSONB", "ARRAY[]::TEXT[]", "true" if is_all else "false")
        add(kind, "null-member", """'{"a":1}'::JSONB""", "ARRAY['a',NULL]", "true")
        add(kind, "only-null-members", "'{}'::JSONB", "ARRAY[NULL]::TEXT[]",
            "true" if is_all else "false")
        add(kind, "null-subject-empty-keys", "NULL::JSONB", "ARRAY[]::TEXT[]", None, True)
        add(kind, "null-key-array", """'{"a":1}'::JSONB""", "NULL::TEXT[]", None, True)
        add(kind, "json-null-subject", "'null'::JSONB", "ARRAY['a']", "false")
        add(kind, "unknown-subject", """'{"a":1}'""", "ARRAY['a']", "true")
        add(kind, "unknown-key-array", """'{"a":1}'::JSONB""", "'{a}'", "true")
        add(kind, "char-array-padding", """'{"a":1}'::JSONB""", "ARRAY['a'::CHAR(4)]", "true")
        add(kind, "multidimensional", """'{"a":1,"b":2}'::JSONB""",
            "ARRAY[['a',NULL],['b','missing']]", "false" if is_all else "true")
        add(kind, "nondefault-bounds", """'{"a":1,"b":2}'::JSONB""",
            "'[-2:-1]={a,b}'::TEXT[]", "true")
        add(kind, "anonymous", "?", "?", "false" if is_all else "true",
            types="jsonb,text[]", values=['{"a":1}', "{missing,a}"],
            native_expression=f"($1) {'?&' if is_all else '?|'} ($2)")
        add(kind, "nullable-binding", "$1", "$2", None, True,
            "jsonb,text[]?", ["{}", None])
    assert len(result) == len({c["id"] for c in result}) == len({c["sql"] for c in result}) == 50
    return result


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--check", action="store_true")
    args = parser.parse_args()
    for name, value in (("synthetic.json", cases()), ("function_signatures.json", SIGNATURES)):
        content = json.dumps(value, indent=2) + "\n"
        path = DIRECTORY / name
        if args.check:
            assert path.read_text() == content, f"stale {path}"
        else:
            DIRECTORY.mkdir(parents=True, exist_ok=True)
            path.write_text(content)
    print("PASS: 50 JSONB existence queries and three exact operator/function signatures")


if __name__ == "__main__":
    main()
