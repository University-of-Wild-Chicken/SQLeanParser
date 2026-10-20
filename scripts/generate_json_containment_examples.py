#!/usr/bin/env python3
"""Author 50 JSONB containment examples, covering both native directions."""
import argparse
import json
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
DESTINATION = ROOT / "fixtures/json_containment/synthetic.json"


def cases():
    inputs = []

    def pair(shape, left, right, value, *, nullable=False, types="", values=(), anonymous=False):
        inputs.append((shape, left, right, value, nullable, types, list(values), anonymous))

    pair("empty-objects", "'{}'::JSONB", "'{}'", "true")
    pair("object-subset", """'{"a":1,"b":2}'::JSONB""", """'{"a":1}'""", "true")
    pair("missing-key", """'{"a":1}'::JSONB""", """'{"b":1}'""", "false")
    pair("wrong-value", """'{"a":1}'::JSONB""", """'{"a":2}'""", "false")
    pair("nested-object", """'{"a":{"b":1,"c":2}}'::JSONB""", """'{"a":{"b":1}}'""", "true")
    pair("array-order", "'[1,2,3]'::JSONB", "'[3,1]'", "true")
    pair("array-duplicates", "'[1]'::JSONB", "'[1,1]'", "true")
    pair("array-missing", "'[1,2]'::JSONB", "'[3]'", "false")
    pair("array-primitive", "'[1,2]'::JSONB", "'1'", "true")
    pair("primitive-array", "'1'::JSONB", "'[1]'", "false")
    pair("object-array", """'{"a":[1,2]}'::JSONB""", """'{"a":[2]}'""", "true")
    pair("scalar-string", """'"x"'::JSONB""", """'"x"'""", "true")
    pair("scalar-different", """'"x"'::JSONB""", """'"y"'""", "false")
    pair("boolean", "'true'::JSONB", "'false'", "false")
    pair("json-null", "'null'::JSONB", "'null'", "true")
    pair("json-null-not-false", "'null'::JSONB", "'false'", "false")
    pair("sql-null", "NULL::JSONB", "'{}'", None, nullable=True)
    pair("unknown-subject", """'{"a":1}'""", "'{}'::JSONB", "true")
    pair("explicit-json-cast", """CAST('{"a":1}'::JSON AS JSONB)""", """'{"a":1}'""", "true")
    pair("anonymous", "CAST(? AS JSONB)", "CAST(? AS JSONB)", "true",
         types="jsonb,jsonb", values=['{"a":1,"b":2}', '{"a":1}'], anonymous=True)
    pair("repeated", "CAST($1 AS JSONB)", "$1", "true",
         types="jsonb", values=['{"a":1}'])
    pair("reordered", "$2", "$1", "true",
         types="jsonb,jsonb", values=['{"a":1}', '{"a":1,"b":2}'])
    pair("nullable-binding", "$1", "'{}'::JSONB", None,
         nullable=True, types="jsonb?", values=[None])
    pair("nested-extraction", """'{"a":{"b":1}}'::JSONB -> 'a'""", """'{"b":1}'""",
         "true", nullable=True)
    pair("coalesce", "COALESCE(NULL::JSONB,'{}'::JSONB)", "'{}'", "true")
    assert len(inputs) == 25
    rows = []
    for contained_by in (False, True):
        operator = "<@" if contained_by else "@>"
        direction = "contained" if contained_by else "contains"
        for shape, left, right, value, nullable, types, values, anonymous in inputs:
            if contained_by:
                left, right = right, left
                if anonymous:
                    values = list(reversed(values))
            sql = f"SELECT ({left}) {operator} ({right}) AS v;"
            rows.append({
                "id": f"json-containment-{len(rows)+1:02}-{direction}-{shape}",
                "source_kind": "synthetic", "shape": shape, "sql": sql,
                "parameter_types": types, "parameter_values": values,
                "output_columns": [{"name": "v", "type": "bool", "nullable": nullable}],
                "postgres_type": "boolean", "postgres_display_type": "boolean",
                "expected_value": value, "sqlite_input": sql.replace("$", "?"),
                "sqlite_supported": False,
            })
    assert len(rows) == len({row["sql"] for row in rows}) == 50
    return rows


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--check", action="store_true")
    args = parser.parse_args()
    content = json.dumps(cases(), indent=2) + "\n"
    if args.check:
        assert DESTINATION.read_text() == content, "stale JSON containment fixtures"
    else:
        DESTINATION.parent.mkdir(parents=True, exist_ok=True)
        DESTINATION.write_text(content)
    print("PASS: 50 JSONB containment cases with exact Boolean and NULL expectations")


if __name__ == "__main__":
    main()
