#!/usr/bin/env python3
"""Author 50 JSON/JSONB extraction queries with distinct SQL NULL observations."""
import argparse
import json
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
DESTINATION = ROOT / "fixtures/json_extraction/synthetic.json"


def cases():
    rows = []
    for base in ("json", "jsonb"):
        def add(shape, expression, value, *, text=False, types="", values=()):
            sql = f"SELECT {expression} AS v;"
            result_type = "text" if text else base
            rows.append({
                "id": f"json-extraction-{len(rows)+1:02}-{base}-{shape}",
                "source_kind": "synthetic", "shape": shape, "sql": sql,
                "parameter_types": types, "parameter_values": list(values),
                # A key may be absent even when both operands are non-NULL.
                "output_columns": [{"name": "v", "type": result_type, "nullable": True}],
                "postgres_type": result_type, "postgres_display_type": result_type,
                "expected_value": value, "expected_sql_null": value is None,
                "sqlite_input": sql.replace("$", "?"), "sqlite_supported": False,
            })

        add("object-number", f"""'{{"a":1}}'::{base} -> 'a'""", "1")
        add("object-string", f"""'{{"a":"x"}}'::{base} -> 'a'""", '"x"')
        add("object-string-text", f"""'{{"a":"x"}}'::{base} ->> 'a'""", "x", text=True)
        add("array-index", f"'[10,20]'::{base} -> 0", "10")
        add("negative-index", f"'[10,20]'::{base}->>-1", "20", text=True)
        add("smallint-index", f"'[10,20]'::{base} -> 1::SMALLINT", "20")
        add("unknown-numeric-key", f"'[10,20]'::{base} -> '1'", None)
        add("missing-key", f"""'{{"a":1}}'::{base} ->> 'missing'""", None, text=True)
        add("wrong-structure", f"'7'::{base} -> 'a'", None)
        add("json-null", f"'[null]'::{base} -> 0", "null")
        add("json-null-as-text", f"'[null]'::{base} ->> 0", None, text=True)
        add("sql-null-subject", f"NULL::{base} -> 'a'", None)
        add("sql-null-key", f"""'{{"a":1}}'::{base} ->> NULL""", None, text=True)
        add("char-key-trims", f"""'{{"a":"x","a  ":"wrong"}}'::{base} ->> 'a'::CHAR(3)""",
            "x", text=True)
        add("path-literal", f"""'{{"a":["x","y"]}}'::{base} #> '{{a,0}}'""", '"x"')
        add("path-array", f"""'{{"a":["x","y"]}}'::{base} #>> ARRAY['a','1']""", "y", text=True)
        add("empty-path", f"""'{{"a":1}}'::{base} #> '{{}}'""",
            '{"a":1}' if base == "json" else '{"a": 1}')
        add("null-path-member", f"""'{{"a":1}}'::{base} #> ARRAY[NULL::TEXT]""", None)
        add("multidimensional-path",
            f"""'{{"a":{{"b":{{"c":{{"d":1}}}}}}}}'::{base} #>> ARRAY[['a','b'],['c','d']]""",
            "1", text=True)
        add("char-path-trims",
            f"""'{{"a":"x","a  ":"wrong"}}'::{base} #>> ARRAY['a'::CHAR(3)]""", "x", text=True)
        add("varchar-path", f"""'{{"a":1}}'::{base} #> ARRAY['a'::VARCHAR(3)]""", "1")
        add("anonymous", f"CAST(? AS {base}) -> ?", "20", types=f"{base},int", values=["[10,20]", 1])
        add("reordered-repeat", f"(CAST($2 AS {base}) -> $1) ->> $1", "x", text=True,
            types=f"text,{base}", values=["a", '{"a":{"a":"x"}}'])
        add("nullable-bound-path", f"CAST($1 AS {base}) #>> $2", None, text=True,
            types=f"{base}?,text[]", values=[None, "{a}"])
        add("generic-precedence", f"""'{{"a":"x"}}'::{base} ->> 'a' || 'y'""", "xy", text=True)
    assert len(rows) == len({row["sql"] for row in rows}) == 50
    return rows


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--check", action="store_true")
    args = parser.parse_args()
    content = json.dumps(cases(), indent=2) + "\n"
    if args.check:
        assert DESTINATION.read_text() == content, "stale JSON extraction fixtures"
    else:
        DESTINATION.parent.mkdir(parents=True, exist_ok=True)
        DESTINATION.write_text(content)
    print("PASS: 50 JSON extraction cases with exact result and SQL NULL expectations")


if __name__ == "__main__":
    main()
