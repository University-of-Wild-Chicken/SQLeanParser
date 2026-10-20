#!/usr/bin/env python3
"""Generate array type, cast and binding examples with authored native oracles."""
import argparse
import json
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
DESTINATION = ROOT / "fixtures/array_types/synthetic.json"

# SQL element declaration, unmodified binding type, pg_typeof spelling,
# textual array input, normalized input, normalized explicitly cast result.
ELEMENTS = [
    ("integer", "integer", "integer[]", "{1,NULL,3}", "{1,NULL,3}", "{1,NULL,3}"),
    ("bigint", "bigint", "bigint[]", "{2147483648,NULL,7}", "{2147483648,NULL,7}", "{2147483648,NULL,7}"),
    ("numeric(6,2)", "numeric", "numeric[]", "{1.234,NULL,5.678}", "{1.234,NULL,5.678}", "{1.23,NULL,5.68}"),
    ("varchar(8)", "varchar", "character varying[]", '{"alpha",NULL,"beta"}', "{alpha,NULL,beta}", "{alpha,NULL,beta}"),
    ("text", "text", "text[]", '{"a,b",NULL,"NULL"}', '{"a,b",NULL,"NULL"}', '{"a,b",NULL,"NULL"}'),
    ("boolean", "boolean", "boolean[]", "{true,NULL,false}", "{t,NULL,f}", "{t,NULL,f}"),
    ("date", "date", "date[]", "{2024-01-02,NULL,2024-02-29}", "{2024-01-02,NULL,2024-02-29}", "{2024-01-02,NULL,2024-02-29}"),
    ("uuid", "uuid", "uuid[]", "{00000000-0000-0000-0000-000000000001,NULL}",
     "{00000000-0000-0000-0000-000000000001,NULL}", "{00000000-0000-0000-0000-000000000001,NULL}"),
    ("jsonb", "jsonb", "jsonb[]", r'{"{\"a\":1}",NULL,"null"}',
     r'{"{\"a\": 1}",NULL,"null"}', r'{"{\"a\": 1}",NULL,"null"}'),
    ("bytea", "bytea", "bytea[]", r'{"\\x00",NULL,"\\x6162"}',
     r'{"\\x00",NULL,"\\x6162"}', r'{"\\x00",NULL,"\\x6162"}'),
]


def quote(value):
    return "'" + value.replace("'", "''") + "'"


def cases():
    result = []
    for index, (element, binding, postgres, value, normalized, cast_value) in enumerate(ELEMENTS, 1):
        target, unmodified = element + "[]", binding + "[]"

        def add(shape, expr, types, values, contract_type, pg_type, expected, nullable=False):
            predicate = f" WHERE CAST(NULL AS {target}) IS NULL" if shape in ("array-binding", "outer-null-test") else ""
            sql = f"SELECT {expr} AS v{predicate};"
            result.append({
                "id": f"array-types-{index:02}-{shape}", "source_kind": "synthetic", "shape": shape,
                "sql": sql, "sqlite_sql": sql.replace("$", "?"),
                "parameter_types": types, "parameter_values": values,
                "output_columns": [{"name": "v", "type": contract_type, "nullable": nullable}],
                "postgres_type": pg_type, "expected_value": expected,
                "postgres_display_type": (
                    element.replace("varchar", "character varying") + "[]"
                    if shape in ("literal-cast", "rank-spelling") else pg_type),
                "declared_element": element, "binding_element": binding,
            })

        add("literal-cast", f"CAST({quote(value)} AS {target})", "", [], target, postgres, cast_value)
        add("array-binding", "$1", unmodified, [value], unmodified, postgres, normalized)
        add("rank-spelling", f"CAST(? AS {element}[][])", "text", [value], target, postgres, cast_value)
        add("nullable-coalesce", f"COALESCE($1, CAST({quote(value)} AS {unmodified}))",
            unmodified + "?", [None], unmodified, postgres, normalized)
        add("outer-null-test", "$1 IS NOT NULL", unmodified, [value], "bool", "boolean", "true")
    assert len(result) == len({case["id"] for case in result}) == len({case["sql"] for case in result}) == 50
    return result


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--check", action="store_true")
    args = parser.parse_args()
    content = json.dumps(cases(), indent=2) + "\n"
    if args.check:
        assert DESTINATION.read_text() == content, "stale array type examples"
    else:
        DESTINATION.parent.mkdir(parents=True, exist_ok=True)
        DESTINATION.write_text(content)
    print("PASS: 50 array type/cast/binding examples over ten exact element declarations")


if __name__ == "__main__":
    main()
