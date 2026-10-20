#!/usr/bin/env python3
"""Author context/NAME witnesses under an explicit pg_catalog search path."""
import argparse
import json
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
DIRECTORY = ROOT / "fixtures/context_values"
FUNCTIONS = [
    {"name": "current_schema", "inputs": [], "output": "name"},
    {"name": "current_database", "inputs": [], "output": "name"},
    {"name": "current_schemas", "inputs": ["boolean"], "output": "name[]"},
    {"name": "current_user", "inputs": [], "output": "name"},
    {"name": "session_user", "inputs": [], "output": "name"},
    {"name": "system_user", "inputs": [], "output": "text"},
]
CASTS = [
    {"source": source, "target": target, "context": context, "function": function}
    for source, target, context, function in (
        ("name", "text", "implicit", "text"),
        ("name", "character", "assignment", "bpchar"),
        ("name", "character varying", "assignment", "varchar"),
        ("text", "name", "implicit", "name"),
        ("character", "name", "implicit", "name"),
        ("character varying", "name", "implicit", "name"),
    )
]


def operators():
    rows = []
    for symbol, stem in (("=", "eq"), ("<>", "ne"), ("<", "lt"),
                         ("<=", "le"), (">", "gt"), (">=", "ge")):
        for left, right, function in (
            ("name", "name", "name" + stem),
            ("name", "text", "name" + stem + "text"),
            ("text", "name", "text" + stem + "name"),
        ):
            rows.append(dict(operator=symbol, left=left, right=right,
                             output="boolean", function=function))
    for symbol, function in (
        ("~~", "namelike"), ("!~~", "namenlike"),
        ("~~*", "nameiclike"), ("!~~*", "nameicnlike"),
        ("~", "nameregexeq"), ("!~", "nameregexne"),
        ("~*", "nameicregexeq"), ("!~*", "nameicregexne"),
    ):
        rows.append(dict(operator=symbol, left="name", right="text",
                         output="boolean", function=function))
    assert len(rows) == 26
    return rows


def cases():
    rows = []

    def add(shape, expression, type_, value, nullable=False, types="", values=(),
            native=None, display=None):
        postgres = {"bool": "boolean", "int32": "integer", "varchar(3)": "character varying",
                    "char(12)": "character"}.get(type_, type_)
        descriptor = {"varchar(3)": "character varying(3)", "char(12)": "character(12)"}.get(type_, postgres)
        rows.append({
            "id": f"context-values-{len(rows)+1:02}-{shape}",
            "source_kind": "synthetic", "shape": shape,
            "sql": f"SELECT {expression} AS v;",
            "postgres_input": f"SELECT {native or expression} AS v;",
            "parameter_types": types, "parameter_values": list(values),
            "output_columns": [{"name": "v", "type": type_, "nullable": nullable}],
            "postgres_type": postgres, "postgres_display_type": display or descriptor,
            "expected_value": value, "expected_sql_null": value is None,
            "search_path": "pg_catalog", "sqlite_supported": False,
            "sqlite_input": f"SELECT {expression} AS v;".replace("$", "?"),
        })

    add("schema-keyword", "CURRENT_SCHEMA", "name", "pg_catalog", True)
    add("schema-call", "current_schema()", "name", "pg_catalog", True)
    add("qualified-schema-call", "pg_catalog.current_schema()", "name", "pg_catalog", True)
    add("quoted-schema-call", '"current_schema"()', "name", "pg_catalog", True)
    add("catalog-spellings", "CURRENT_CATALOG = current_database()", "bool", "true")
    add("current-user-spellings", 'CURRENT_USER = "current_user"()', "bool", "true")
    add("user-synonym", "USER = CURRENT_USER", "bool", "true")
    add("role-synonym", "CURRENT_ROLE = CURRENT_USER", "bool", "true")
    add("session-spellings", 'SESSION_USER = "session_user"()', "bool", "true")
    add("system-spellings", 'COALESCE(SYSTEM_USER, \'\') = COALESCE("system_user"(), \'\')', "bool", "true")
    add("explicit-search-path", "current_schemas(FALSE)", "name[]", "{pg_catalog}")
    # pg_temp can be implicitly visible after the harness creates its capture
    # functions. Assert membership, not a fabricated fixed temporary namespace.
    add("implicit-search-path", "current_schemas(TRUE) @> ARRAY['pg_catalog'::NAME]", "bool", "true")
    add("null-schemas-argument", "current_schemas(NULL)", "name[]", None, True)
    add("numbered-schemas", "current_schemas($1)", "name[]", "{pg_catalog}", types="bool", values=[False])
    add("anonymous-schemas", "current_schemas(?) @> ARRAY['pg_catalog'::NAME]", "bool", "true",
        types="bool", values=[True], native="current_schemas($1) @> ARRAY['pg_catalog'::NAME]")
    add("nullable-schemas-binding", "current_schemas(CAST($1 AS BOOLEAN))", "name[]", None, True, "bool?", [None])
    add("unknown-fallback", "COALESCE(CURRENT_SCHEMA, 'fallback')", "name", "pg_catalog")
    add("name-first-common-type", "COALESCE(CURRENT_SCHEMA, 'fallback'::TEXT)", "name", "pg_catalog")
    add("text-first-common-type", "COALESCE('fixed'::TEXT, CURRENT_SCHEMA)", "text", "fixed")
    add("case-unknown-else", "CASE WHEN TRUE THEN CURRENT_SCHEMA ELSE 'fallback' END",
        "name", "pg_catalog", True)
    add("case-text-else", "CASE WHEN TRUE THEN CURRENT_SCHEMA ELSE 'fallback'::TEXT END",
        "text", "pg_catalog", True)
    add("explicit-text-cast", "CAST(CURRENT_SCHEMA AS TEXT)", "text", "pg_catalog", True)
    add("explicit-varchar-cast", "CAST(CURRENT_SCHEMA AS VARCHAR(3))", "varchar(3)", "pg_", True)
    add("explicit-char-cast", "CAST(CURRENT_SCHEMA AS CHAR(12))", "char(12)", "pg_catalog", True)
    add("name-byte-limit", "COALESCE(NULLIF(CURRENT_SCHEMA, CURRENT_SCHEMA), $1::NAME)",
        "name", "x" * 63, types="text", values=["x" * 70])
    add("name-unicode-byte-limit", "COALESCE(NULLIF(CURRENT_SCHEMA, CURRENT_SCHEMA), CAST($1 AS NAME))",
        "name", "é" * 31, types="varchar", values=["é" * 40])
    add("exact-name-cast", "CAST(CURRENT_SCHEMA AS NAME)", "name", "pg_catalog", True)
    for operator, shape, value in (
        ("=", "equal", "true"), ("<>", "not-equal", "false"), ("<", "less", "false"),
        ("<=", "less-equal", "true"), (">", "greater", "false"), (">=", "greater-equal", "true"),
    ):
        add("name-" + shape, f"CURRENT_SCHEMA {operator} 'pg_catalog'::NAME", "bool", value, True)
    add("name-text-comparison", "CURRENT_SCHEMA = $1", "bool", "true", True, "text", ["pg_catalog"])
    add("text-name-comparison", "$1 = CURRENT_SCHEMA", "bool", "true", True, "text", ["pg_catalog"])
    add("char-name-comparison", "CURRENT_SCHEMA = 'pg_catalog'::CHAR(12)", "bool", "true", True)
    for shape, expression in (
        ("like", "CURRENT_SCHEMA LIKE 'pg_%'"),
        ("not-like", "CURRENT_SCHEMA NOT LIKE 'x%'"),
        ("ilike", "CURRENT_SCHEMA ILIKE 'PG_%'"),
        ("regex", "CURRENT_SCHEMA ~ '^pg_'"),
        ("negative-regex", "CURRENT_SCHEMA !~ '^no'"),
        ("casefold-regex", "CURRENT_SCHEMA ~* '^PG_'"),
        ("negative-casefold-regex", "CURRENT_SCHEMA !~* '^NO'"),
    ):
        add(shape, expression, "bool", "true", True)
    add("length-name", "length(CURRENT_SCHEMA)", "int32", "10", True)
    add("bytea-encoding-name", "length('abc'::BYTEA, COALESCE(NULLIF(CURRENT_SCHEMA, CURRENT_SCHEMA), 'UTF8'::NAME))",
        "int32", "3")
    add("name-array-constructor", "ARRAY[CURRENT_SCHEMA]", "name[]", "{pg_catalog}")
    add("name-array-equality", "ARRAY[CURRENT_SCHEMA] = ARRAY['pg_catalog'::NAME]", "bool", "true")
    add("name-any", "CURRENT_SCHEMA = ANY(ARRAY['pg_catalog'::NAME])", "bool", "true", True)
    add("nullif-context", "NULLIF(CURRENT_SCHEMA, CURRENT_SCHEMA)", "name", None, True)
    add("name-array-subscript", "(current_schemas(FALSE))[1]", "name", "pg_catalog", True)
    assert len(rows) == len({row["id"] for row in rows}) == len({row["sql"] for row in rows}) == 50
    return rows


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--check", action="store_true")
    args = parser.parse_args()
    for name, value in (
        ("synthetic.json", cases()), ("function_signatures.json", FUNCTIONS),
        ("operator_signatures.json", operators()), ("cast_signatures.json", CASTS),
    ):
        content = json.dumps(value, ensure_ascii=False, indent=2) + "\n"
        path = DIRECTORY / name
        if args.check:
            assert path.read_text() == content, f"stale {path}"
        else:
            DIRECTORY.mkdir(parents=True, exist_ok=True)
            path.write_text(content)
    print("PASS: 50 context/NAME queries, six functions, 26 operators and six casts")


if __name__ == "__main__":
    main()
