#!/usr/bin/env python3
"""Author 50 row-comparison SELECTs with explicit type and value expectations."""
import argparse
import json
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
DESTINATION = ROOT / "fixtures/row_comparisons/synthetic.json"


def cases():
    rows = []

    def add(shape, expression, value, *, types="", values=(), sqlite=False, predicate=""):
        sql = f"SELECT {expression} AS v{predicate};"
        rows.append({
            "id": f"row-comparison-{len(rows)+1:02}-{shape}",
            "source_kind": "synthetic", "shape": shape, "sql": sql,
            "sqlite_sql": sql.replace("ROW(", "(").replace("$", "?") if sqlite else None,
            "parameter_types": types, "parameter_values": list(values),
            "output_columns": [{"name": "v", "type": "bool", "nullable": True}],
            "postgres_type": "boolean", "postgres_display_type": "boolean",
            "expected_value": None if value is None else ("true" if value else "false"),
            "sqlite_value": None if value is None else int(value),
        })

    for name, operator, result in (
            ("eq", "=", False), ("ne", "<>", True), ("lt", "<", True),
            ("le", "<=", True), ("gt", ">", False), ("ge", ">=", False)):
        add("second-field-" + name, f"(1,2) {operator} (1,3)", result, sqlite=True)
    for name, operator, result in (
            ("eq", "=", False), ("ne", "<>", True), ("lt", "<", False),
            ("le", "<=", False), ("gt", ">", True), ("ge", ">=", True)):
        add("first-field-" + name, f"ROW(2,0) {operator} ROW(1,9)", result, sqlite=True)
    add("equal-null-fields", "(1,NULL) = (1,NULL)", None, sqlite=True)
    add("unequal-null-fields", "(1,NULL) <> (1,NULL)", None, sqlite=True)
    add("decisive-equality", "(1,NULL) = (2,NULL)", False, sqlite=True)
    add("decisive-inequality", "(1,NULL) != (2,NULL)", True, sqlite=True)
    add("decisive-less", "(1,NULL) < (2,NULL)", True, sqlite=True)
    add("decisive-greater", "(1,NULL) > (2,NULL)", False, sqlite=True)
    add("null-first", "(NULL,1) < (NULL,2)", None, sqlite=True)
    add("null-second", "(1,NULL) <= (1,2)", None, sqlite=True)
    add("single-field", "ROW(1) = ROW(1)", True)
    add("single-null", "ROW(NULL) <> ROW(1)", None)
    add("unknown-text", "('b',2) > ('a',9)", True, sqlite=True)
    add("contextual-unknown", "('1',NULL) = (1,NULL::INTEGER)", None)
    add("cross-int-bigint", "(1,2::BIGINT) <= (1::BIGINT,3)", True)
    add("cross-smallint", "(1::SMALLINT,3) > (1::BIGINT,2::SMALLINT)", True)
    add("numeric-unknown", "(1.25,'2.5') = (1.25::NUMERIC,2.5)", True)
    add("cross-float", "(1::REAL,2::DOUBLE PRECISION) = (1::DOUBLE PRECISION,2::REAL)", True)
    add("date-timestamp", "(DATE '2024-01-01',1) < (TIMESTAMP '2024-01-02',0)", True)
    add("time-zone", "(TIME WITH TIME ZONE '12:00+00',1) = (TIME WITH TIME ZONE '12:00+00',1)", True)
    add("numeric-modifier", "(1.234::NUMERIC(6,2),2) = (1.23,2)", True)
    add("varchar-modifier", "('abcd'::VARCHAR(2),1) = ('ab'::TEXT,1)", True)
    add("character-padding", "('a'::CHAR(3),1) = ('a'::CHAR(1),1)", True)
    add("boolean-order", "(FALSE,2) < (TRUE,1)", True, sqlite=True)
    add("uuid-order", "('00000000-0000-0000-0000-000000000001'::UUID,1) < "
        "('00000000-0000-0000-0000-000000000002'::UUID,0)", True)
    add("jsonb-equality", """('{"a":1,"b":2}'::JSONB,1) = ('{"b":2,"a":1}'::JSONB,1)""", True)
    add("bytea-order", r"('\x6162'::BYTEA,1) < ('\x6163'::BYTEA,0)", True)
    add("array-null-members", "(ARRAY[1,NULL],1) = (ARRAY[1,NULL],1)", True)
    add("array-order", "(ARRAY[1,2],9) < (ARRAY[1,3],0)", True)
    add("date-array", "(ARRAY[DATE '2024-01-01'],2) >= (ARRAY[DATE '2024-01-01'],1)", True)
    add("anonymous-order", "ROW(?,?) < ROW(?,?)", True,
        types="int,int,int,int", values=[1,2,1,3], sqlite=True)
    add("reordered-repeat", "($2,$1,$2) > ($1,$2,$1)", True,
        types="int,int", values=[1,2], sqlite=True)
    add("nullable-binding", "($1,2) = (1,$2)", None,
        types="int?,int", values=[None,2], sqlite=True)
    add("wide-binding", "($1,1) > (2147483647,$2)", True,
        types="bigint,int", values=[2147483648,2])
    add("parameter-modifier-erasure", "($1,0) <> (1.23,0)", True,
        types="numeric(6,2)", values=["1.234"])
    add("conditional-fields", "(CASE WHEN TRUE THEN 1 ELSE 2 END,COALESCE(NULL,2)) = (1,2)",
        True, sqlite=True)
    add("function-fields", "(ABS(-2),LENGTH('abc')) = (2,3)", True)
    add("subscript-fields", "((ARRAY[1,2])[1],(ARRAY[3,4])[2]) < (2,0)", True)
    add("predicate", "($1,2) <= (1,2)", True, types="int", values=[1], sqlite=True,
        predicate=" WHERE (1,2) < (2,1)")
    add("four-fields", "(1,'a',TRUE,4) = (1,'a',TRUE,4)", True, sqlite=True)
    excluded = {
        "single-field", "single-null", "date-timestamp", "time-zone",
        "uuid-order", "jsonb-equality", "bytea-order", "array-null-members",
        "array-order", "date-array", "function-fields", "subscript-fields",
    }
    for row in rows:
        row["sqlite_supported"] = row["shape"] not in excluded
        # The CLI's SQLite mode reads tuple spelling. Replacing a one-field
        # ROW would change it into a scalar, so retain that rejection input.
        row["sqlite_input"] = row["sql"].replace("$", "?")
        if row["shape"] not in {"single-field", "single-null"}:
            row["sqlite_input"] = row["sqlite_input"].replace("ROW(", "(")
        # SQLite has no PostgreSQL contextual-string coercion or enforcement
        # of NUMERIC/VARCHAR modifiers. These are separate native oracles.
        if row["shape"] in {"contextual-unknown", "numeric-unknown", "numeric-modifier", "varchar-modifier"}:
            row["sqlite_value"] = 0
    assert len(rows) == len({row["sql"] for row in rows}) == 50
    return rows


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--check", action="store_true")
    args = parser.parse_args()
    content = json.dumps(cases(), indent=2) + "\n"
    if args.check:
        assert DESTINATION.read_text() == content, "stale row comparison fixtures"
    else:
        DESTINATION.parent.mkdir(parents=True, exist_ok=True)
        DESTINATION.write_text(content)
    print("PASS: 50 distinct row comparison examples with exact BOOL and value metadata")


if __name__ == "__main__":
    main()
