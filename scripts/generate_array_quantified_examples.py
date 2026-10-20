#!/usr/bin/env python3
"""Generate quantified-array examples with authored native results and signatures."""
import argparse
import json
from itertools import product
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
DESTINATION = ROOT / "fixtures/array_quantified"
OPERATORS = ("=", "<>", "<", "<=", ">", ">=")


def operator_signatures():
    """Declared catalog expectations, independently checked against PostgreSQL."""
    pairs = []
    for group in (
            ("smallint", "integer", "bigint"),
            ("real", "double precision"),
            ("date", "timestamp", "timestamp with time zone")):
        pairs.extend(product(group, repeat=2))
    pairs.extend((type_, type_) for type_ in (
        "numeric", "text", "char", "boolean", "time", "time with time zone",
        "interval", "uuid", "jsonb", "bytea"))
    assert len(pairs) == len(set(pairs)) == 32
    result = [{"operator": operator, "left": left, "right": right}
              for operator in OPERATORS for left, right in pairs]
    assert len(result) == 192
    return result


def cases():
    result = []

    def add(shape, expr, value, types="", values=()):
        sql = f"SELECT {expr} AS v;"
        result.append({
            "id": f"array-quantified-{len(result) + 1:02}-{shape}",
            "source_kind": "synthetic", "shape": shape, "sql": sql,
            "sqlite_sql": sql.replace("$", "?"),
            "parameter_types": types, "parameter_values": list(values),
            "output_columns": [{"name": "v", "type": "bool", "nullable": True}],
            "postgres_type": "boolean", "postgres_display_type": "boolean",
            "expected_value": value,
        })

    # Six operators by three source quantifiers: SOME is retained as source
    # syntax even though PostgreSQL treats it as an alias of ANY.
    grid = [
        ("equal", "=", (("4", "[1,4,7]", True), ("2", "[1,4,7]", False), ("4", "[4,4]", True))),
        ("not-equal", "<>", (("4", "[4,4]", False), ("4", "[1,4]", True), ("4", "[1,7]", True))),
        ("less", "<", (("4", "[1,7]", True), ("8", "[1,7]", False), ("0", "[1,7]", True))),
        ("less-equal", "<=", (("4", "[1,4]", True), ("8", "[1,7]", False), ("4", "[4,7]", True))),
        ("greater", ">", (("4", "[1,7]", True), ("0", "[1,7]", False), ("8", "[1,7]", True))),
        ("greater-equal", ">=", (("4", "[4,7]", True), ("0", "[1,7]", False), ("7", "[1,7]", True))),
    ]
    for shape, operator, examples in grid:
        for quantifier, (left, right, expected) in zip(("ANY", "SOME", "ALL"), examples):
            add(f"{shape}-{quantifier.lower()}", f"{left} {operator} {quantifier}(ARRAY{right})",
                "true" if expected else "false")
    add("not-equal-alias", "4 != ANY(ARRAY[4,5])", "true")
    add("empty-any-null-left", "NULL::INTEGER = ANY(ARRAY[]::INTEGER[])", "false")
    add("empty-all-null-left", "NULL::INTEGER > ALL('{}'::INTEGER[])", "true")
    add("empty-some", "9 = SOME('{}'::INTEGER[])", "false")
    add("null-array", "1 = ANY(NULL::INTEGER[])", None)
    add("null-scalar", "NULL::INTEGER = ALL(ARRAY[1,2])", None)
    add("null-element-any", "9 = ANY(ARRAY[1,NULL])", None)
    add("true-over-null", "1 = ANY(ARRAY[NULL,1])", "true")
    add("false-over-null", "2 = ALL(ARRAY[NULL,1])", "false")
    add("null-element-all", "1 = ALL(ARRAY[NULL,1])", None)
    add("multidimensional-any", "3 = ANY(ARRAY[[1,2],[3,4]])", "true")
    add("multidimensional-all", "0 < ALL(ARRAY[[1,2],[3,4]])", "true")
    add("numeric-integer", "1.5 < ANY(ARRAY[1,2])", "true")
    add("real-bigint", "2::REAL = SOME(ARRAY[1,2]::BIGINT[])", "true")
    add("numeric-modifiers", "1.23::NUMERIC(6,2) = ANY(ARRAY[1.234::NUMERIC(7,3),1.23::NUMERIC(6,2)])", "true")
    add("date", "DATE '2024-01-01' < ALL(ARRAY[DATE '2024-01-02',DATE '2024-02-01'])", "true")
    add("date-timestamp", "DATE '2024-01-01' = ANY(ARRAY[TIMESTAMP '2024-01-01 00:00:00',TIMESTAMP '2024-02-01 00:00:00'])", "true")
    add("time-null-element", "TIME '12:00' > SOME(ARRAY[TIME '11:00',NULL])", "true")
    add("interval", "INTERVAL '2 hours' >= ALL(ARRAY[INTERVAL '60 minutes',INTERVAL '2 hours'])", "true")
    add("text-order", "'b'::TEXT > ALL(ARRAY['a','aa'])", "true")
    add("uuid", "'00000000-0000-0000-0000-000000000002'::UUID = ANY(ARRAY['00000000-0000-0000-0000-000000000001','00000000-0000-0000-0000-000000000002']::UUID[])", "true")
    add("bytea", r"'\x00'::BYTEA <> ALL(ARRAY['\x01','\x02']::BYTEA[])", "true")
    add("unknown-array-literal", "2 = ANY('{1,2,3}')", "true")
    add("unknown-empty-array", "NULL::INTEGER = ALL('{}')", "true")
    add("unknown-null-array", "2 = SOME(NULL)", None)
    add("unknown-null-scalar", "NULL = ANY(ARRAY[1,2])", None)
    add("both-unknown-text", "'b' = ANY('{a,b}')", "true")
    add("anonymous-order", "? = ANY(ARRAY[?,?])", "true", "int,int,int", [5,1,5])
    add("numbered-reorder-repeat", "$2 = SOME(ARRAY[$1,$2,$1])", "true", "int,int", [4,7])
    add("nullable-array-binding", "$1 <> ALL($2)", None, "int?,int[]?", [1,None])
    add("numeric-array-binding", "$1 < ANY($2)", "true", "bigint,numeric[]", [3,"{2.5,4.5}"])
    add("multiple-quantifiers-bindings", "($2 = ANY($1)) AND ($2 < ALL($3))", "true",
        "int[],int,int[]", ["{1,4}",4,"{5,6}"])
    assert len(result) == len({case["sql"] for case in result}) == 50
    return result


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--check", action="store_true")
    args = parser.parse_args()
    for name, rows in (("synthetic.json", cases()), ("operator_signatures.json", operator_signatures())):
        content = json.dumps(rows, indent=2) + "\n"
        path = DESTINATION / name
        if args.check:
            assert path.read_text() == content, f"stale quantified-array fixture: {name}"
        else:
            DESTINATION.mkdir(parents=True, exist_ok=True)
            path.write_text(content)
    print("PASS: 50 distinct quantified-array examples and 192 declared scalar operator signatures")


if __name__ == "__main__":
    main()
