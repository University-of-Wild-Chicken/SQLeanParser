#!/usr/bin/env python3
"""Author two fifty-query populations with independent Boolean expectations."""
import argparse
import json
from pathlib import Path

from check_advanced_cli import question_parameters

ROOT = Path(__file__).resolve().parents[1]


def distinct_cases():
    # Subject pairs and expected DISTINCT result; NOT DISTINCT inverts it.
    forms = [
        ("equal-integers", "1", "1", False, "", [], True),
        ("unequal-integers", "1", "2", True, "", [], True),
        ("raw-null-left", "NULL", "1", True, "", [], True),
        ("raw-null-right", "1", "NULL", True, "", [], True),
        ("both-raw-null", "NULL", "NULL", False, "", [], True),
        ("nullable-parameter", "$1", "$2", True, "integer?,integer", [None, 3], True),
        ("reversed-parameters", "$2", "$1", True, "integer?,integer", [None, 7], True),
        ("anonymous-parameters", "?", "?", False, "integer?,integer?", [None, None], True),
        ("unknown-strings", "'a'", "'a'", False, "", [], True),
        ("unknown-integer", "'2'", "2", False, "", [], True),
        ("typed-null", "CAST(NULL AS TEXT)", "NULL", False, "", [], True),
        ("json-raw-null", "'{}'::JSON", "NULL", True, "", [], False),
        ("json-array-raw-null", "ARRAY['{}'::JSON]", "NULL", True, "", [], False),
        ("numeric-widths", "1::SMALLINT", "1::BIGINT", False, "", [], True),
        ("float-nan", "'NaN'::DOUBLE PRECISION", "'NaN'::DOUBLE PRECISION", False, "", [], True),
        ("name-text", "'alpha'::NAME", "'alpha'::TEXT", False, "", [], False),
        ("char-padding", "'abc '::CHAR(4)", "'abc'::TEXT", False, "", [], True),
        ("date-timestamp", "DATE '2024-01-01'", "TIMESTAMP '2024-01-01 00:00:00'", False, "", [], False),
        ("jsonb-key-order", "'{\"a\":1,\"b\":2}'::JSONB", "'{\"b\":2,\"a\":1}'::JSONB", False, "", [], False),
        ("array-equality", "ARRAY[1,NULL,3]", "ARRAY[1,NULL,3]", False, "", [], False),
        ("row-null-equality", "ROW(1,NULL)", "ROW(1,NULL)", False, "", [], False),
        ("row-null-difference", "ROW(1,NULL)", "ROW(1,2)", True, "", [], False),
        ("empty-rows", "ROW()", "ROW()", False, "", [], False),
        ("row-vs-raw-null", "ROW(NULL,NULL)", "NULL", True, "", [], False),
        ("row-reversed-parameters", "ROW($2,$1)", "ROW($1,$2)", True, "integer,integer", [1, 2], False),
    ]
    result = []
    for negated in (False, True):
        for name, left, right, expected, types, values, sqlite in forms:
            op = "IS NOT DISTINCT FROM" if negated else "IS DISTINCT FROM"
            result.append(make_case("distinct-from", len(result)+1,
                                   ("not-" if negated else "")+name,
                                   f"{left} {op} {right}", expected != negated,
                                   types, values, sqlite))
            sqlite_pairs = {
                "numeric-widths": ("CAST(1 AS SMALLINT)", "CAST(1 AS BIGINT)"),
                "float-nan": ("CAST('NaN' AS DOUBLE PRECISION)", "CAST('NaN' AS DOUBLE PRECISION)"),
                "char-padding": ("CAST('abc ' AS CHAR(4))", "CAST('abc' AS TEXT)"),
            }
            if name in sqlite_pairs:
                a, b = sqlite_pairs[name]
                result[-1]["sqlite_sql"] = f"SELECT {a} {op} {b} AS v;"
            if name in {"unknown-integer", "char-padding"}:
                # SQLite compares storage classes; PostgreSQL contextually coerces
                # the unknown string to INTEGER. SQLite CHAR casts retain padding.
                # Preserve each dialect's independently specified result.
                result[-1]["sqlite_expected_value"] = int(not negated)
    return result


def null_cases():
    # The last two truth values are ISNULL and NOTNULL, not logical inverses
    # for rows with mixed fields or empty rows.
    forms = [
        ("raw-null", "NULL", True, False, "", [], True),
        ("integer", "1", False, True, "", [], True),
        ("empty-text", "''", False, True, "", [], True),
        ("null-spelling-text", "'null'", False, True, "", [], True),
        ("boolean-false", "FALSE", False, True, "", [], True),
        ("nullable-parameter", "$1", True, False, "integer?", [None], True),
        ("nullable-nonnull-parameter", "$1 + 0", False, True, "integer?", [7], True),
        ("anonymous-parameter", "?", True, False, "text?", [None], True),
        ("reversed-parameters", "COALESCE($2,$1)", True, False, "text?,text?", [None, None], True),
        ("json-typed-null", "CAST(NULL AS JSON)", True, False, "", [], False),
        ("json-value", "'{}'::JSON", False, True, "", [], False),
        ("jsonb-typed-null", "CAST(NULL AS JSONB)", True, False, "", [], False),
        ("array-null-elements", "ARRAY[NULL,NULL]", False, True, "", [], False),
        ("array-typed-null", "CAST(NULL AS INTEGER[])", True, False, "", [], False),
        ("empty-row", "ROW()", True, True, "", [], False),
        ("all-null-row", "ROW(NULL,NULL)", True, False, "", [], False),
        ("mixed-row", "ROW(1,NULL)", False, False, "", [], False),
        ("nonnull-row", "ROW(1,'x')", False, True, "", [], False),
        ("json-null-row", "ROW(NULL::JSON,NULL::JSON)", True, False, "", [], False),
        ("array-mixed-row", "ROW(ARRAY[NULL]::INTEGER[],NULL)", False, False, "", [], False),
        ("row-reversed-parameters", "ROW($2,$1)", False, False, "integer?,integer", [None, 4], False),
        ("comparison-precedence", "1 = NULL", True, False, "", [], True),
        ("postfix-chain", "TRUE ISNULL", False, True, "", [], True),
        ("null-arithmetic", "1 + NULL", True, False, "", [], True),
        ("case-null", "CASE WHEN TRUE THEN NULL ELSE TRUE END", True, False, "", [], True),
    ]
    result = []
    for negated in (False, True):
        for name, expression, isnull, notnull, types, values, sqlite in forms:
            result.append(make_case("null-predicates", len(result)+1,
                                   ("notnull-" if negated else "isnull-")+name,
                                   f"{expression} {'NOTNULL' if negated else 'ISNULL'}",
                                   notnull if negated else isnull, types, values, sqlite))
    return result


def make_case(factor, index, shape, expression, expected, types, values, sqlite):
    sql = f"SELECT {expression} AS v;"
    return {
        "id": f"{factor}-{index:02}-{shape}", "source_kind": "synthetic", "shape": shape,
        "sql": sql, "postgres_input": question_parameters(sql),
        "parameter_types": types, "parameter_values": values,
        "output_columns": [{"name": "v", "type": "bool", "nullable": False}],
        "postgres_type": "boolean", "postgres_display_type": "boolean",
        "expected_value": "true" if expected else "false", "expected_sql_null": False,
        "sqlite_supported": sqlite, "sqlite_input": sql.replace("$", "?"),
        "sqlite_sql": sql.replace("$", "?") if sqlite else None,
        "sqlite_expected_value": int(expected) if sqlite else None,
    }


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--check", action="store_true")
    args = parser.parse_args()
    for factor, rows in (("distinct_from", distinct_cases()), ("null_predicates", null_cases())):
        assert len(rows) == len({r['id'] for r in rows}) == len({r['sql'] for r in rows}) == 50
        path = ROOT / "fixtures" / factor / "synthetic.json"
        content = json.dumps(rows, ensure_ascii=False, indent=2) + "\n"
        if args.check:
            assert path.read_text() == content, f"stale {path}"
        else:
            path.parent.mkdir(parents=True, exist_ok=True)
            path.write_text(content)
    print("PASS: 50 DISTINCT FROM and 50 null-predicate authored queries")


if __name__ == "__main__":
    main()
