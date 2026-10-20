#!/usr/bin/env python3
"""Author 50 interval qualifier cases with exact metadata and native values."""
import argparse
import json
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
DESTINATION = ROOT / "fixtures/interval_fields/synthetic.json"
FIELDS = {
    "year": 4, "month": 2, "day": 8, "hour": 1024, "minute": 2048, "second": 4096,
    "year to month": 6, "day to hour": 1032, "day to minute": 3080,
    "day to second": 7176, "hour to minute": 3072, "hour to second": 7168,
    "minute to second": 6144,
}


def cases():
    rows = []

    def add(shape, expr, type_, value, nullable=False, types="", values=()):
        sql = f"SELECT {expr} AS v;"
        oid = ("interval[]" if type_.endswith("[]") else "interval") if type_.startswith(
            "interval") else {"bool": "boolean", "timestamp": "timestamp without time zone"}.get(type_, type_)
        display = {"bool": "boolean", "timestamp": "timestamp without time zone"}.get(type_, type_)
        rows.append({
            "id": f"interval-fields-{len(rows)+1:02}-{shape}", "source_kind": "synthetic",
            "shape": shape, "sql": sql, "parameter_types": types, "parameter_values": list(values),
            "output_columns": [{"name": "v", "type": type_, "nullable": nullable}],
            "postgres_type": oid, "postgres_display_type": display, "expected_value": value,
            "sqlite_input": sql.replace("$", "?"), "sqlite_supported": False,
        })

    value = "1 year 2 mons 3 days 04:05:06.789"
    truncations = {
        "year": "1 year", "month": "1 year 2 mons", "day": "1 year 2 mons 3 days",
        "hour": "1 year 2 mons 3 days 04:00:00",
        "minute": "1 year 2 mons 3 days 04:05:00", "second": value,
    }
    for fields in FIELDS:
        add("literal-" + fields.replace(" ", "-"), f"INTERVAL '{value}' {fields.upper()}",
            "interval " + fields, truncations[fields.split()[-1]])
    for fields in ("second", "day to second", "hour to second", "minute to second"):
        for precision in (0, 6):
            declaration = f"interval {fields}({precision})"
            add(fields.replace(" ", "-") + f"-precision-{precision}",
                f"CAST('-1.234567 seconds' AS {declaration})", declaration,
                "-00:00:01" if precision == 0 else "-00:00:01.234567")
    for fields, literal, expected in [
        ("year", "2", "2 years"), ("month", "14", "1 year 2 mons"),
        ("day", "90", "90 days"), ("hour", "27", "27:00:00"),
        ("minute", "90", "01:30:00"), ("second(2)", "1.235", "00:00:01.24"),
        ("year to month", "2-3", "2 years 3 mons"), ("day to hour", "2 3", "2 days 03:00:00"),
    ]:
        add("numeric-" + fields.replace(" ", "-"), f"INTERVAL '{literal}' {fields.upper()}",
            "interval " + fields, expected)
    add("unknown-input", "'1'::INTERVAL YEAR", "interval year", "1 year")
    add("known-text-input", "'1'::TEXT::INTERVAL YEAR", "interval year", "00:00:00")
    add("known-interval-input", "(INTERVAL '1')::INTERVAL YEAR", "interval year", "00:00:00")
    add("array-element-input", "'{1,2}'::INTERVAL YEAR[]", "interval year[]", "{00:00:00,00:00:00}")
    add("array-equal-modifiers", "ARRAY[INTERVAL '1' YEAR, INTERVAL '2' YEAR]",
        "interval year[]", '{"1 year","2 years"}')
    add("array-different-modifiers", "ARRAY[INTERVAL '1' YEAR, INTERVAL '2' MONTH]",
        "interval[]", '{"1 year","2 mons"}')
    add("array-cast", """'{"1 year 2 mons","2 years 3 mons"}'::INTERVAL YEAR[]""",
        "interval year[]", '{"1 year","2 years"}')
    add("array-index", "(ARRAY[INTERVAL '1' YEAR, INTERVAL '2' YEAR])[2]",
        "interval year", "2 years", True)
    add("array-slice", "(ARRAY[INTERVAL '1' YEAR, INTERVAL '2' YEAR])[1:1]",
        "interval year[]", '{"1 year"}', True)
    add("coalesce-equal-modifiers", "COALESCE(NULL::INTERVAL DAY TO SECOND(2), "
        "INTERVAL '1 day 01:02:03.456' DAY TO SECOND(2))",
        "interval day to second(2)", "1 day 01:02:03.46")
    add("coalesce-different-modifiers", "COALESCE(INTERVAL '2' YEAR, INTERVAL '3' MONTH)",
        "interval", "2 years")
    add("nullif-left-modifiers", "NULLIF(INTERVAL '2' HOUR, INTERVAL '3' MINUTE)",
        "interval hour", "02:00:00", True)
    add("null-binding", "CAST($1 AS INTERVAL YEAR)", "interval year", None, True, "text?", [None])
    add("reordered", "CAST($2 AS INTERVAL YEAR) > CAST($1 AS INTERVAL MONTH)",
        "bool", "true", False, "text,text", ["2 months", "1 year"])
    add("repeated", "CAST($1 AS INTERVAL SECOND(2)) + CAST($1 AS INTERVAL SECOND(2))",
        "interval", "00:00:02.48", False, "text", ["1.235"])
    add("anonymous-known-text", "CAST(? AS INTERVAL DAY)", "interval day", "00:00:00",
        False, "text", ["90"])
    add("parameter-drops-modifiers", "COALESCE($1, NULL::INTERVAL YEAR)", "interval", "00:00:01",
        False, "interval year", ["1"])
    add("parameter-explicit-cast", "$1::INTERVAL YEAR", "interval year", "1 year",
        False, "interval year", ["1 year 2 mons"])
    add("extract", "EXTRACT(MONTH FROM INTERVAL '1 year 2 mons' MONTH)", "numeric", "2")
    add("comparison", "INTERVAL '2' HOUR > INTERVAL '3' MINUTE", "bool", "true")
    add("date-arithmetic", "DATE '2024-01-31' + INTERVAL '1' MONTH",
        "timestamp", "2024-02-29 00:00:00")
    assert len(rows) == len({row["id"] for row in rows}) == len({row["sql"] for row in rows}) == 50
    return rows


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--check", action="store_true")
    args = parser.parse_args()
    content = json.dumps(cases(), indent=2) + "\n"
    if args.check:
        assert DESTINATION.read_text() == content, "stale interval qualifier fixtures"
    else:
        DESTINATION.parent.mkdir(parents=True, exist_ok=True)
        DESTINATION.write_text(content)
    print("PASS: 50 authored interval qualifier cases with exact typmods and values")


if __name__ == "__main__":
    main()
