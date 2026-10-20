#!/usr/bin/env python3
"""Author 50 EXTRACT cases with explicit temporal, numeric and NULL expectations."""
import argparse
import json
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
DESTINATION = ROOT / "fixtures/extract/synthetic.json"


def cases():
    rows = []

    def add(shape, expression, value, nullable, types="", values=()):
        sql = f"SELECT {expression} AS v;"
        rows.append({
            "id": f"extract-{len(rows)+1:02}-{shape}", "source_kind": "synthetic",
            "shape": shape, "sql": sql, "parameter_types": types,
            "parameter_values": list(values),
            "output_columns": [{"name": "v", "type": "numeric", "nullable": nullable}],
            "postgres_type": "numeric", "postgres_display_type": "numeric",
            "expected_value": value, "sqlite_input": sql.replace("$", "?"),
            "sqlite_supported": False,
        })

    for shape, field, declaration, value, expected, nullable in [
        ("date-year", "YEAR", "DATE", "2024-02-29", "2024", True),
        ("iso-year", "ISOYEAR", "DATE", "2021-01-01", "2020", True),
        ("iso-week", "WEEK", "DATE", "2021-01-01", "53", True),
        ("quarter", "QUARTER", "DATE", "2024-12-31", "4", True),
        ("sunday", "DOW", "DATE", "2024-01-07", "0", True),
        ("iso-sunday", "ISODOW", "DATE", "2024-01-07", "7", True),
        ("leap-year-day", "DOY", "DATE", "2024-12-31", "366", True),
        ("leap-day", "DAY", "DATE", "2024-02-29", "29", True),
        ("month", "MONTH", "DATE", "2024-02-29", "2", True),
        ("century", "CENTURY", "DATE", "2001-01-01", "21", True),
        ("millennium", "MILLENNIUM", "DATE", "2001-01-01", "3", True),
        ("bc-year", "YEAR", "DATE", "0001-01-01 BC", "-1", True),
        ("hour-24", "HOUR", "TIME", "24:00:00", "24", False),
        ("minute", "MINUTE", "TIME", "12:34:56.789", "34", False),
        ("fractional-second", "SECOND", "TIME", "12:34:56.789", "56.789000", False),
        ("milliseconds", "MILLISECONDS", "TIME", "12:34:56.789", "56789.000", False),
        ("microseconds", "MICROSECONDS", "TIME", "12:34:56.789", "56789000", False),
        ("time-epoch", "EPOCH", "TIME", "01:02:03.5", "3723.500000", False),
        ("zone-seconds", "TIMEZONE", "TIME WITH TIME ZONE", "12:00:00+05:30", "19800", False),
        ("zone-hour", "TIMEZONE_HOUR", "TIME WITH TIME ZONE", "12:00:00-03:30", "-3", False),
        ("zone-minute", "TIMEZONE_MINUTE", "TIME WITH TIME ZONE", "12:00:00-03:30", "-30", False),
        ("zoned-time-epoch", "EPOCH", "TIME WITH TIME ZONE", "01:02:03+02", "-3477.000000", False),
        ("timestamp-year", "YEAR", "TIMESTAMP", "2025-01-02 12:34:56.789", "2025", True),
        ("unix-origin", "EPOCH", "TIMESTAMP WITH TIME ZONE", "1970-01-01 00:00:00+00", "0.000000", True),
        ("julian-date", "JULIAN", "DATE", "2000-01-01", "2451545", True),
        ("interval-year", "YEAR", "INTERVAL", "2 years 3 months", "2", False),
        ("interval-month", "MONTH", "INTERVAL", "2 years 3 months", "3", False),
        ("interval-quarter", "QUARTER", "INTERVAL", "7 months", "3", False),
        ("interval-day", "DAY", "INTERVAL", "2 days 3 hours", "2", False),
        ("interval-hours", "HOUR", "INTERVAL", "2 days 27 hours", "27", False),
        ("negative-minute", "MINUTE", "INTERVAL", "-1 day -02:03:04.5", "-3", False),
        ("negative-second", "SECOND", "INTERVAL", "-1 day -02:03:04.5", "-4.500000", False),
        ("interval-epoch", "EPOCH", "INTERVAL", "1 day 2 hours", "93600.000000", False),
        ("infinite-year", "YEAR", "DATE", "infinity", "Infinity", True),
        ("infinite-day", "DAY", "DATE", "infinity", None, True),
        ("negative-infinite-second", "SECOND", "TIMESTAMP", "-infinity", None, True),
        ("infinite-epoch", "EPOCH", "TIMESTAMP WITH TIME ZONE", "infinity", "Infinity", True),
    ]:
        add(shape, f"EXTRACT({field} FROM CAST('{value}' AS {declaration}))", expected, nullable)
    add("null-date", "EXTRACT(YEAR FROM NULL::DATE)", None, True)
    add("null-time", "EXTRACT(HOUR FROM NULL::TIME)", None, True)
    add("null-interval", "EXTRACT(SECOND FROM NULL::INTERVAL)", None, True)
    add("anonymous", "EXTRACT(YEAR FROM CAST(? AS DATE))", "2024", True, "date", ["2024-02-29"])
    add("reordered", "EXTRACT(YEAR FROM $2) + EXTRACT(MONTH FROM $1)", "2027", True,
        "date,date", ["2024-02-29", "2025-01-02"])
    add("repeated", "EXTRACT(HOUR FROM $1) + EXTRACT(MINUTE FROM $1)", "46", False,
        "time", ["12:34:56"])
    add("nullable-binding", "EXTRACT(HOUR FROM $1)", None, True, "time?", [None])
    add("explicit-time-rounding", "EXTRACT(SECOND FROM CAST($1 AS TIME(0)))", "57.000000",
        False, "time", ["12:34:56.789"])
    add("bound-text-cast", "EXTRACT(YEAR FROM CAST($1 AS DATE))", "2024",
        True, "text", ["2024-02-29"])
    add("case-interval", "EXTRACT(SECOND FROM CASE WHEN TRUE THEN INTERVAL '1.25 seconds' "
        "ELSE NULL::INTERVAL END)", "1.250000", True)
    add("coalesced-result", "COALESCE(EXTRACT(HOUR FROM NULL::TIME),"
        "EXTRACT(HOUR FROM TIME '12:34:56'))", "12", False)
    add("string-field", "EXTRACT('YeAr' FROM DATE '2024-02-29')", "2024", True)
    add("quoted-field", 'EXTRACT("day" FROM DATE \'2024-02-29\')', "29", True)
    assert len(rows) == len({row["id"] for row in rows}) == len({row["sql"] for row in rows}) == 50
    return rows


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--check", action="store_true")
    args = parser.parse_args()
    content = json.dumps(cases(), indent=2) + "\n"
    if args.check:
        assert DESTINATION.read_text() == content, "stale EXTRACT fixtures"
    else:
        DESTINATION.parent.mkdir(parents=True, exist_ok=True)
        DESTINATION.write_text(content)
    print("PASS: 50 authored EXTRACT cases with numeric and SQL NULL expectations")


if __name__ == "__main__":
    main()
