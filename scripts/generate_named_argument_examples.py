#!/usr/bin/env python3
"""Author named/default argument witnesses independently of the SQL renderer."""
import argparse
import json
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
DIRECTORY = ROOT / "fixtures/named_arguments"
SIGNATURES = [{
    "name": "make_interval",
    "names": ["years", "months", "weeks", "days", "hours", "mins", "secs"],
    "inputs": ["integer"] * 6 + ["double precision"],
    "defaults": ["0"] * 6 + ["0.0"],
    "output": "interval",
}]


def cases():
    rows = []

    def add(shape, expression, value, nullable=False, types="", values=(),
            type_="interval", native=None, display=None):
        postgres = {"bool": "boolean"}.get(type_, type_)
        if type_.startswith("interval"):
            postgres = "interval"
        rows.append({
            "id": f"named-arguments-{len(rows)+1:02}-{shape}",
            "source_kind": "synthetic", "shape": shape,
            "sql": f"SELECT {expression} AS v;",
            "postgres_input": f"SELECT {native or expression} AS v;",
            "parameter_types": types, "parameter_values": list(values),
            "output_columns": [{"name": "v", "type": type_, "nullable": nullable}],
            "postgres_type": postgres, "postgres_display_type": display or (
                "boolean" if type_ == "bool" else type_),
            "expected_value": value, "expected_sql_null": value is None,
            "sqlite_supported": False,
            "sqlite_input": f"SELECT {expression} AS v;".replace("$", "?"),
        })

    for shape, arguments, value in (
        ("all-defaults", "", "00:00:00"),
        ("positional-year", "1", "1 year"),
        ("positional-month", "1, 2", "1 year 2 mons"),
        ("positional-weeks", "0, 0, 2", "14 days"),
        ("positional-days", "0, 0, 0, 3", "3 days"),
        ("positional-hours", "0, 0, 0, 0, 4", "04:00:00"),
        ("positional-mins", "0, 0, 0, 0, 0, 5", "00:05:00"),
        ("positional-all", "1, 2, 1, 3, 4, 5, 6.25", "1 year 2 mons 10 days 04:05:06.25"),
    ):
        add(shape, f"make_interval({arguments})", value)
    names = SIGNATURES[0]["names"]
    for name, value in zip(names, ("2 years", "2 mons", "14 days", "2 days",
                                 "02:00:00", "00:02:00", "00:00:02")):
        add("arrow-" + name, f"make_interval({name} => 2)", value)
    for name, value in zip(names, ("1 year", "1 mon", "7 days", "1 day",
                                 "01:00:00", "00:01:00", "00:00:01")):
        add("colon-" + name, f"make_interval({name} := 1)", value)
    add("reverse-all", "make_interval(secs => 7, mins => 6, hours => 5, days => 4, "
        "weeks => 3, months => 2, years => 1)", "1 year 2 mons 25 days 05:06:07")
    add("mixed-prefix", "make_interval(2, months => 3, secs => 4)", "2 years 3 mons 00:00:04")
    add("mixed-notations", "make_interval(1, 2, days := 5, hours => 6)", "1 year 2 mons 5 days 06:00:00")
    add("qualified-function", "pg_catalog.make_interval(days => 4)", "4 days")
    add("quoted-function-and-name", '"make_interval"("days" => 5)', "5 days")
    add("folded-name", "make_interval(YEARS => 2)", "2 years")
    add("comment-separated-colon", "make_interval(mins/**/:=/**/8)", "00:08:00")
    add("adjacent-negative", "make_interval(secs=>-1.5)", "-00:00:01.5")
    add("unknown-slot-context", "make_interval(days => '6')", "6 days")
    add("smallint-integer-slot", "make_interval(days => 4::SMALLINT)", "4 days")
    add("bigint-seconds", "make_interval(secs => 7::BIGINT)", "00:00:07")
    add("numeric-seconds", "make_interval(secs => 1.125::NUMERIC(8,3))", "00:00:01.125")
    add("real-seconds", "make_interval(secs => 1.5::REAL)", "00:00:01.5")
    add("float8-seconds", "make_interval(secs => 2.5::DOUBLE PRECISION)", "00:00:02.5")
    add("numbered-reversed-slots", "make_interval(secs => $2, days => $1)",
        "3 days 00:00:04.5", types="integer,float8", values=[3, 4.5])
    add("anonymous-days-first", "make_interval(days => ?, secs => ?)", "2 days 00:00:03.25",
        types="integer,float8", values=[2, 3.25], native="make_interval(days => $1, secs => $2)")
    add("anonymous-seconds-first", "make_interval(secs => ?, days => ?)", "2 days 00:00:04.5",
        types="float8,integer", values=[4.5, 2], native="make_interval(secs => $1, days => $2)")
    add("reused-slot", "make_interval(years => $1, months => $1)", "2 years 2 mons",
        types="integer", values=[2])
    add("numbered-lexical-order", "make_interval(days => $2, secs => $1)", "2 days 00:00:01.5",
        types="float8,integer", values=[1.5, 2])
    add("unknown-null", "make_interval(days => NULL)", None, True)
    add("nullable-declaration", "make_interval(secs => $1)", None, True, "float8?", [None])
    add("coalesce-default", "COALESCE(make_interval(days => NULL), make_interval(hours => 1))", "01:00:00")
    add("case-result", "CASE WHEN TRUE THEN make_interval(days => 2) ELSE make_interval() END", "2 days")
    add("extract-result", "EXTRACT(DAY FROM make_interval(weeks => 2))", "14", type_="numeric")
    add("interval-modifier", "CAST(make_interval(secs => 1.234) AS INTERVAL DAY TO SECOND(2))",
        "00:00:01.23", type_="interval day to second(2)")
    add("array-equality", "ARRAY[make_interval(secs => 1), make_interval(days => 2)] = "
        "ARRAY[INTERVAL '1 second', INTERVAL '2 days']", "true", type_="bool")
    add("strict-null-suppresses-infinity", "make_interval(days => NULL, secs => 'Infinity'::FLOAT8)",
        None, True)
    add("month-year-equality", "make_interval(1, 0) = make_interval(months => 12)", "true", type_="bool")
    assert len(rows) == len({row["id"] for row in rows}) == len({row["sql"] for row in rows}) == 50
    return rows


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--check", action="store_true")
    args = parser.parse_args()
    for name, value in (("synthetic.json", cases()), ("function_signatures.json", SIGNATURES)):
        content = json.dumps(value, ensure_ascii=False, indent=2) + "\n"
        path = DIRECTORY / name
        if args.check:
            assert path.read_text() == content, f"stale {path}"
        else:
            DIRECTORY.mkdir(parents=True, exist_ok=True)
            path.write_text(content)
    print("PASS: 50 named/default argument queries and one exact seven-slot declaration")


if __name__ == "__main__":
    main()
