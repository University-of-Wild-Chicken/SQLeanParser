#!/usr/bin/env python3
"""Author 50 SUBSTRING cases with positional, regex and binding expectations."""
import argparse
import json
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
DESTINATION = ROOT / "fixtures/substring/synthetic.json"


def cases():
    rows = []

    def add(shape, expression, value, nullable=False, type_="text", types="", values=()):
        sql = f"SELECT {expression} AS v;"
        rows.append({
            "id": f"substring-{len(rows)+1:02}-{shape}", "source_kind": "synthetic",
            "shape": shape, "sql": sql, "parameter_types": types,
            "parameter_values": list(values),
            "output_columns": [{"name": "v", "type": type_, "nullable": nullable}],
            "postgres_type": type_, "postgres_display_type": type_,
            "expected_value": value, "sqlite_input": sql.replace("$", "?"),
            "sqlite_supported": False,
        })

    for shape, arguments, value in [
        ("from", "'abcdef' FROM 2", "bcdef"),
        ("from-zero", "'abcdef' FROM 0", "abcdef"),
        ("from-negative", "'abcdef' FROM -2", "abcdef"),
        ("from-beyond-end", "'abcdef' FROM 20", ""),
        ("from-end", "'abcdef' FROM 7", ""),
        ("unicode-characters", "'Aé🙂界Z' FROM 2 FOR 3", "é🙂界"),
        ("from-for", "'abcdef' FROM 2 FOR 3", "bcd"),
        ("from-zero-for", "'abcdef' FROM 0 FOR 3", "ab"),
        ("from-negative-for", "'abcdef' FROM -1 FOR 3", "a"),
        ("before-start", "'abcdef' FROM -5 FOR 3", ""),
        ("length-beyond-end", "'abcdef' FROM 6 FOR 20", "f"),
        ("zero-length", "'abcdef' FROM 2 FOR 0", ""),
        ("for-only", "'abcdef' FOR 3", "abc"),
        ("for-zero", "'abcdef' FOR 0", ""),
        ("for-boolean-true", "'abcdef' FOR TRUE", "a"),
        ("for-boolean-false", "'abcdef' FOR FALSE", ""),
        ("for-rounded-numeric", "'abcdef' FOR 2.6", "abc"),
        ("for-known-text", "'abcdef' FOR '2'::TEXT", "ab"),
        ("for-from", "'abcdef' FOR 3 FROM 2", "bcd"),
        ("similar-positional", "'abcdef' SIMILAR 2 ESCAPE 3", "bcd"),
    ]:
        add(shape, f"SUBSTRING({arguments})", value)
    for shape, arguments, value, nullable in [
        ("bytea-from", "'abcdef'::BYTEA FROM 2", "\\x6263646566", False),
        ("bytea-from-for", "'abcdef'::BYTEA FROM 2 FOR 3", "\\x626364", False),
        ("bytea-for", "'abcdef'::BYTEA FOR 2", "\\x6162", False),
        ("bytea-for-from", "'abcdef'::BYTEA FOR 3 FROM 2", "\\x626364", False),
        ("bytea-similar-positional", "'abcdef'::BYTEA SIMILAR 2 ESCAPE 3", "\\x626364", False),
        ("bytea-zero-byte", "'\\x000102ff'::BYTEA FROM 2 FOR 2", "\\x0102", False),
        ("bytea-empty", "'abcdef'::BYTEA FOR 0", "\\x", False),
        ("bytea-before-start", "'abcdef'::BYTEA FROM 0 FOR 2", "\\x61", False),
        ("bytea-null", "NULL::BYTEA FROM 2", None, True),
        ("for-json-number", "'abcdef'::BYTEA FOR '2'::JSONB", "\\x6162", True),
    ]:
        add(shape, f"SUBSTRING({arguments})", value, nullable, "bytea")
    for shape, arguments, value in [
        ("regex-capture", "'abc123def' FROM '([0-9]+)'", "123"),
        ("regex-first-capture", "'abcdef' FROM '(a)(b)'", "a"),
        ("regex-whole-match", "'abcdef' FROM 'bc.'", "bcd"),
        ("regex-no-match", "'abcdef' FROM 'xyz'", None),
        ("regex-null-pattern", "'abcdef' FROM NULL::TEXT", None),
        ("similar-capture", """'abcdef' SIMILAR '%#"bc#"%' ESCAPE '#'""", "bc"),
        ("similar-whole-match", "'abcdef' SIMILAR '%' ESCAPE '#'", "abcdef"),
        ("similar-no-match", "'abcdef' SIMILAR 'xyz' ESCAPE '#'", None),
        ("from-for-regex", """'abcdef' FROM '%#"bc#"%' FOR '#'""", "bc"),
        ("for-from-regex", """'abcdef' FOR '#' FROM '%#"bc#"%'""", "bc"),
    ]:
        add(shape, f"SUBSTRING({arguments})", value, True)
    add("anonymous", "SUBSTRING(? FROM ? FOR ?)", "bcd", types="text,int,int", values=["abcdef", 2, 3])
    add("anonymous-reversed", "SUBSTRING(? FOR ? FROM ?)", "bcd",
        types="text,int,int", values=["abcdef", 3, 2])
    add("numbered-reordered", "SUBSTRING($3 FOR $1 FROM $2)", "bcd",
        types="int,int,text", values=[3, 2, "abcdef"])
    add("numbered-repeated", "SUBSTRING($1 FROM $2 FOR $2)", "bc",
        types="text,int", values=["abcdef", 2])
    add("nullable-binding", "SUBSTRING($1 FROM $2)", None, True,
        types="text?,int", values=[None, 2])
    add("for-bound-text", "SUBSTRING($1 FOR $2)", "ab", types="text,text", values=["abcdef", "2"])
    add("ordinary-positional", "substring('abcdef', 2)", "bcdef")
    add("ordinary-regex", "substring('abcdef', 'bc.')", "bcd", True)
    add("coalesced-no-match", "COALESCE(SUBSTRING('abcdef' FROM 'xyz'), 'fallback')", "fallback")
    add("char-padding-conversion", "SUBSTRING(CAST('abc' AS CHAR(6)) FROM 2 FOR 5)", "bc")
    assert len(rows) == len({row["id"] for row in rows}) == len({row["sql"] for row in rows}) == 50
    return rows


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--check", action="store_true")
    args = parser.parse_args()
    content = json.dumps(cases(), indent=2, ensure_ascii=False) + "\n"
    if args.check:
        assert DESTINATION.read_text() == content, "stale SUBSTRING fixtures"
    else:
        DESTINATION.parent.mkdir(parents=True, exist_ok=True)
        DESTINATION.write_text(content)
    print("PASS: 50 authored SUBSTRING cases with positional, regex, NULL and binding expectations")


if __name__ == "__main__":
    main()
