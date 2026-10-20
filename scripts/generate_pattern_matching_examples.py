#!/usr/bin/env python3
"""Author 50 ILIKE and 50 regex examples with independent PostgreSQL expectations."""
import argparse
import json
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]


def cases():
    populations = {}

    def population(factor):
        rows = []
        populations[factor] = rows

        def add(shape, expression, value, *, nullable=False, types="", values=(),
                type_="bool", suffix=""):
            sql = f"SELECT {expression} AS v{suffix};"
            rows.append({
                "id": f"{factor}-{len(rows)+1:02}-{shape}", "source_kind": "synthetic",
                "shape": shape, "sql": sql, "parameter_types": types,
                "parameter_values": list(values),
                "output_columns": [{"name": "v", "type": type_, "nullable": nullable}],
                "postgres_type": "boolean" if type_ == "bool" else type_,
                "postgres_display_type": "boolean" if type_ == "bool" else type_,
                "expected_value": value,
                "sqlite_input": sql.replace("$", "?"),
                "sqlite_supported": False,
            })
        return add

    add = population("ilike")
    add("case-fold", "'AbC' ILIKE 'abc'", "true")
    add("case-fold-miss", "'AbC' ILIKE 'abd'", "false")
    add("prefix", "'AbCd' ILIKE 'a%'", "true")
    add("suffix", "'AbCd' ILIKE '%D'", "true")
    add("substring", "'AbCd' ILIKE '%BC%'", "true")
    add("one-character", "'AbC' ILIKE '_B_'", "true")
    add("one-character-miss", "'AbCd' ILIKE '_B_'", "false")
    add("empty", "'' ILIKE ''", "true")
    add("empty-wildcard", "'' ILIKE '%'", "true")
    add("empty-single", "'' ILIKE '_'", "false")
    add("full-string", "'AbCd' ILIKE 'bc'", "false")
    add("not-match", "'AbC' NOT ILIKE 'a%'", "false")
    add("not-miss", "'AbC' NOT ILIKE 'z%'", "true")
    add("explicit-not", "NOT ('AbC' ILIKE 'a%')", "false")
    add("escaped-percent", r"'A%B' ILIKE 'a\%b'", "true")
    add("escaped-underscore", r"'A_B' ILIKE 'a\_b'", "true")
    add("escaped-backslash", r"'A\B' ILIKE 'a\\b'", "true")
    add("quote", "'O''Brien' ILIKE 'o''b%'", "true")
    add("subject-null", "NULL ILIKE 'a%'", None, nullable=True)
    add("pattern-null", "'abc' ILIKE NULL", None, nullable=True)
    add("both-null", "NULL ILIKE NULL", None, nullable=True)
    add("not-null", "NULL NOT ILIKE 'a%'", None, nullable=True)
    add("typed-null", "NULL::TEXT ILIKE 'a%'", None, nullable=True)
    add("varchar-subject", "'AbCd'::VARCHAR(3) ILIKE 'abc'", "true")
    add("varchar-pattern", "'AbC' ILIKE 'abcdef'::VARCHAR(3)", "true")
    add("char-subject-padding", "'AbC'::CHAR(5) ILIKE 'abc'", "false")
    add("char-subject-wildcard", "'AbC'::CHAR(5) ILIKE 'abc%'", "true")
    add("char-subject-spaces", "'AbC'::CHAR(5) ILIKE 'abc  '", "true")
    add("char-pattern-trim", "'AbC' ILIKE 'abc'::CHAR(5)", "true")
    add("char-both", "'AbC'::CHAR(5) ILIKE 'abc'::CHAR(5)", "false")
    add("explicit-char-text", "('AbC'::CHAR(5))::TEXT ILIKE 'abc'", "true")
    add("char-null", "NULL::CHAR(5) ILIKE 'abc'", None, nullable=True)
    add("pattern-concatenation", "'AbC' ILIKE 'a' || 'bc'", "true")
    add("subject-concatenation", "'A' || 'bC' ILIKE 'abc'", "true")
    add("coalesce-subject", "COALESCE(NULL,'AbC') ILIKE 'abc'", "true")
    add("case-pattern", "'AbC' ILIKE CASE WHEN TRUE THEN 'a%' ELSE 'z%' END", "true")
    add("coalesce-result", "COALESCE(NULL ILIKE 'a%',FALSE)", "false")
    add("boolean-and", "'AbC' ILIKE 'a%' AND TRUE", "true")
    add("boolean-or", "'AbC' ILIKE 'z%' OR TRUE", "true")
    add("anonymous", "? ILIKE ?", "true", types="text,text", values=["AbC", "abc"])
    add("reordered", "$2 ILIKE $1", "true", types="text,text", values=["a%", "AbC"])
    add("repeated", "$1 ILIKE $1", "true", types="text", values=["AbC"])
    add("nullable-subject", "$1 ILIKE 'a%'", None,
        types="text?", values=[None], nullable=True)
    add("nullable-pattern", "'AbC' ILIKE $1", None,
        types="text?", values=[None], nullable=True)
    add("bound-char-subject", "CAST($1 AS CHAR(5)) ILIKE $2", "false",
        types="text,text", values=["AbC", "abc"])
    add("bound-char-pattern", "$1 ILIKE CAST($2 AS CHAR(5))", "true",
        types="text,text", values=["AbC", "abc"])
    add("bound-not", "$1 NOT ILIKE $2", "true", types="text,text", values=["AbC", "z%"])
    add("derived", "d.s ILIKE d.p", "true",
        suffix=" FROM (SELECT 'AbC' AS s, 'abc' AS p) AS d")
    add("ordered", "'AbC' ILIKE 'a%'", "true", suffix=" ORDER BY v DESC NULLS LAST")
    # Strict NULL propagation bypasses execution-time escape validation.
    add("null-bad-pattern", "NULL::TEXT ILIKE $1", None,
        types="text", values=["\\"], nullable=True)

    add = population("regex")
    add("substring", "'abcd' ~ 'bc'", "true")
    add("case-sensitive-miss", "'AbCd' ~ 'bc'", "false")
    add("insensitive", "'AbCd' ~* 'bc'", "true")
    add("negated-sensitive", "'AbCd' !~ 'bc'", "true")
    add("negated-insensitive", "'AbCd' !~* 'bc'", "false")
    add("anchored", "'abc' ~ '^abc$'", "true")
    add("anchored-miss", "'xabc' ~ '^abc$'", "false")
    add("alternation", "'abcd' ~ '(bc|xy)'", "true")
    add("bracket", "'abc3' ~ '[0-9]$'", "true")
    add("dot", "'abc' ~ '^a.c$'", "true")
    add("star", "'ac' ~ '^ab*c$'", "true")
    add("plus", "'abbc' ~ '^ab+c$'", "true")
    add("optional", "'ac' ~ '^ab?c$'", "true")
    add("count", "'abbc' ~ '^ab{2}c$'", "true")
    add("range", "'abbbc' ~ '^ab{2,4}c$'", "true")
    add("empty-pattern", "'abc' ~ ''", "true")
    add("empty-subject", "'' ~ '^$'", "true")
    add("empty-miss", "'' ~ 'a'", "false")
    add("escaped-dot", r"'a.b' ~ '^a\.b$'", "true")
    add("quote", "'O''Brien' ~ '^O''B'", "true")
    add("subject-null", "NULL ~ '^a'", None, nullable=True)
    add("pattern-null", "'abc' ~ NULL", None, nullable=True)
    add("both-null", "NULL ~ NULL", None, nullable=True)
    add("negated-null", "NULL !~* 'a'", None, nullable=True)
    add("varchar-subject", "'abcd'::VARCHAR(3) ~ '^abc$'", "true")
    add("varchar-pattern", "'abc' ~ '^abc$extra'::VARCHAR(5)", "true")
    add("char-subject-padding", "'abc'::CHAR(5) ~ '^abc$'", "false")
    add("char-subject-spaces", "'abc'::CHAR(5) ~ '^abc  $'", "true")
    add("char-pattern-trim", "'abc' ~ '^abc$'::CHAR(8)", "true")
    add("char-both", "'abc'::CHAR(5) ~ '^abc$'::CHAR(8)", "false")
    add("explicit-char-text", "('abc'::CHAR(5))::TEXT ~ '^abc$'", "true")
    add("char-insensitive", "'AbC'::CHAR(5) ~* '^abc  $'", "true")
    add("char-negated", "'abc'::CHAR(5) !~ '^abc$'", "true")
    add("char-negated-insensitive", "'AbC'::CHAR(5) !~* '^abc  $'", "false")
    add("char-null", "NULL::CHAR(5) ~ '^abc$'", None, nullable=True)
    add("concat-left", "'a' || 'bc' ~ '^abc$'", "true")
    add("concat-right-parenthesized", "'abc' ~ ('^a' || 'bc$')", "true")
    add("generic-left-association", "'abc' ~ 'a' || 'bc'", "truebc", type_="text")
    add("not-generic-left-association", "'abc' !~ 'a' || 'bc'", "falsebc", type_="text")
    add("comparison-precedence", "'abc' ~ '^a' = TRUE", "true")
    add("boolean-precedence", "NOT 'abc' ~ 'z' AND TRUE", "true")
    add("case", "CASE WHEN 'abc' ~ '^a' THEN TRUE ELSE FALSE END", "true")
    add("coalesce", "COALESCE(NULL ~ 'a',FALSE)", "false")
    add("anonymous", "? ~* ?", "true", types="text,text", values=["AbC", "^abc$"])
    add("reordered", "$2 !~ $1", "true", types="text,text", values=["^z", "abc"])
    add("repeated", "$1 ~ $1", "true", types="text", values=["abc"])
    add("nullable-binding", "$1 !~* '^a'", None,
        types="text?", values=[None], nullable=True)
    add("null-bad-pattern", "NULL::TEXT ~ $1", None,
        types="text", values=["["], nullable=True)
    add("derived", "d.s ~* d.p", "true",
        suffix=" FROM (SELECT 'AbC' AS s, '^abc$' AS p) AS d")
    add("where-order", "'abc' !~* '^z'", "true",
        suffix=" WHERE 'abc' ~ '^a' ORDER BY v")
    for rows in populations.values():
        assert len(rows) == len({row["sql"] for row in rows}) == 50
    return populations


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--check", action="store_true")
    args = parser.parse_args()
    for factor, rows in cases().items():
        path = ROOT / "fixtures" / factor / "synthetic.json"
        content = json.dumps(rows, indent=2) + "\n"
        if args.check:
            assert path.read_text() == content, f"stale {factor} fixtures"
        else:
            path.parent.mkdir(parents=True, exist_ok=True)
            path.write_text(content)
    print("PASS: 50 ILIKE and 50 regex cases with exact result expectations")


if __name__ == "__main__":
    main()
