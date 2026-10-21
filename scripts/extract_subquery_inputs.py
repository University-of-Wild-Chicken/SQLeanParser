"""Finite readers for actual input literals, never plans or executed setup.

These readers serve only the closed pinned subquery population. They retain
complete input boundaries, reject string assembly, and do not evaluate Go,
YAML, Quidem commands, or PostgreSQL view definitions.
"""
from __future__ import annotations

import json
import re

from extract_application_corpus import go_tokens
from extract_extended_type_corpus import sql_code
from extract_statement_corpus import selected_sql, statement_spans


def integers(selector, keys, kind):
    if (set(selector) != keys | {"kind"} or selector["kind"] != kind
            or any(type(selector[k]) is not int for k in keys)):
        raise ValueError("invalid literal input selector")


def complete_select(sql):
    code = sql_code(sql).strip()
    if (not re.match(r"\(*\s*(?:SELECT|WITH)\b", code, re.I)
            or ";" in code.removesuffix(";") or "\x00" in sql):
        raise ValueError("literal must be one complete SELECT input")


def go_query(source, selector):
    integers(selector, {"start", "end", "token_index"}, "go_query_token")
    tokens = go_tokens(source)
    if any(t.kind == "symbol" and t.text in {'"', "'", '`'} for t in tokens):
        raise ValueError("malformed Go quoted region")
    if any(token.text == "/" and tokens[pos + 1].text == "*"
           and token.end == tokens[pos + 1].start for pos, token in enumerate(tokens[:-1])):
        raise ValueError("unterminated Go block comment")
    i = selector["token_index"]
    if not 0 <= i < len(tokens):
        raise ValueError("Go token index outside input")
    token = tokens[i]
    if ((token.start, token.end) != (selector["start"], selector["end"])
            or token.kind not in {"raw", "string"}
            or "\\" in token.text or "\r" in token.text):
        raise ValueError("selection is not a complete unescaped Go SQL token")
    before = [t.text for t in tokens[:i] if t.kind != "newline"]
    after = [t.text for t in tokens[i + 1:] if t.kind != "newline"]
    ordinary = len(before) >= 2 and before[-2:] == ["QueryRow", "("]
    context = len(before) >= 4 and before[-4:] == ["QueryRowContext", "(", "ctx", ","]
    if not (ordinary or context) or not after or after[0] not in {",", ")"}:
        raise ValueError("literal is not a whole query argument of a pinned Go API")
    sql = token.text[1:-1] if token.kind == "raw" else json.loads(token.text)
    complete_select(sql)
    return sql, source.count("\n", 0, token.start) + 1, {
        "extraction": "complete Go query argument token", "source_expression": token.text,
        "source_start": token.start, "source_end": token.end, "token_index": i,
    }


def view_body(source, selector):
    keys = {"kind", "start", "end", "statement_index", "body_start", "container_kind"}
    if (set(selector) != keys or selector["kind"] != "sql_query_body"
            or selector["container_kind"] != "ViewStmt"
            or any(type(selector[k]) is not int for k in keys - {"kind", "container_kind"})):
        raise ValueError("invalid view-body selector")
    a, b, body = (selector[k] for k in ("start", "end", "body_start"))
    container, _, _ = selected_sql(source, {
        "kind": "sql_slice", "start": a, "end": b,
        "statement_index": selector["statement_index"]}, statement_spans(source))
    if not a < body < b or re.fullmatch(
            r"CREATE VIEW [a-zA-Z_][a-zA-Z_0-9]*(?: WITH \(security_barrier = true\))? AS[ \t\r\n]+", source[a:body], re.I) is None:
        raise ValueError("body does not follow the complete pinned CREATE VIEW prefix")
    sql = source[body:b]
    complete_select(sql)
    return sql, source.count("\n", 0, body) + 1, {
        "extraction": "unchanged SELECT body of source CREATE VIEW input",
        "container_sql": container, "container_start": a, "container_end": b,
        "source_start": body, "source_end": b, "source_prefix": source[a:body],
    }


def yaml_query(source, selector):
    integers(selector, {"header_line", "block_start", "block_end", "start", "end", "statement_index"},
             "yaml_sql_statement")
    lines = source.splitlines(keepends=True)
    offsets = [0]
    for line in lines:
        offsets.append(offsets[-1] + len(line))
    i = selector["header_line"] - 1
    if not 0 <= i < len(lines) or lines[i].rstrip("\r\n") != "- sql: |":
        raise ValueError("selection is not a literal YAML sql input block")
    j = i + 1
    while j < len(lines) and (not lines[j].strip() or lines[j].startswith("    ")):
        j += 1
    a, b = offsets[i + 1], offsets[j]
    if ((a, b) != (selector["block_start"], selector["block_end"])
            or j == len(lines) or lines[j].rstrip("\r\n") != "  expected_outputs:"):
        raise ValueError("YAML input is not the exact complete sql block")
    spans = statement_spans(source[a:b])
    selected = {"kind": "sql_slice", "start": selector["start"] - a,
                "end": selector["end"] - a, "statement_index": selector["statement_index"]}
    sql, _, _ = selected_sql(source[a:b], selected, spans)
    complete_select(sql)
    return sql, source.count("\n", 0, selector["start"]) + 1, {
        "extraction": "whole SELECT statement in literal YAML sql input",
        "source_start": selector["start"], "source_end": selector["end"],
        "block_start": a, "block_end": b, "header_line": i + 1,
        "preceding_inputs": [source[a + x:a + y] for x, y in spans[:selector["statement_index"]]],
        "controls_executed": False,
    }


def quidem_query(source, selector):
    integers(selector, {"start", "end"}, "whole_query_input")
    a, b = selector["start"], selector["end"]
    if not 0 <= a < b <= len(source) or a and source[a - 1] != "\n":
        raise ValueError("Quidem selection must start at the beginning of a whole input line")
    before = source[:a].splitlines()
    if before and before[-1].strip() and not before[-1].startswith("#"):
        raise ValueError("selection starts inside an earlier input statement")
    sql = source[a:b]
    if (not sql.endswith(";") or statement_spans(sql) != [(0, len(sql))]
            or re.match(r"\r?\n\+[+-]+\+\r?\n", source[b:]) is None):
        raise ValueError("Quidem input must end before its separate result table")
    complete_select(sql)
    return sql, source.count("\n", 0, a) + 1, {
        "extraction": "complete Quidem SQL input before opaque tabular output",
        "source_start": a, "source_end": b, "controls_executed": False,
    }
