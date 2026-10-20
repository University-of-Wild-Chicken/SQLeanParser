"""Read the closed corpus's complete plain Go query literals without evaluation."""
from __future__ import annotations

import json
import re

from extract_application_corpus import go_tokens
from extract_extended_type_corpus import sql_code


def whole_select(sql: str) -> None:
    code = sql_code(sql).strip()
    if (not re.match(r"SELECT\b", code, re.I) or ";" in code.removesuffix(";")
            or "\x00" in sql or re.search(r"%[sdv]|__TEST_DIR__|\$\{", sql)):
        raise ValueError("query literal is not one complete static SELECT")


def selected_go_query(source: str, selector: dict, *,
                      assertion_query: bool = False) -> tuple[str, int, dict]:
    keys = {"kind", "start", "end", "token_index"}
    if (set(selector) != keys or selector["kind"] != "go_string_literal"
            or any(type(selector[key]) is not int for key in keys - {"kind"})):
        raise ValueError("invalid Go query-literal selector")
    tokens = [token for token in go_tokens(source) if token.kind != "newline"]
    # The stored index uses the original token stream, including line breaks.
    original = go_tokens(source)
    for offset, item in enumerate(original):
        if item.kind == "symbol" and item.text in {'"', "'", "`"}:
            raise ValueError("unterminated Go quoted region")
        if (item.text == "/" and offset + 1 < len(original)
                and original[offset + 1].text == "*"
                and item.end == original[offset + 1].start):
            raise ValueError("unterminated Go block comment")
    index = selector["token_index"]
    if not 0 <= index < len(original):
        raise ValueError("Go query token index is outside its source")
    token = original[index]
    if (token.kind != "string" or "\\" in token.text
            or (token.start, token.end) != (selector["start"], selector["end"])):
        raise ValueError("selection is not a complete plain Go string token")
    position = tokens.index(token)
    before = tokens[:position]
    after = tokens[position + 1:]
    map_value = (len(before) >= 2 and before[-1].text == ":"
                 and before[-2].kind == "string" and after and after[0].text == ",")
    call_argument = (
        len(before) >= 4 and [item.text for item in before[-3:]] == ["(", "ctx", ","]
        and before[-4].text in {"QueryRow", "QueryRowContext"}
        and after and after[0].text == ")")
    assertion_field = (assertion_query and len(before) >= 3
                       and [item.text for item in before[-3:]] == ["{", "Query", ":"]
                       and after and after[0].text == ",")
    if not ((assertion_field if assertion_query else map_value or call_argument)):
        raise ValueError("query literal is outside the pinned map/call contexts")
    sql = json.loads(token.text)
    whole_select(sql)
    return sql, source.count("\n", 0, token.start) + 1, {
        "source_start": token.start, "source_end": token.end,
        "token_index": index, "source_expression": token.text,
        "extraction": "go_string_literal",
    }


def selected_whole_sql(source: str, selector: dict) -> tuple[str, int, dict]:
    if selector != {"kind": "whole_sql_file"}:
        raise ValueError("invalid whole-SQL-file selector")
    whole_select(source)
    return source, 1, {"extraction": "whole_sql_file"}
