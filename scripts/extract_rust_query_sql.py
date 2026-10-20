"""Read literal query/description tuples in a pinned Rust test's Vec declaration.

This is a finite source-format recognizer, not a Rust interpreter or general
parser. Comments and other strings cannot contribute token boundaries. Only
unescaped ordinary string tokens in the exact declaration below are selected.
"""
from __future__ import annotations

import re

from extract_extended_type_corpus import sql_code

HEADER = ["let", "queries", ":", "Vec", "<", "(", "&", "str", ",", "&", "str",
          ")", ">", "=", "vec", "!", "["]


def tokens(source: str) -> list[dict]:
    result, i = [], 0
    while i < len(source):
        if source[i].isspace():
            i += 1
            continue
        if source.startswith("//", i):
            end = source.find("\n", i)
            i = len(source) if end < 0 else end + 1
            continue
        if source.startswith("/*", i):
            depth, i = 1, i + 2
            while i < len(source) and depth:
                if source.startswith("/*", i):
                    depth, i = depth + 1, i + 2
                elif source.startswith("*/", i):
                    depth, i = depth - 1, i + 2
                else:
                    i += 1
            if depth:
                raise ValueError("unterminated Rust comment")
            continue
        start = i
        raw = re.match(r'(?:br|cr|r)(#*)"', source[i:])
        if raw:
            close = '"' + raw[1]
            end = source.find(close, i + len(raw[0]))
            if end < 0:
                raise ValueError("unterminated Rust raw string")
            i = end + len(close)
            kind = "other-string"
        elif source[i] == '"' or source.startswith(('b"', 'c"'), i):
            quote = i if source[i] == '"' else i + 1
            escaped, i = False, quote + 1
            while i < len(source) and source[i] != '"':
                if source[i] == "\\":
                    escaped, i = True, i + 2
                else:
                    i += 1
            if i >= len(source):
                raise ValueError("unterminated Rust string")
            i += 1
            kind = "string" if quote == start and not escaped else "other-string"
        elif source[i] == "'":
            # Character tokens are opaque; lifetimes are separate identifiers.
            char = re.match(r"'(?:\\(?:u\{[0-9A-Fa-f_]+\}|x[0-9A-Fa-f]{2}|.)|[^'\\])'", source[i:])
            if char:
                i += len(char[0])
                kind = "other-string"
            else:
                i += 1
                kind = "punct"
        else:
            word = re.match(r"[A-Za-z_][A-Za-z_0-9]*", source[i:])
            i += len(word[0]) if word else 1
            kind = "word" if word else "punct"
        result.append({"kind": kind, "text": source[start:i], "start": start, "end": i})
    return result


def query_literals(source: str) -> list[dict]:
    stream, result = tokens(source), []
    words = [token["text"] for token in stream]
    for start in range(len(stream) - len(HEADER) + 1):
        if words[start:start + len(HEADER)] != HEADER:
            continue
        i = start + len(HEADER)
        while i < len(stream) and words[i] != "]":
            if words[i] != "(":
                raise ValueError("Rust query vector must contain literal pairs")
            i += 1
            if i + 3 >= len(stream) or stream[i]["kind"] != "string" or words[i + 1] != ",":
                raise ValueError("Rust query must be a plain unescaped string")
            query = stream[i]
            if stream[i + 2]["kind"] != "string":
                raise ValueError("Rust query description must be a plain string")
            i += 3
            if words[i] == ",":
                i += 1
            if i >= len(stream) or words[i] != ")":
                raise ValueError("Rust query tuple is not a complete literal pair")
            i += 1
            if i < len(stream) and words[i] == ",":
                i += 1
            elif i >= len(stream) or words[i] != "]":
                raise ValueError("Rust query tuples require separators")
            result.append(query)
        if i + 1 >= len(stream) or words[i:i + 2] != ["]", ";"]:
            raise ValueError("unterminated Rust query vector")
    return result


def selected_rust_sql(source: str, selector: dict) -> tuple[str, int, dict]:
    if (set(selector) != {"kind", "start", "end"} or selector["kind"] != "rust_string"
            or type(selector["start"]) is not int or type(selector["end"]) is not int):
        raise ValueError("invalid Rust query selector")
    token = next((item for item in query_literals(source)
                  if item["start"] == selector["start"] and item["end"] == selector["end"]), None)
    if token is None:
        raise ValueError("selection is not a whole Rust query string token")
    sql = token["text"][1:-1]
    code = sql_code(sql).strip()
    if not re.match(r"(SELECT|WITH)\b", code, re.I) or ";" in code.removesuffix(";"):
        raise ValueError("Rust query string must contain one whole SELECT")
    return sql, source.count("\n", 0, token["start"]) + 1, {
        "extraction": "rust_string", "source_start": token["start"], "source_end": token["end"]}
