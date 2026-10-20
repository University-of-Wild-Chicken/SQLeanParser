"""Recognize complete literal query blocks in the pinned SQLLogicTest files.

This deliberately small source-format reader does not run SQL or test directives.
It accepts comments, blank lines, statement records, and query records. Query
results are skipped as opaque text; they are never PostgreSQL expectations.
"""
from __future__ import annotations

import re

from extract_extended_type_corpus import sql_code

HEADER = re.compile(r"query [IRTB]+(?: (?:nosort|rowsort|valuesort))?")
SELECTOR_KEYS = {"kind", "start", "end", "header_line"}


def query_blocks(source: str) -> list[dict]:
    lines = source.splitlines(keepends=True)
    offsets, position = [], 0
    for line in lines:
        offsets.append(position)
        position += len(line)
    offsets.append(position)
    result, index = [], 0
    while index < len(lines):
        header = lines[index].rstrip("\r\n")
        if not header.strip() or header.startswith("#"):
            index += 1
            continue
        if re.fullmatch(r"statement (?:ok|error(?: .*)?)", header):
            # These unselected records have no role in query extraction.
            index += 1
            while index < len(lines) and lines[index].strip():
                index += 1
            continue
        if HEADER.fullmatch(header) is None:
            raise ValueError("unsupported SQLLogicTest top-level directive")
        header_line, start = index + 1, offsets[index + 1]
        index += 1
        while index < len(lines) and lines[index].rstrip("\r\n") != "----":
            if not lines[index].strip():
                raise ValueError("SQLLogicTest query lacks its result delimiter")
            index += 1
        if index == len(lines):
            raise ValueError("unterminated SQLLogicTest query block")
        end = offsets[index]
        if start == end:
            raise ValueError("empty SQLLogicTest query block")
        result.append({"header_line": header_line, "start": start, "end": end,
                       "query_header": header})
        index += 1
        # Consume the result section before considering any further headers.
        while index < len(lines) and lines[index].strip():
            index += 1
    return result


def selected_sqllogic_sql(source: str, selector: dict) -> tuple[str, int, dict]:
    if (set(selector) != SELECTOR_KEYS or selector["kind"] != "sqllogic_query"
            or any(type(selector[key]) is not int for key in SELECTOR_KEYS - {"kind"})):
        raise ValueError("invalid SQLLogicTest query selector")
    block = next((entry for entry in query_blocks(source)
                  if entry["header_line"] == selector["header_line"]), None)
    if block is None or any(block[key] != selector[key] for key in ("start", "end")):
        raise ValueError("selection is not a complete SQLLogicTest query block")
    sql = source[block["start"]:block["end"]]
    code = sql_code(sql).strip()
    if (not re.match(r"(SELECT|WITH)\b", code, re.I)
            or ";" in code.removesuffix(";")):
        raise ValueError("selected SQLLogicTest block must contain one whole SELECT")
    if re.search(r"\$\{|\$[A-Za-z_]|__TEST_DIR__", sql):
        raise ValueError("SQLLogicTest substitutions are outside the literal source population")
    detail = {**block, "extraction": "sqllogic_query"}
    return sql, block["header_line"] + 1, detail
