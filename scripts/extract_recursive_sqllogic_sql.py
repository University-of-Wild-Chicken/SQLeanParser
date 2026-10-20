"""Finite input reader for pinned DuckDB recursive-query tests.

Only the literal ``require no_alternative_verify`` control is recognized, and
its presence is retained as provenance. Controls, setup SQL and result text
are never executed or treated as PostgreSQL expectations.
"""
from __future__ import annotations

import re

from extract_extended_type_corpus import sql_code
from extract_sqllogic_sql import HEADER, SELECTOR_KEYS


def selected_recursive_sqllogic(source, selector):
    if (set(selector) != SELECTOR_KEYS or selector["kind"] != "sqllogic_query"
            or any(type(selector[k]) is not int for k in SELECTOR_KEYS - {"kind"})
            or selector["header_line"] < 1):
        raise ValueError("invalid recursive SQLLogicTest selector")
    lines, offsets, position = source.splitlines(keepends=True), [], 0
    for line in lines:
        offsets.append(position)
        position += len(line)
    offsets.append(position)
    index, requirements = 0, []
    while index < len(lines) and index + 1 <= selector["header_line"]:
        header = lines[index].rstrip("\r\n")
        if not header.strip() or header.startswith("#"):
            index += 1
            continue
        if header == "require no_alternative_verify" and not requirements:
            requirements.append(header)
            index += 1
            continue
        if re.fullmatch(r"statement (?:ok|error(?: .*)?)", header):
            index += 1
            while index < len(lines) and lines[index].strip():
                index += 1
            continue
        if HEADER.fullmatch(header) is None:
            raise ValueError("unsupported directive before selected recursive query")
        header_line, start = index + 1, offsets[index + 1]
        index += 1
        while index < len(lines) and lines[index].rstrip("\r\n") != "----":
            if not lines[index].strip():
                raise ValueError("recursive query lacks its result delimiter")
            index += 1
        if index == len(lines) or start == offsets[index]:
            raise ValueError("empty or unterminated recursive query input")
        end = offsets[index]
        if header_line == selector["header_line"]:
            if (start, end) != (selector["start"], selector["end"]):
                raise ValueError("selection does not preserve the whole query block")
            sql = source[start:end]
            code = sql_code(sql).strip()
            if (not re.match(r"(SELECT|WITH)\b", code, re.I)
                    or ";" in code.removesuffix(";")
                    or re.search(r"\$\{|\$[A-Za-z_]|__TEST_DIR__", sql)):
                raise ValueError("selected block must contain one literal SELECT")
            return sql, header_line + 1, {
                "extraction": "recursive_sqllogic_query", "header_line": header_line,
                "start": start, "end": end, "query_header": header,
                "source_requirements": list(requirements),
            }
        index += 1
        while index < len(lines) and lines[index].strip():
            index += 1
    raise ValueError("selection is not a recognized recursive query input")
