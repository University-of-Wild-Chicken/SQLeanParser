"""Select complete literal queries from a bounded SQLLogicTest prefix.

The pinned SUBSTRING and JSONB-existence inputs use Cockroach-style headers.
This reader recognizes the prefix through the selected record, never executes
directives, and leaves result sections opaque. Unknown directives before that
record fail. The default selection remains query T; only the existence factor
opts into query B/BB. The stricter reader for other populations is unchanged.
"""
from __future__ import annotations

import re

from extract_extended_type_corpus import sql_code

HEADER = re.compile(r"query [IRTB]+(?: (?:nosort|rowsort|valuesort|colnames|colnames,rowsort))?")
KEYS = {"kind", "start", "end", "header_line"}


def selected_cockroach_sql(source: str, selector: dict, *,
                          boolean_queries: bool = False) -> tuple[str, int, dict]:
    if (set(selector) != KEYS or selector["kind"] != "cockroach_sqllogic_query"
            or any(type(selector[key]) is not int for key in KEYS - {"kind"})
            or selector["header_line"] < 1):
        raise ValueError("invalid Cockroach SQLLogicTest selector")
    lines = source.splitlines(keepends=True)
    offsets, position = [], 0
    for line in lines:
        offsets.append(position)
        position += len(line)
    offsets.append(position)
    index, records, mode = 0, 0, False
    while index < len(lines) and index + 1 <= selector["header_line"]:
        header = lines[index].rstrip("\r\n")
        if not header.strip() or header.startswith("#"):
            index += 1
            continue
        if header == "mode cockroach" and not records and not mode:
            mode = True
            index += 1
            continue
        if re.fullmatch(r"(?:statement (?:ok|error(?: .*)?)|query error(?: .*)?)", header):
            # These complete unselected records do not supply SQL or expectations.
            records += 1
            index += 1
            while index < len(lines) and lines[index].strip():
                index += 1
            continue
        if HEADER.fullmatch(header) is None:
            raise ValueError("unsupported directive before selected SQLLogicTest query")
        records += 1
        header_line, start = index + 1, offsets[index + 1]
        index += 1
        while index < len(lines) and lines[index].rstrip("\r\n") != "----":
            if not lines[index].strip():
                raise ValueError("SQLLogicTest query lacks its result delimiter")
            index += 1
        if index == len(lines):
            raise ValueError("unterminated SQLLogicTest query")
        end = offsets[index]
        if start == end:
            raise ValueError("empty SQLLogicTest query")
        if header_line == selector["header_line"]:
            allowed_headers = {"query B", "query BB"} if boolean_queries else {"query T"}
            if header not in allowed_headers or (start, end) != (selector["start"], selector["end"]):
                raise ValueError("selection is not the complete pinned literal query")
            sql = source[start:end]
            code = sql_code(sql).strip()
            if (not re.match(r"SELECT\b", code, re.I)
                    or ";" in code.removesuffix(";")
                    or re.search(r"\$\{|[$][A-Za-z_]|\{[A-Za-z_][A-Za-z_0-9]*\}|__TEST_DIR__", sql)):
                raise ValueError("selected query is not one literal SELECT")
            return sql, header_line + 1, {
                "header_line": header_line, "start": start, "end": end,
                "query_header": header, "extraction": "cockroach_sqllogic_query",
            }
        index += 1
        while index < len(lines) and lines[index].strip():
            index += 1
    raise ValueError("selection is not a recognized SQLLogicTest query header")
