"""Finite input-only SQLLogicTest reader for the pinned set-operation files.

Materialize's unselected multiline plans end at a literal EOF line. Their
contents stay opaque, as do ordinary expected results. No SQL, connection
directive, or conditional directive is executed.
"""
from __future__ import annotations

import re

from extract_extended_type_corpus import sql_code

KEYS = {"kind", "header_line", "start", "end"}
HEADER = re.compile(r"query [IRTB]+(?: (?:nosort|rowsort|valuesort|colnames|colnames,rowsort|multiline))?")


def selected_setop_sqllogic(source, selector):
    if (set(selector) != KEYS or selector["kind"] != "setop_sqllogic_query"
            or any(type(selector[k]) is not int for k in KEYS - {"kind"})
            or selector["header_line"] < 1):
        raise ValueError("invalid set-operation SQLLogicTest selector")
    lines = source.splitlines(keepends=True)
    offsets, offset = [], 0
    for line in lines:
        offsets.append(offset)
        offset += len(line)
    index, conditional, mode = 0, False, False
    while index < len(lines) and index + 1 <= selector["header_line"]:
        header = lines[index].rstrip("\r\n")
        if not header.strip() or header.startswith("#"):
            index += 1
            continue
        if header == "mode cockroach" and not mode and not conditional:
            mode = True
            index += 1
            continue
        if header == "onlyif cockroach" and not conditional:
            conditional = True
            index += 1
            continue
        if re.fullmatch(r"(?:statement (?:ok|OK|error(?: .*)?)|query error(?: .*)?)", header):
            index += 1
            while index < len(lines) and lines[index].strip():
                index += 1
            conditional = False
            continue
        simple = header == "simple conn=mz_system,user=mz_system"
        if not simple and HEADER.fullmatch(header) is None:
            raise ValueError("unsupported directive before selected set-operation query")
        if simple and conditional:
            raise ValueError("conditional connection directives are outside this reader")
        header_line, start = index + 1, offsets[index + 1] if index + 1 < len(lines) else len(source)
        index += 1
        omitted_result = False
        while index < len(lines) and lines[index].rstrip("\r\n") != "----":
            if not lines[index].strip():
                # The pinned Cockroach file contains an unselected query with
                # an omitted empty-result separator. It cannot supply a source
                # selection; selected inputs always require an exact delimiter.
                if (header_line != selector["header_line"] and not simple
                        and not header.endswith(" multiline") and offsets[index] > start):
                    omitted_result = True
                    break
                raise ValueError(f"SQLLogicTest input at line {header_line} lacks its result delimiter")
            index += 1
        if omitted_result:
            conditional = False
            continue
        if index == len(lines) or offsets[index] == start:
            raise ValueError("empty or unterminated SQLLogicTest input")
        end = offsets[index]
        if header_line == selector["header_line"]:
            if simple or header.endswith(" multiline") or (start, end) != (selector["start"], selector["end"]):
                raise ValueError("selection is not a complete ordinary query input")
            sql = source[start:end]
            code = sql_code(sql).strip()
            if (not re.match(r"\(*\s*(?:SELECT|WITH)\b", code, re.I)
                    or ";" in code.removesuffix(";")
                    or re.search(r"\$\{|[$][A-Za-z_]|__TEST_DIR__", sql)):
                raise ValueError("selected input is not one literal SELECT")
            return sql, header_line + 1, {
                "extraction": "setop_sqllogic_query", "header_line": header_line,
                "start": start, "end": end, "query_header": header,
                "source_condition": "onlyif cockroach" if conditional else None,
            }
        index += 1
        if header.endswith(" multiline"):
            while index < len(lines) and lines[index].rstrip("\r\n") != "EOF":
                index += 1
            if index == len(lines):
                raise ValueError("unterminated opaque multiline SQLLogicTest result")
            index += 1
        else:
            while index < len(lines) and lines[index].strip():
                index += 1
        conditional = False
    raise ValueError("selection is not a recognized query input")
