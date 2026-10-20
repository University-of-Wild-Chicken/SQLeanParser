"""Finite, non-executing readers for the pinned NULL-predicate source inputs.

Only complete input SELECTs are selected. H2 EXPLAIN bodies retain the complete
wrapper as provenance; generated expected plans/results never supply SQL.
"""
from __future__ import annotations

import ast
import re

from extract_go_query_literal import whole_select
from extract_rust_query_sql import tokens

CONTEXTS = {"h2", "turso", "python", "rust", "java", "calcite"}
KEYS = {"kind", "context", "start", "end", "container_start", "container_end"}


def selected_null_input(source: str, selector: dict) -> tuple[str, int, dict]:
    if (set(selector) != KEYS or selector["kind"] != "embedded_null_input"
            or selector["context"] not in CONTEXTS
            or any(type(selector[k]) is not int for k in KEYS - {"kind", "context"})):
        raise ValueError("invalid embedded NULL-input selector")
    start, end = selector["start"], selector["end"]
    a, b, context = selector["container_start"], selector["container_end"], selector["context"]
    if not 0 <= a <= start < end <= b <= len(source):
        raise ValueError("embedded input bounds are outside their whole container")
    sql, container = source[start:end], source[a:b]
    if context == "h2":
        if (a and source[a - 1] != "\n" or b < len(source) and source[b] not in "\r\n"
                or re.fullmatch(r"(?:EXPLAIN )?SELECT [^\r\n]+;", container) is None
                or not source[b:].lstrip("\r\n").startswith(">")
                or start != a + (8 if container.startswith("EXPLAIN ") else 0) or end != b):
            raise ValueError("H2 input must be a whole input line, optionally an EXPLAIN body")
        # This closed file uses line comments; no selected input may be hidden
        # in a block comment or an expected-output line.
        for line in source[:a].splitlines():
            if not line.strip() or line.startswith(("--", ">")):
                continue
            if re.fullmatch(r"(?:SELECT|EXPLAIN SELECT|CREATE TABLE|CREATE INDEX|DROP TABLE) [^\r\n]+;", line) is None:
                raise ValueError("unrecognized H2 record before selected input")
    elif context == "turso":
        match = re.fullmatch(r"test (?:isnull|notnull) \{\n(?P<sql>[^{}]+)\}", container)
        if (match is None or a and source[a - 1] != "\n"
                or (a + match.start("sql"), a + match.end("sql")) != (start, end)
                or not source[b:].lstrip().startswith("expect {")):
            raise ValueError("Turso input must be the complete literal test block")
    elif context == "calcite":
        previous = source[:a].rstrip().splitlines()[-1:]
        if (a != start or b != end or a and source[a - 1] != "\n"
                or previous != ["# [CALCITE-3627] Null check if all fields of ROW are null"]
                or not source[b:].startswith("\n+---") or not container.endswith(";")):
            raise ValueError("Calcite selection is not the registered whole input query")
    elif context == "python":
        matches = []
        for node in ast.walk(ast.parse(source)):
            if (not isinstance(node, ast.Call) or not isinstance(node.func, ast.Attribute)
                    or node.func.attr != "validate_identity" or not node.args
                    or not isinstance(node.args[0], ast.Constant)):
                continue
            arg = node.args[0]
            lines = source.splitlines(keepends=True)
            left = sum(map(len, lines[:arg.lineno - 1])) + len(lines[arg.lineno - 1].encode()[:arg.col_offset].decode())
            right = sum(map(len, lines[:arg.end_lineno - 1])) + len(lines[arg.end_lineno - 1].encode()[:arg.end_col_offset].decode())
            if (left, right) == (a, b):
                matches.append(arg.value)
        if (matches != [sql] or (start, end) != (a + 1, b - 1)
                or container[0] != '"' or container[-1] != '"' or "\\" in container):
            raise ValueError("Python source is not a whole plain first input argument")
    else:
        stream = tokens(source)
        index = next((i for i, t in enumerate(stream) if (t["start"], t["end"]) == (a, b)), None)
        if (index is None or stream[index]["kind"] != "string" or (start, end) != (a + 1, b - 1)):
            raise ValueError("source is not one complete plain string token")
        words = [t["text"] for t in stream]
        before, after = words[max(0, index - 3):index], words[index + 1:index + 2]
        allowed = (before[-2:] == ["verified_only_select_with_canonical", "("] and after == [","]
                   if context == "rust" else before == ["String", "sqlStr", "="] and after == [";"])
        if not allowed:
            raise ValueError("string is outside its pinned test input position")
    whole_select(sql)
    return sql, source.count("\n", 0, start) + 1, {
        "extraction": "embedded_null_input", "context": context,
        "source_start": start, "source_end": end,
        "container_start": a, "container_end": b, "source_container": container,
    }
