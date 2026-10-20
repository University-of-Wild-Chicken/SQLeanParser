"""Read pinned SQL statement spans inside literal SQLite Tcl test blocks.

This is a finite source-format recognizer, not a Tcl interpreter. No Tcl or SQL
is evaluated. Selected blocks must use one of four explicit command spellings,
have balanced literal braces, and require no backslash-newline substitution.
"""
from __future__ import annotations

import re

from extract_statement_corpus import statement_spans


COMMAND = re.compile(
    r"^[ \t]*(?P<command>do_execsql_test|do_catchsql_test|execsql|catchsql)"
    r"(?P<arguments>[ \t][^\n{}]*)\{", re.MULTILINE)
SELECTOR_KEYS = {"kind", "command_start", "block_start", "block_end",
                 "start", "end", "statement_index"}


def block_end(source: str, opening: int) -> int:
    """Locate the matching brace under Tcl's literal-braced-word rules."""
    if not 0 <= opening < len(source) or source[opening] != "{":
        raise ValueError("Tcl SQL block must begin with a literal brace")
    depth, position = 1, opening + 1
    while position < len(source):
        char = source[position]
        if char == "\\":
            position += 2  # Escaped braces do not affect nesting.
            continue
        if char == "{":
            depth += 1
        elif char == "}":
            depth -= 1
            if depth == 0:
                return position
        position += 1
    raise ValueError("unterminated Tcl SQL block")


def selected_tcl_sql(source: str, selector: dict) -> tuple[str, int, dict]:
    if (set(selector) != SELECTOR_KEYS or selector["kind"] != "tcl_sql_statement"
            or any(type(selector[key]) is not int for key in SELECTOR_KEYS - {"kind"})):
        raise ValueError("invalid Tcl SQL selector")
    command_start = selector["command_start"]
    if not 0 <= command_start < len(source) or (
            command_start and source[command_start - 1] != "\n"):
        raise ValueError("Tcl SQL command must begin on the pinned source line")
    command = COMMAND.match(source, command_start)
    if command is None:
        raise ValueError("selected block is not an explicit Tcl SQL command")
    name, arguments = command["command"], command["arguments"].strip()
    if name in ("execsql", "catchsql"):
        if arguments:
            raise ValueError("Tcl SQL command has unsupported arguments")
        test_name = None
    else:
        # Test names may contain loop variables; the literal SQL argument does
        # not undergo their evaluation. SQL itself is never substituted.
        if not re.fullmatch(r'[^\s{}"\\;\[\]]+', arguments):
            raise ValueError("Tcl SQL test name must be one simple source token")
        test_name = arguments
    start = command.end()
    end = block_end(source, start - 1)
    if (start, end) != (selector["block_start"], selector["block_end"]):
        raise ValueError("selected Tcl block is not the pinned complete SQL argument")
    if end + 1 < len(source) and not source[end + 1].isspace():
        raise ValueError("literal Tcl SQL argument has a non-word boundary")
    block = source[start:end]
    if re.search(r"\\\r?\n", block):
        raise ValueError("Tcl backslash-newline substitution would alter source SQL")
    spans = statement_spans(block)
    index = selector["statement_index"]
    if not 0 <= index < len(spans):
        raise ValueError("Tcl SQL statement index is outside the complete block")
    relative_start, relative_end = spans[index]
    absolute_start, absolute_end = start + relative_start, start + relative_end
    if (absolute_start, absolute_end) != (selector["start"], selector["end"]):
        raise ValueError("selected Tcl SQL slice is not the pinned complete statement")
    sql = source[absolute_start:absolute_end]
    detail = {**selector, "extraction": "tcl_sql_statement",
              "tcl_command": name, "tcl_test_name": test_name}
    detail.pop("kind")
    return sql, source.count("\n", 0, absolute_start) + 1, detail
