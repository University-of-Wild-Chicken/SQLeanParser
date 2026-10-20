"""Independent bounded observer for SQL template binding positions.

This is neither a SQL validator nor a PostgreSQL parser. It observes supported
expression/clause boundaries, quoted values, comments and maximal operators in
already-admitted fixture SQL. PostgreSQL question operators do not bind values.
The explicit template extension allows a leading primary '?' and a supported
infix operator followed by '?' in one run (1=?, ?+?, ?||?, CAST(?)??).
Unsupported native runs such as ?- or ?! in infix position stay whole.

Offsets are Python character offsets into the unchanged input. No SQL runs.
"""
from __future__ import annotations

from dataclasses import dataclass
import re


@dataclass(frozen=True)
class ObservedToken:
    kind: str
    value: object
    depth: int
    start: int
    end: int


_OP_CHARS = frozenset("~!@#^&|`?+-*/%<>=")
_SPECIAL = frozenset("~!@#^&|`?%")
_SUPPORTED = ("->>", "#>>", "!~*", "<=", ">=", "<>", "!=", "||", "&&", "~*", "!~",
              "->", "#>", "@>", "<@", "?|", "?&", "+", "-", "*", "/", "=", "<", ">", "~", "?")
_START_WORDS = frozenset("SELECT WHERE ON HAVING LIMIT OFFSET RETURNING WHEN THEN ELSE CASE "
                        "AND OR NOT IS IN BETWEEN LIKE ILIKE AS FROM FOR BY VALUES SET USING "
                        "ESCAPE SIMILAR DISTINCT UNION INTERSECT EXCEPT".split())
_NUMBER = re.compile(r"(?:[0-9]+(?:\.[0-9]*)?|\.[0-9]+)(?:[eE][+-]?[0-9]+)?")
_DOLLAR = re.compile(r"\$(?:[A-Za-z_][A-Za-z_0-9]*)?\$")


def _lex(source, mode):
    """Yield lexical units including atoms needed to identify expression ends."""
    i = 0
    while i < len(source):
        start = i
        if source[i].isspace():
            i += 1
            continue
        if source.startswith("--", i):
            end = source.find("\n", i + 2)
            i = len(source) if end < 0 else end + 1
            continue
        if source.startswith("/*", i):
            nesting, i = 1, i + 2
            while i < len(source) and nesting:
                if source.startswith("*/", i):
                    nesting, i = nesting - 1, i + 2
                elif mode != "sqlite" and source.startswith("/*", i):
                    nesting, i = nesting + 1, i + 2
                else:
                    i += 1
            assert nesting == 0, "unterminated observed comment"
            continue
        escaped = mode != "sqlite" and source[i:i + 2].upper() == "E'"
        prefixed = mode != "sqlite" and source[i:i + 2].upper() in ("E'", "B'", "X'", "N'")
        if source[i] in "'\"" or prefixed:
            if prefixed:
                i += 1
            quote = source[i]
            i += 1
            while i < len(source):
                if escaped and source[i] == "\\":
                    i += 2
                elif source[i] == quote:
                    i += 1
                    if i < len(source) and source[i] == quote:
                        i += 1
                    else:
                        break
                else:
                    i += 1
            else:
                raise AssertionError("unterminated observed quoted text")
            assert i <= len(source), "unterminated observed escape"
            yield "atom", source[start:i], start, i
            continue
        dollar = _DOLLAR.match(source, i) if mode != "sqlite" else None
        if dollar:
            end = source.find(dollar[0], dollar.end())
            assert end >= 0, "unterminated observed dollar quote"
            i = end + len(dollar[0])
            yield "atom", source[start:i], start, i
            continue
        if source[i] == "$" or (mode == "sqlite" and source[i] == "?" and source[i + 1:i + 2].isdigit()):
            i += 1
            digits = i
            while i < len(source) and source[i].isdigit():
                i += 1
            assert i > digits, "bare dollar marker"
            assert int(source[digits:i]) > 0, "nonpositive parameter index"
            assert i == len(source) or not (source[i].isalnum() or source[i] in "_$"), "invalid parameter suffix"
            yield "numbered", int(source[digits:i]), start, i
            continue
        if source[i].isalpha() or source[i] == "_":
            i += 1
            while i < len(source) and (source[i].isalnum() or source[i] in "_$"):
                i += 1
            yield "word", source[start:i].upper(), start, i
            continue
        number = _NUMBER.match(source, i)
        if number:
            i = number.end()
            yield "atom", source[start:i], start, i
            continue
        if source.startswith("::", i):
            i += 2
            yield "op", "::", start, i
            continue
        if source[i] in _OP_CHARS:
            if mode == "sqlite":
                # SQLite bindings are always lexical; PostgreSQL operators
                # have no SQLite semantics in this observation profile.
                if source[i] == "?":
                    i += 1
                    yield "anonymous", None, start, i
                    continue
                i += 1
                while i < len(source) and source[i] in _OP_CHARS - {"?"}:
                    if source.startswith("--", i) or source.startswith("/*", i):
                        break
                    i += 1
            else:
                i += 1
                while i < len(source) and source[i] in _OP_CHARS:
                    if source.startswith("--", i) or source.startswith("/*", i):
                        break
                    i += 1
                raw = source[start:i]
                if not any(c in _SPECIAL for c in raw):
                    stripped = raw.rstrip("+-")
                    i = start + (len(stripped) if stripped else 1)
            yield "op", source[start:i], start, i
            continue
        i += 1
        yield "punct", source[start:i], start, i


def observe_sql(source, mode="postgres"):
    """Observe lexical bindings and words, retaining exact replacement spans.

    The SELECT-prefix stack handles DISTINCT ON (...) before the first item;
    ordinary closing parentheses instead finish an expression. Word tokens
    after a dot are identifiers even when spelled SELECT, FROM or another
    keyword. This deliberately finite observer does not infer SQL types.
    """
    assert mode in ("postgres", "identity", "sqlite"), "unknown SQL observation mode"
    tokens = []
    depth, ordinal = 0, 0
    operand, after_dot = True, False
    groups, select_prefix = [], {}
    for kind, value, start, end in _lex(source, mode):
        if kind == "punct":
            if value == "(":
                special = select_prefix.get(depth) == "on"
                groups.append(special)
                select_prefix.pop(depth, None)
                depth += 1
                operand = True
            elif value == ")":
                assert groups, "unbalanced observed parentheses"
                select_prefix.pop(depth, None)
                operand = groups.pop()
                depth -= 1
            elif value in (",", "[", ";", ":"):
                operand = True
            elif value == "]":
                operand = False
            after_dot = value == "."
            continue
        if kind == "word":
            if after_dot:
                operand = False
            elif value == "SELECT":
                select_prefix[depth] = "select"
                operand = True
            elif value in ("DISTINCT", "ALL") and select_prefix.get(depth) == "select":
                select_prefix[depth] = "distinct" if value == "DISTINCT" else "item"
                operand = True
            elif value == "ON" and select_prefix.get(depth) == "distinct":
                select_prefix[depth] = "on"
                operand = True
            else:
                select_prefix.pop(depth, None)
                operand = value in _START_WORDS
            tokens.append(ObservedToken("word", value, depth, start, end))
            after_dot = False
            continue
        after_dot = False
        if kind in ("anonymous", "numbered"):
            if kind == "anonymous":
                ordinal += 1
                parameter = ("anonymous", ordinal)
            else:
                parameter = ("numbered", value)
            tokens.append(ObservedToken("parameter", parameter, depth, start, end))
            select_prefix.pop(depth, None)
            operand = False
        elif kind == "atom":
            operand = False
            select_prefix.pop(depth, None)
        elif kind == "op":
            raw, cursor = value, start
            while raw:
                if mode != "sqlite" and operand and raw.startswith("?") and (not raw.startswith("?|") or raw.startswith("?||")) and (not raw.startswith("?&") or raw.startswith("?&&")):
                    assert cursor + 1 == len(source) or not source[cursor + 1].isdigit(), "unexpected numbered question marker"
                    ordinal += 1
                    tokens.append(ObservedToken("parameter", ("anonymous", ordinal), depth, cursor, cursor + 1))
                    select_prefix.pop(depth, None)
                    operand, cursor, raw = False, cursor + 1, raw[1:]
                elif mode != "sqlite" and operand and "?" in raw and raw[0] in "+-":
                    cursor, raw = cursor + 1, raw[1:]
                elif mode != "sqlite" and not operand and "?" in raw and raw not in _SUPPORTED:
                    piece = next((op for op in _SUPPORTED if raw.startswith(op + "?")), None)
                    if piece:
                        operand, cursor, raw = True, cursor + len(piece), raw[len(piece):]
                    else:
                        operand, raw = True, ""
                else:
                    operand, raw = True, ""
    assert depth == 0, "unbalanced observed parentheses"
    return tokens


def parameter_spans(source, mode="postgres"):
    return [token for token in observe_sql(source, mode) if token.kind == "parameter"]


def postgres_parameters(source):
    """Replace only true anonymous binding spans; preserve all other bytes."""
    spans = parameter_spans(source, "postgres")
    styles = {token.value[0] for token in spans}
    assert len(styles) <= 1, "mixed parameter styles"
    output, previous = [], 0
    for token in spans:
        if token.value[0] != "anonymous":
            continue
        output.extend((source[previous:token.start], f"${token.value[1]}"))
        previous = token.end
    output.append(source[previous:])
    return "".join(output)
