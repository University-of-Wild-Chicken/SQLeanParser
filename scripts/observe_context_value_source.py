"""Finite source observations of SQL context names, without context evaluation."""
from __future__ import annotations

import re

from extract_extended_type_corpus import sql_code

CONTEXT_NAMES = {
    "SVFOP_CURRENT_SCHEMA": "current_schema",
    "SVFOP_CURRENT_CATALOG": "current_catalog",
    "SVFOP_CURRENT_USER": "current_user",
    "SVFOP_USER": "user",
    "SVFOP_CURRENT_ROLE": "current_role",
    "SVFOP_SESSION_USER": "session_user",
}
CONTEXT_CALLS = {"current_schema", "current_database"}
KEYWORD_NAMES = {*CONTEXT_NAMES.values(), "system_user"}


def context_spelling(sql: str, name: str, form: str, location: int) -> None:
    if type(location) is not int or location < 0:
        raise ValueError("context name has no source position")
    try:
        position = len(sql.encode()[:location].decode())
    except UnicodeDecodeError as error:
        raise ValueError("context name location is not a UTF-8 boundary") from error
    code = sql_code(sql)
    suffix = r"\s*\(\s*\)" if form == "call" else ""
    match = re.match(re.escape(name) + r"(?![A-Za-z_0-9$])" + suffix,
                     code[position:], re.I)
    if not match or (position and (code[position - 1].isalnum()
                                  or code[position - 1] in "_$.")):
        raise ValueError("context occurrence disagrees with its original source spelling")
    if form == "keyword" and re.match(r"\s*[.(]", code[position + len(match[0]):]):
        raise ValueError("bare context keyword cannot stand for a qualified name/call")


def validate_context_values(observation: dict, sql: str | None = None) -> None:
    if type(observation.get("source_free")) is not bool:
        raise ValueError("context source-free observation must be Boolean")
    values = observation.get("context_values")
    if not isinstance(values, list) or not values:
        raise ValueError("context-name factor is absent")
    for value in values:
        if (not isinstance(value, dict) or set(value) != {"name", "form", "byte_location"}
                or value["form"] not in {"keyword", "call"}
                or not isinstance(value["name"], str)
                or value["name"] not in (CONTEXT_CALLS if value["form"] == "call"
                                         else KEYWORD_NAMES)
                or type(value["byte_location"]) is not int or value["byte_location"] < 0):
            raise ValueError("invalid source context-name occurrence")
        if sql is not None:
            context_spelling(sql, value["name"], value["form"], value["byte_location"])
    locations = [value["byte_location"] for value in values]
    if len(set(locations)) != len(locations):
        raise ValueError("duplicate source context-name occurrence")


def observe_context_values(parsed: dict, sql: str) -> dict:
    if set(parsed) != {"SelectStmt"}:
        raise ValueError("context source must be one whole SELECT")
    entries = []
    source_free = True

    def spelling(name: str, form: str, location: int) -> None:
        context_spelling(sql, name, form, location)
        entries.append({"name": name, "form": form, "byte_location": location})

    def walk(value):
        nonlocal source_free
        if isinstance(value, list):
            for item in value:
                walk(item)
        elif isinstance(value, dict):
            for kind, node in value.items():
                if kind in {"InsertStmt", "UpdateStmt", "DeleteStmt", "MergeStmt",
                            "RangeFunction", "WindowDef", "NamedArgExpr", "CollateClause"}:
                    raise ValueError("later dependency is outside this context source population")
                if kind in {"RangeVar", "ColumnRef", "ParamRef"}:
                    source_free = False
                if kind == "SQLValueFunction":
                    name = CONTEXT_NAMES.get(node.get("op"))
                    if name is None or node.get("typmod", -1) != -1:
                        raise ValueError("temporal/modified value is outside the context-name factor")
                    spelling(name, "keyword", node.get("location"))
                if kind == "FuncCall":
                    names = [part.get("String", {}).get("sval") for part in node.get("funcname", [])]
                    system_keyword = (names == ["pg_catalog", "system_user"]
                                      and node.get("funcformat") == "COERCE_SQL_SYNTAX")
                    if system_keyword or (names and names[-1] in CONTEXT_CALLS):
                        modified = any(node.get(key) for key in (
                            "args", "agg_order", "agg_filter", "over", "agg_star",
                            "agg_distinct", "agg_within_group", "func_variadic"))
                        if modified or (not system_keyword and len(names) != 1):
                            raise ValueError("context call must be unqualified with no arguments/modifiers")
                        spelling("system_user" if system_keyword else names[0],
                                 "keyword" if system_keyword else "call", node.get("location"))
                walk(node)

    walk(parsed)
    result = {"source_free": source_free, "context_values": entries}
    validate_context_values(result)
    return result
