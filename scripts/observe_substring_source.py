"""Closed syntax observations for the fifty unchanged SUBSTRING sources."""
from __future__ import annotations

import re

from extract_extended_type_corpus import sql_code

FORMS = {"from", "for", "from-for", "for-from", "similar-escape", "ordinary"}


def validate_substrings(entries: list[dict]) -> None:
    if not isinstance(entries, list) or len(entries) != 1:
        raise ValueError("expected one source SUBSTRING expression")
    entry = entries[0]
    if (set(entry) != {"form", "arguments", "wrapper", "alias"}
            or entry["form"] not in FORMS
            or entry["wrapper"] not in {"plain", "is-null", "equality"}
            or (entry["alias"] is not None and not isinstance(entry["alias"], str))):
        raise ValueError("invalid SUBSTRING source observation")
    args = entry["arguments"]
    if (not isinstance(args, list) or len(args) not in (2, 3)
            or (entry["form"] == "from" and len(args) != 2)
            or (entry["form"] not in {"ordinary", "from"} and len(args) != 3)):
        raise ValueError("invalid SUBSTRING argument count")
    for arg in args:
        if set(arg) != {"form", "value", "cast"} or arg["cast"] not in {None, "bytea", "pg_catalog.int4"}:
            raise ValueError("invalid literal SUBSTRING argument")
        if not ((arg["form"] == "string" and isinstance(arg["value"], str))
                or (arg["form"] == "integer" and type(arg["value"]) is int)
                or (arg["form"] == "null" and arg["value"] is None)):
            raise ValueError("invalid literal SUBSTRING value")
        if ((arg["cast"] == "bytea" and arg["form"] != "string")
                or (arg["cast"] == "pg_catalog.int4" and arg["form"] != "integer")):
            raise ValueError("invalid literal SUBSTRING cast")
    if entry["form"] == "for":
        if (args[1] != {"form": "integer", "value": 1, "cast": None}
                or args[2]["cast"] != "pg_catalog.int4"):
            raise ValueError("FOR-only parser defaults changed")
    elif any(arg["cast"] == "pg_catalog.int4" for arg in args):
        raise ValueError("implicit FOR-only cast outside its syntax form")
    if any(arg["cast"] == "bytea" for arg in args[1:]):
        raise ValueError("unexpected BYTEA bound/pattern argument")


def observe_substrings(parsed: dict, sql: str) -> dict:
    if not isinstance(parsed, dict) or set(parsed) != {"SelectStmt"}:
        raise ValueError("SUBSTRING source must be a SELECT")
    query = parsed["SelectStmt"]
    if (set(query) - {"targetList", "op", "limitOption"}
            or query.get("op", "SETOP_NONE") != "SETOP_NONE"
            or len(query.get("targetList", [])) != 1):
        raise ValueError("SUBSTRING population is one source-free projection")
    target = query["targetList"][0]["ResTarget"]
    value, wrapper = target["val"], "plain"
    if set(value) == {"NullTest"}:
        node = value["NullTest"]
        if node.get("nulltesttype") != "IS_NULL" or node.get("argisrow"):
            raise ValueError("unsupported SUBSTRING null-test wrapper")
        value, wrapper = node["arg"], "is-null"
    elif set(value) == {"A_Expr"}:
        node = value["A_Expr"]
        if (node.get("kind") != "AEXPR_OP"
                or node.get("name") != [{"String": {"sval": "="}}]
                or set(node.get("rexpr", {})) != {"A_Const"}
                or "sval" not in node["rexpr"]["A_Const"]):
            raise ValueError("unsupported SUBSTRING comparison wrapper")
        value, wrapper = node["lexpr"], "equality"
    if set(value) != {"FuncCall"}:
        raise ValueError("source projection does not contain the required SUBSTRING")
    call = value["FuncCall"]
    if set(call) - {"funcname", "args", "funcformat", "location"}:
        raise ValueError("aggregate/window/variadic SUBSTRING is outside this population")
    names = [name["String"]["sval"] for name in call["funcname"]]
    ordinary = call["funcformat"] == "COERCE_EXPLICIT_CALL"
    if (names != (["substring"] if ordinary else ["pg_catalog", "substring"])
            or call["funcformat"] not in {"COERCE_EXPLICIT_CALL", "COERCE_SQL_SYNTAX"}):
        raise ValueError("unsupported SUBSTRING function identity")
    location = call.get("location")
    if type(location) is not int or location < 0:
        raise ValueError("SUBSTRING spelling has no source location")
    try:
        start = len(sql.encode()[:location].decode())
    except UnicodeDecodeError as error:
        raise ValueError("SUBSTRING location is not a UTF-8 boundary") from error
    code = sql_code(sql)
    match = re.match(r"substring\s*\(", code[start:], re.I)
    if match is None:
        raise ValueError("SUBSTRING location disagrees with its source spelling")
    depth, index, words = 1, start + match.end(), []
    while index < len(code) and depth:
        char = code[index]
        if char == "(":
            depth += 1
        elif char == ")":
            depth -= 1
        elif depth == 1 and (word := re.match(r"[A-Za-z_][A-Za-z_0-9$]*", code[index:])):
            if word[0].upper() in {"FROM", "FOR", "SIMILAR", "ESCAPE"}:
                words.append(word[0].upper())
            index += len(word[0])
            continue
        index += 1
    if depth:
        raise ValueError("unterminated SUBSTRING source spelling")
    forms = {(): "ordinary", ("FROM",): "from", ("FOR",): "for",
             ("FROM", "FOR"): "from-for", ("FOR", "FROM"): "for-from",
             ("SIMILAR", "ESCAPE"): "similar-escape"}
    form = forms.get(tuple(words))
    if form is None or ordinary != (form == "ordinary"):
        raise ValueError("SUBSTRING keyword order disagrees with its raw AST")

    def argument(value):
        cast = None
        if set(value) == {"TypeCast"}:
            node = value["TypeCast"]
            name = node["typeName"]
            cast = ".".join(part["String"]["sval"] for part in name["names"])
            if (name.get("typmods") or name.get("arrayBounds")
                    or cast not in {"bytea", "pg_catalog.int4"}
                    or (cast == "pg_catalog.int4"
                        and (form != "for" or node.get("location") != -1))):
                raise ValueError("nonliteral/unsupported SUBSTRING argument cast")
            value = node["arg"]
        if set(value) != {"A_Const"}:
            raise ValueError("SUBSTRING source arguments must be literal syntax")
        constant = value["A_Const"]
        if constant.get("isnull") is True:
            return {"form": "null", "value": None, "cast": cast}
        if "sval" in constant:
            return {"form": "string", "value": constant["sval"]["sval"], "cast": cast}
        if "ival" in constant:
            return {"form": "integer", "value": constant["ival"].get("ival", 0), "cast": cast}
        raise ValueError("unsupported SUBSTRING literal class")

    entries = [{"form": form, "arguments": [argument(arg) for arg in call["args"]],
                "wrapper": wrapper, "alias": target.get("name")}]
    validate_substrings(entries)
    return {"source_free": True, "substrings": entries}
