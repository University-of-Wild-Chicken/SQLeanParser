"""Closed JSONB-existence source observations; no catalog or execution oracle."""
from __future__ import annotations

import json

from extract_extended_type_corpus import sql_code

OPERATORS = {"?", "?|", "?&"}
KEYS = {"operator", "left_form", "left_cast", "left_literal_null", "right_form", "right_cast"}


def validate_json_existence(observation: dict) -> None:
    entries = observation.get("json_existence")
    if (type(observation.get("source_free")) is not bool
            or not isinstance(entries, list) or not entries):
        raise ValueError("missing JSONB existence observations")
    for entry in entries:
        if (not isinstance(entry, dict) or set(entry) != KEYS
                or entry["operator"] not in OPERATORS
                or entry["left_form"] not in {"TypeCast", "ColumnRef", "A_Expr"}
                or entry["right_form"] not in {"A_Const", "A_ArrayExpr", "TypeCast"}
                or type(entry["left_literal_null"]) is not bool):
            raise ValueError("invalid JSONB existence operand observation")
        if entry["left_cast"] != ("jsonb" if entry["left_form"] == "TypeCast" else None):
            raise ValueError("existence metadata cannot infer a document type")
        if entry["left_literal_null"] and entry["left_form"] != "TypeCast":
            raise ValueError("literal NULL observation requires its explicit JSONB cast")
        if observation["source_free"] != (entry["left_form"] == "TypeCast"):
            raise ValueError("existence source scope and written operands disagree")
        if entry["right_form"] == "TypeCast":
            expected = "text" if entry["operator"] == "?" else "text[]"
            if entry["right_cast"] != expected:
                raise ValueError("unexpected explicit existence key type")
        elif entry["right_cast"] is not None:
            raise ValueError("existence metadata cannot infer a key type")
        if (entry["operator"] == "?" and entry["right_form"] == "A_ArrayExpr"
                or entry["operator"] != "?" and entry["right_form"] == "A_Const"):
            raise ValueError("unexpected key expression in the closed existence population")


def observe_json_existence(parsed: dict, sql: str) -> dict:
    if not isinstance(parsed, dict) or set(parsed) != {"SelectStmt"}:
        raise ValueError("existence source must be one SELECT")
    query = parsed["SelectStmt"]
    if any(query.get(key) for key in ("withClause", "larg", "rarg", "valuesLists",
                                     "groupClause", "havingClause", "lockingClause", "distinctClause")):
        raise ValueError("later query forms are outside this existence population")
    sources = query.get("fromClause", [])
    if len(sources) > 1 or any(
            set(source) != {"RangeVar"} or any(source["RangeVar"].get(key)
                                             for key in ("schemaname", "catalogname", "alias"))
            for source in sources):
        raise ValueError("only one unqualified base source is admitted")
    source_free = not sources
    entries, code = [], sql_code(sql)

    def expression_form(value):
        if not isinstance(value, dict) or len(value) != 1:
            raise ValueError("existence operator requires two expression operands")
        return next(iter(value))

    def literal(value):
        if expression_form(value) != "A_Const":
            raise ValueError("expected a literal source operand")
        node = value["A_Const"]
        if node.get("isnull") is True:
            return None
        text = node.get("sval", {}).get("sval")
        if not isinstance(text, str):
            raise ValueError("expected a string or NULL source literal")
        return text

    def cast(value):
        node = value["TypeCast"]
        name = node.get("typeName", {})
        if name.get("typmods") or name.get("setof") or name.get("pct_type"):
            raise ValueError("modified types are outside this existence population")
        names = [part.get("String", {}).get("sval") for part in name.get("names", [])]
        if names not in (["jsonb"], ["text"], ["pg_catalog", "int8"]):
            raise ValueError("unrecognized explicit existence-related cast")
        bounds = name.get("arrayBounds", [])
        if bounds and bounds != [{"Integer": {"ival": -1}}]:
            raise ValueError("sized or multiple array bounds are outside this population")
        return ".".join(names) + ("[]" if bounds else ""), node.get("arg")

    def invalid_json_constant(value):
        raise ValueError("non-JSON numeric constant " + value)

    def left_operand(value):
        form, declared, is_null = expression_form(value), None, False
        if form == "TypeCast":
            declared, argument = cast(value)
            if declared != "jsonb":
                raise ValueError("source-free document needs an explicit JSONB cast")
            document = literal(argument)
            is_null = document is None
            if not is_null:
                # A finite malformed-input screen, not PostgreSQL conversion semantics.
                json.loads(document, parse_constant=invalid_json_constant)
        elif form == "A_Expr":
            node = value[form]
            if (node.get("kind") != "AEXPR_OP"
                    or node.get("name") != [{"String": {"sval": "->"}}]
                    or expression_form(node.get("lexpr")) != "ColumnRef"):
                raise ValueError("nested document expression is outside this population")
            literal(node.get("rexpr"))
        elif form != "ColumnRef":
            raise ValueError("document operand is outside this population")
        return form, declared, is_null

    def right_operand(value, operator):
        form, declared = expression_form(value), None
        argument = value
        if form == "TypeCast":
            declared, argument = cast(value)
            if declared != ("text" if operator == "?" else "text[]"):
                raise ValueError("wrong explicit existence key type")
        if expression_form(argument) == "A_ArrayExpr":
            if operator == "?" or form != "A_ArrayExpr":
                raise ValueError("array key expression is outside this population")
            elements = argument["A_ArrayExpr"].get("elements", [])
            if not elements:
                raise ValueError("untyped empty array is outside this population")
            for element in elements:
                literal(element)
        else:
            text = literal(argument)
            if operator != "?" and (declared != "text[]" or text != "{}"):
                raise ValueError("only explicit empty text-array literals are selected")
        return form, declared

    def walk(value):
        if isinstance(value, list):
            for child in value:
                walk(child)
        elif isinstance(value, dict):
            for kind, node in value.items():
                if not isinstance(node, dict):
                    walk(node)
                    continue
                if kind in {"SubLink", "RowExpr", "RangeSubselect", "RangeFunction",
                            "A_Indirection", "A_Indices", "WindowDef", "CollateClause"}:
                    raise ValueError("later expression dependency is outside this population")
                if kind in {"ColumnRef", "ParamRef"} and source_free:
                    raise ValueError("source-free existence has no columns or parameters")
                if kind == "FuncCall":
                    if (source_free or node.get("funcname") != [{"String": {"sval": "count"}}]
                            or node.get("agg_star") is not True
                            or any(node.get(key) for key in ("args", "over", "agg_order", "agg_filter"))):
                        raise ValueError("call is outside this existence population")
                if kind == "TypeCast":
                    cast({"TypeCast": node})
                if kind == "A_Expr":
                    names = [part.get("String", {}).get("sval") for part in node.get("name", [])]
                    if len(names) != 1:
                        raise ValueError("qualified operators are outside this population")
                    operator = names[0]
                    if operator in OPERATORS:
                        if node.get("kind") != "AEXPR_OP":
                            raise ValueError("existence expression is not an ordinary binary operator")
                        location = node.get("location")
                        if type(location) is not int or location < 0:
                            raise ValueError("existence operator has no source position")
                        try:
                            start = len(sql.encode()[:location].decode())
                        except UnicodeDecodeError as error:
                            raise ValueError("existence position is not a UTF-8 boundary") from error
                        end = start + len(operator)
                        operator_chars = "+-*/<>=~!@#%^&|`?"
                        if (code[start:end] != operator
                                or start > 0 and code[start - 1] in operator_chars
                                or end < len(code) and code[end] in operator_chars):
                            raise ValueError("existence source spelling disagrees with raw AST")
                        left_form, left_cast, left_null = left_operand(node.get("lexpr"))
                        right_form, right_cast = right_operand(node.get("rexpr"), operator)
                        entries.append({"operator": operator, "left_form": left_form,
                                        "left_cast": left_cast, "left_literal_null": left_null,
                                        "right_form": right_form, "right_cast": right_cast})
                    elif (source_free or operator not in {"=", "->"}
                          or node.get("kind") not in {"AEXPR_OP", "AEXPR_OP_ANY"}):
                        raise ValueError("another operator is outside this existence population")
                walk(node)

    walk(parsed)
    if source_free:
        # The selected empty-catalog population projects only these predicates,
        # optionally under NOT. This is syntax observation, not validity typing.
        for target in query.get("targetList", []):
            value = target.get("ResTarget", {}).get("val", {})
            if "BoolExpr" in value:
                node = value["BoolExpr"]
                if node.get("boolop") != "NOT_EXPR" or len(node.get("args", [])) != 1:
                    raise ValueError("source projection has an unsupported Boolean wrapper")
                value = node["args"][0]
            node = value.get("A_Expr", {})
            if node.get("name") not in [[{"String": {"sval": operator}}] for operator in OPERATORS]:
                raise ValueError("source-free projection must be an existence predicate")
    result = {"source_free": source_free, "json_existence": entries}
    validate_json_existence(result)
    return result
