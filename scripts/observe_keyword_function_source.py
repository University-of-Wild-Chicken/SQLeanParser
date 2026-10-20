"""Finite source observations of unquoted LEFT/RIGHT ordinary call heads."""
from __future__ import annotations

from observe_named_argument_source import identifier_at

FUNCTIONS = {"left", "right"}
ARGUMENT_FORMS = {"A_Const", "TypeCast", "A_Expr", "ColumnRef", "FuncCall"}


def validate_keyword_functions(observation: dict, sql: str | None = None) -> None:
    if type(observation.get("source_free")) is not bool:
        raise ValueError("keyword-call source-free observation must be Boolean")
    calls = observation.get("keyword_functions")
    if not isinstance(calls, list) or not calls:
        raise ValueError("keyword-function factor is absent")
    locations = []
    for call in calls:
        if (not isinstance(call, dict)
                or set(call) != {"function", "byte_location", "argument_forms", "literal_nulls", "explicit_casts"}
                or call["function"] not in FUNCTIONS
                or type(call["byte_location"]) is not int or call["byte_location"] < 0
                or not isinstance(call["argument_forms"], list) or len(call["argument_forms"]) != 2
                or not all(form in ARGUMENT_FORMS for form in call["argument_forms"])
                or not isinstance(call["literal_nulls"], list) or len(call["literal_nulls"]) != 2
                or any(type(flag) is not bool for flag in call["literal_nulls"])
                or not isinstance(call["explicit_casts"], list) or len(call["explicit_casts"]) != 2
                or any(cast not in {None, "int4"} for cast in call["explicit_casts"])):
            raise ValueError("invalid keyword-call source metadata")
        for form, null, cast in zip(call["argument_forms"], call["literal_nulls"], call["explicit_casts"]):
            if null and form != "A_Const" or (cast is not None) != (form == "TypeCast"):
                raise ValueError("keyword-call immediate operand metadata disagrees")
        if sql is not None:
            identifier_at(sql, call["function"], call["byte_location"], r"\(")
        locations.append(call["byte_location"])
    if len(set(locations)) != len(locations):
        raise ValueError("duplicate keyword-call source location")


def observe_keyword_functions(parsed: dict, sql: str) -> dict:
    if set(parsed) != {"SelectStmt"}:
        raise ValueError("keyword-call source must be one whole SELECT")
    calls, source_free = [], True

    def cast_name(argument):
        cast = argument.get("TypeCast")
        if cast is None:
            return None
        typename = cast["typeName"]
        names = [part["String"]["sval"] for part in typename["names"]]
        if (names not in [["int4"], ["pg_catalog", "int4"]]
                or typename.get("typmods") or typename.get("arrayBounds")):
            raise ValueError("keyword-call source has an unselected immediate cast")
        return "int4"

    def walk(value):
        nonlocal source_free
        if isinstance(value, list):
            for child in value:
                walk(child)
        elif isinstance(value, dict):
            for kind, node in value.items():
                if kind in {"RangeVar", "ColumnRef", "ParamRef"}:
                    source_free = False
                if kind in {"RangeFunction", "WindowDef", "SubLink", "NamedArgExpr",
                            "CollateClause", "RowExpr", "A_Indirection",
                            "InsertStmt", "UpdateStmt", "DeleteStmt", "MergeStmt"}:
                    raise ValueError("later dependency is outside this keyword-call source population")
                if kind == "FuncCall":
                    names = [part["String"]["sval"] for part in node.get("funcname", [])]
                    if names and names[-1] in FUNCTIONS:
                        args = node.get("args", [])
                        if len(names) != 1 or len(args) != 2 or any(node.get(key) for key in (
                                "agg_order", "agg_filter", "agg_star", "agg_distinct", "over",
                                "func_variadic", "agg_within_group")):
                            raise ValueError("keyword-call source requires an ordinary unqualified binary call")
                        calls.append({
                            "function": names[0], "byte_location": node.get("location"),
                            "argument_forms": [next(iter(arg)) for arg in args],
                            "literal_nulls": [arg.get("A_Const", {}).get("isnull", False) for arg in args],
                            "explicit_casts": [cast_name(arg) for arg in args],
                        })
                walk(node)

    walk(parsed)
    if source_free:
        query = parsed["SelectStmt"]
        if any(query.get(key) for key in ("fromClause", "withClause", "larg", "rarg", "whereClause",
                                         "groupClause", "havingClause", "sortClause", "limitCount",
                                         "limitOffset", "lockingClause", "distinctClause")):
            raise ValueError("closed keyword-call sources have only direct projections")
        targets = query.get("targetList", [])
        for target in targets:
            item = target.get("ResTarget", {})
            call = item.get("val", {}).get("FuncCall", {})
            if (item.get("name") or [p["String"]["sval"] for p in call.get("funcname", [])]
                    not in [["left"], ["right"]]):
                raise ValueError("closed keyword-call source has a different projection form")
            for argument in call.get("args", []):
                def literal_operand(node):
                    if set(node) == {"A_Const"}:
                        return True
                    if set(node) == {"TypeCast"}:
                        return literal_operand(node["TypeCast"]["arg"])
                    if set(node) == {"A_Expr"}:
                        expr = node["A_Expr"]
                        return (expr.get("kind") == "AEXPR_OP" and not expr.get("lexpr")
                                and [n["String"]["sval"] for n in expr.get("name", [])] in [["-"], ["+"]]
                                and literal_operand(expr.get("rexpr", {})))
                    return False
                if not literal_operand(argument):
                    raise ValueError("closed keyword-call inputs are literals/explicit casts only")
    result = {"source_free": source_free, "keyword_functions": calls}
    validate_keyword_functions(result, sql)
    return result
