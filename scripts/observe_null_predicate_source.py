"""Finite raw-syntax observations of DISTINCT FROM and new NULL-predicate forms."""
from __future__ import annotations

import re

from extract_extended_type_corpus import sql_code

FACTORS = {"distinct_from", "null_predicates"}


def spelling(sql, location, pattern):
    if type(location) is not int or location < 0:
        raise ValueError("predicate has no exact source byte location")
    try:
        offset = len(sql.encode()[:location].decode())
    except UnicodeDecodeError as exc:
        raise ValueError("predicate byte location splits UTF-8") from exc
    match = re.match(pattern, sql_code(sql)[offset:], re.I)
    if match is None:
        raise ValueError("predicate spelling differs from its source position")
    return re.sub(r"\s+", " ", match[0]).lower()


def validate_null_predicates(observation, factor, sql=None):
    entries = observation.get(factor)
    if (factor not in FACTORS or type(observation.get("source_free")) is not bool
            or not isinstance(entries, list) or not entries):
        raise ValueError("new NULL predicate factor is absent")
    locations = []
    for entry in entries:
        common = {"form", "byte_location"}
        if factor == "distinct_from":
            if (set(entry) != common | {"left_form", "right_form"}
                    or entry["form"] not in {"is distinct from", "is not distinct from"}
                    or entry["left_form"] not in {"A_Const", "ColumnRef", "TypeCast"}
                    or entry["right_form"] not in {"A_Const", "ColumnRef", "TypeCast", "A_Expr"}):
                raise ValueError("invalid DISTINCT FROM source observation")
            pattern = r"IS\s+(?:NOT\s+)?DISTINCT\s+FROM\b"
        else:
            if (set(entry) != common | {"argument_form", "row_arity", "nested_row"}
                    or entry["form"] not in {"isnull", "notnull", "is null", "is not null"}
                    or entry["argument_form"] not in {"A_Const", "ColumnRef", "NullTest", "RowExpr", "A_Expr"}
                    or type(entry["nested_row"]) is not bool):
                raise ValueError("invalid NULL-predicate source observation")
            row = entry["argument_form"] == "RowExpr"
            if (row and (type(entry["row_arity"]) is not int or entry["row_arity"] < 0)
                    or not row and (entry["row_arity"] is not None or entry["nested_row"])
                    or not row and entry["form"] not in {"isnull", "notnull"}):
                raise ValueError("ordinary scalar IS NULL is not a new factor witness")
            pattern = r"(?:ISNULL|NOTNULL|IS\s+(?:NOT\s+)?NULL)\b"
        location = entry["byte_location"]
        if type(location) is not int or location < 0:
            raise ValueError("invalid source predicate location")
        if sql is not None and spelling(sql, location, pattern) != entry["form"]:
            raise ValueError("source predicate metadata was changed")
        locations.append(location)
    if len(set(locations)) != len(locations):
        raise ValueError("duplicate predicate location")


def observe_null_predicates(parsed, sql, factor):
    if factor not in FACTORS or set(parsed) != {"SelectStmt"}:
        raise ValueError("NULL-predicate source must be one SELECT")
    entries, source_free = [], True

    def nested_row(value):
        if isinstance(value, list):
            return any(nested_row(x) for x in value)
        if isinstance(value, dict):
            return "RowExpr" in value or any(nested_row(x) for x in value.values())
        return False

    def walk(value):
        nonlocal source_free
        if isinstance(value, list):
            for child in value:
                walk(child)
        elif isinstance(value, dict):
            for kind, node in value.items():
                if kind in {"RangeVar", "ColumnRef", "ParamRef"}:
                    source_free = False
                if kind in {"SubLink", "RangeFunction", "WindowDef", "CollateClause", "NamedArgExpr", "FuncCall",
                            "A_ArrayExpr", "A_Indirection", "InsertStmt", "UpdateStmt", "DeleteStmt"}:
                    raise ValueError("unselected dependency in the NULL source population")
                if kind == "SelectStmt" and (node.get("withClause") or node.get("valuesLists")):
                    raise ValueError("unselected CTE/VALUES query source")
                if kind == "A_Expr" and node.get("kind") in {"AEXPR_DISTINCT", "AEXPR_NOT_DISTINCT"}:
                    if factor != "distinct_from":
                        raise ValueError("other new factor in NULL-predicate population")
                    form = spelling(sql, node.get("location"), r"IS\s+(?:NOT\s+)?DISTINCT\s+FROM\b")
                    expected = "is distinct from" if node["kind"] == "AEXPR_DISTINCT" else "is not distinct from"
                    if form != expected:
                        raise ValueError("DISTINCT negation disagrees with source")
                    entries.append({"form": form, "byte_location": node["location"],
                                    "left_form": next(iter(node["lexpr"])), "right_form": next(iter(node["rexpr"]))})
                if kind == "NullTest":
                    form = spelling(sql, node.get("location"), r"(?:ISNULL|NOTNULL|IS\s+(?:NOT\s+)?NULL)\b")
                    if (form in {"notnull", "is not null"}) != (node.get("nulltesttype") == "IS_NOT_NULL"):
                        raise ValueError("NULL-test negation disagrees with source")
                    arg = node["arg"]
                    if factor == "null_predicates" and (form in {"isnull", "notnull"} or "RowExpr" in arg):
                        fields = arg.get("RowExpr", {}).get("args", [])
                        entries.append({"form": form, "byte_location": node["location"],
                                        "argument_form": next(iter(arg)),
                                        "row_arity": len(fields) if "RowExpr" in arg else None,
                                        "nested_row": nested_row(fields)})
                walk(node)
    walk(parsed)
    result = {"source_free": source_free, factor: entries}
    validate_null_predicates(result, factor, sql)
    return result
