#!/usr/bin/env python3
"""Reproduce unchanged public SELECT corpora for incremental syntax factors.

Each closed factor population contains 50 source statements. Source programs,
templates, and SQL are never executed. --oracle requires pinned pglast 7.21.
"""
from __future__ import annotations

import argparse
from collections import Counter
import json
from pathlib import Path
import re

from audit_postgresql_corpus import features
from extract_application_corpus import first_sql_text
from extract_extended_type_corpus import (
    NEW_FAMILIES, OLD_FAMILIES, parameter_slots, select_sql, sql_code,
)
from extract_pagination_corpus import checked_file, comparison_key, sha256
from extract_statement_corpus import selected_sql, statement_spans
from extract_tcl_sql import selected_tcl_sql
from extract_sqllogic_sql import selected_sqllogic_sql

ROOT = Path(__file__).resolve().parents[1]
POPULATIONS = {
    "functions": {"hatchet": 20, "sqlc": 10, "postgres": 20},
    "conditional": {"hatchet": 11, "sqlc": 13, "postgres": 26},
    "locking": {"temporal": 15, "hatchet": 8, "sqlc": 2, "postgres": 25},
    "join_contract": {"hatchet": 1, "sqlc": 19, "postgres": 30},
    "using_contract": {"postgres": 16, "sqlc": 3, "sqlite": 31},
    "natural_contract": {"postgres": 6, "sqlite": 44},
    "derived_contract": {"postgres": 47, "sqlc": 3},
    "array_types": {"postgres": 42, "hatchet": 7, "sqlc": 1},
    "array_constructors": {"postgres": 49, "sqlc": 1},
    "array_quantified": {"hatchet": 29, "postgres": 18, "sqlc": 3},
    "array_subscripts": {"postgres": 24, "duckdb": 26},
    "row_comparisons": {"hatchet": 16, "postgres": 8, "temporal": 6, "sqlite": 20},
    "concatenation": {"hatchet": 1, "postgres": 49},
    "ilike": {"hatchet": 1, "river": 2, "postgres": 7, "duckdb": 40},
    "regex": {"postgres": 50},
    "json_extraction": {"postgres": 50},
}
CONDITIONAL_FORMS = {"searched-case", "simple-case", "coalesce", "nullif", "greatest", "least"}
AGGREGATES = {"count", "sum", "avg", "min", "max"}
LOCK_STRENGTHS = {"update", "no-key-update", "share", "key-share"}
LOCK_POLICIES = {"default", "nowait", "skip-locked"}
JOIN_KINDS = {"cross", "inner", "left", "right", "full"}
MERGED_FACTORS = {"using_contract": "using", "natural_contract": "natural"}
JOIN_FACTORS = {"join_contract", *MERGED_FACTORS}
ARRAY_ELEMENT_FAMILIES = {"int4", "int8", "text", "float8", "interval", "timestamptz", "uuid"}
ARRAY_FACTORS = {"array_types", "array_constructors", "array_quantified", "array_subscripts"}
COMPARISON_OPERATORS = {"=", "<>", "<", "<=", ">", ">="}


def validate_join_tree(tree: dict, *, root: bool = True, allow_merged: bool = False) -> set[str]:
    """Check the closed structural observation, retaining left/right nesting."""
    if not isinstance(tree, dict):
        raise ValueError("invalid base-table join observation")
    if tree.get("kind") == "table":
        if (root or set(tree) != {"kind", "name", "alias"}
                or not isinstance(tree["name"], str) or not tree["name"]
                or (tree["alias"] is not None
                    and (not isinstance(tree["alias"], str) or not tree["alias"]))):
            raise ValueError("invalid base-table join observation")
        return set()
    condition = tree.get("condition")
    keys = {"kind", "condition", "left", "right"}
    if allow_merged and condition == "using":
        keys.add("columns")
    if (set(tree) != keys
            or not isinstance(tree["kind"], str)
            or tree["kind"] not in JOIN_KINDS
            or not isinstance(condition, str)
            or (tree["kind"] == "cross" and condition != "none")
            or (tree["kind"] != "cross"
                and condition not in ({"on", "using", "natural"} if allow_merged else {"on"}))):
        raise ValueError("invalid base-table join observation")
    if condition == "using":
        columns = tree["columns"]
        if (not isinstance(columns, list) or not columns
                or not all(isinstance(column, str) and column for column in columns)
                or len(set(columns)) != len(columns)):
            raise ValueError("invalid ordered USING columns")
    return ({tree["kind"]} | validate_join_tree(tree["left"], root=False, allow_merged=allow_merged)
            | validate_join_tree(tree["right"], root=False, allow_merged=allow_merged))


def merged_join_kinds(tree: dict, condition: str) -> set[str]:
    if tree["kind"] == "table":
        return set()
    return (({tree["kind"]} if tree["condition"] == condition else set())
            | merged_join_kinds(tree["left"], condition)
            | merged_join_kinds(tree["right"], condition))


def observe_derived_queries(parsed: dict) -> list[dict]:
    """Conservative finite-source screen, not catalog-dependent name resolution."""
    result = []

    def query(value, depth):
        if (set(value) != {"SelectStmt"} or not isinstance(value["SelectStmt"], dict)):
            raise ValueError("derived source must be a SELECT")
        select = value["SelectStmt"]
        if any(select.get(key) for key in (
                "withClause", "distinctClause", "groupClause", "havingClause", "larg",
                "rarg", "lockingClause", "valuesLists")):
            raise ValueError("derived population excludes CTE/grouping/set/locking/value forms")

        def source(node):
            if "RangeVar" in node:
                table = node["RangeVar"]
                alias = table.get("alias", {})
                if (table.get("schemaname") or table.get("catalogname")
                        or table.get("inh") is False or alias.get("colnames")):
                    raise ValueError("qualified/ONLY/column-aliased base source is outside this population")
                return [alias.get("aliasname", table["relname"])]
            if "RangeSubselect" in node:
                derived = node["RangeSubselect"]
                alias = derived.get("alias")
                if derived.get("lateral") or not alias or not alias.get("aliasname"):
                    raise ValueError("derived population requires named non-LATERAL sources")
                result.append({"alias": alias["aliasname"],
                               "columns": [column["String"]["sval"] for column in alias.get("colnames", [])],
                               "query_depth": depth + 1, "lateral": False})
                query(derived["subquery"], depth + 1)
                return [alias["aliasname"]]
            if "JoinExpr" in node:
                join = node["JoinExpr"]
                if join.get("alias") or join.get("join_using_alias"):
                    raise ValueError("aliased join node is outside this derived population")
                return source(join["larg"]) + source(join["rarg"])
            raise ValueError("unsupported source in derived population")

        names = [name for item in select.get("fromClause", []) for name in source(item)]

        def own_references(node):
            if isinstance(node, list):
                for item in node:
                    own_references(item)
            elif isinstance(node, dict):
                if "SelectStmt" in node:
                    return  # Each derived query was screened with its own namespace.
                if "SubLink" in node or "FuncCall" in node:
                    raise ValueError("expression subquery/function is outside the derived population")
                if "ColumnRef" in node:
                    fields = node["ColumnRef"]["fields"]
                    first = fields[0].get("String", {}).get("sval")
                    if len(fields) > 2 or (len(fields) == 2 and first not in names):
                        raise ValueError("qualified column is outside its own derived-query scope")
                    if len(fields) == 1 and first is not None and not names:
                        raise ValueError("source-free derived query contains a column reference")
                    return
                for item in node.values():
                    own_references(item)

        own_references(select)

    query(parsed, 0)
    if not result:
        raise ValueError("derived source factor is absent")
    return result


def validate_derived_sources(sources: list[dict]) -> None:
    if not isinstance(sources, list) or not sources:
        raise ValueError("derived source factor is absent")
    for entry in sources:
        if (not isinstance(entry, dict)
                or set(entry) != {"alias", "columns", "query_depth", "lateral"}
                or not isinstance(entry["alias"], str) or not entry["alias"]
                or not isinstance(entry["columns"], list)
                or not all(isinstance(column, str) and column for column in entry["columns"])
                or len(set(entry["columns"])) != len(entry["columns"])
                or type(entry["query_depth"]) is not int or entry["query_depth"] < 1
                or entry["lateral"] is not False):
            raise ValueError("invalid non-LATERAL derived source observation")


def validate_array_types(types: list[dict]) -> None:
    if not isinstance(types, list) or not types:
        raise ValueError("array type factor is absent")
    for entry in types:
        if (not isinstance(entry, dict)
                or set(entry) != {"element_type", "modifiers", "bounds"}
                or not isinstance(entry["element_type"], str)
                or entry["element_type"] not in NEW_FAMILIES | OLD_FAMILIES
                or not isinstance(entry["modifiers"], list)
                or not all(type(value) is int and value >= 0 for value in entry["modifiers"])
                or not isinstance(entry["bounds"], list) or not entry["bounds"]
                or not all(value is None or (type(value) is int and value >= 0)
                           for value in entry["bounds"])):
            raise ValueError("invalid array type observation")


def observe_array_types(parsed: dict) -> list[dict]:
    """Observe suffix declarations without admitting other array-expression forms.

    Bounds describe source syntax, not a runtime rank/size constraint. This is
    a finite source-population screen, not PostgreSQL's semantic analyzer.
    """
    if not isinstance(parsed, dict) or set(parsed) != {"SelectStmt"}:
        raise ValueError("array type source must be a SELECT")
    result = []

    def walk(value):
        if isinstance(value, list):
            for child in value:
                walk(child)
        elif isinstance(value, dict):
            for kind, node in value.items():
                if not isinstance(node, dict):
                    walk(node)
                    continue
                if kind in {"A_ArrayExpr", "A_Indices", "A_Indirection", "RowExpr"}:
                    raise ValueError("array constructor/subscript/row expression belongs to a later factor")
                if kind == "A_Expr" and node.get("kind") in {"AEXPR_OP_ANY", "AEXPR_OP_ALL"}:
                    raise ValueError("quantified comparison belongs to a later factor")
                if kind == "SubLink" and (
                        node.get("subLinkType") == "ARRAY_SUBLINK"
                        or node.get("subLinkType") in {"ANY_SUBLINK", "ALL_SUBLINK"}):
                    raise ValueError("array/quantified subquery belongs to a later factor")
                if kind in {"TypeName", "typeName"} and node.get("arrayBounds"):
                    names = [part.get("String", {}).get("sval") for part in node.get("names", [])]
                    if (not names or names[-1] not in NEW_FAMILIES | OLD_FAMILIES
                            or len(names) > 2 or (len(names) == 2 and names[0] != "pg_catalog")):
                        raise ValueError("array element must be a supported built-in type")
                    modifiers = []
                    for modifier in node.get("typmods", []):
                        literal = modifier.get("A_Const", {}).get("ival")
                        if not isinstance(literal, dict):
                            raise ValueError("non-integer array element type modifier")
                        modifiers.append(literal.get("ival", 0))
                    bounds = []
                    for bound in node["arrayBounds"]:
                        integer = bound.get("Integer")
                        if not isinstance(integer, dict):
                            raise ValueError("non-integer array type bound")
                        number = integer.get("ival", 0)
                        if type(number) is not int:
                            raise ValueError("non-integer array type bound")
                        bounds.append(None if number == -1 else number)
                    result.append({"element_type": names[-1], "modifiers": modifiers, "bounds": bounds})
                walk(node)

    walk(parsed)
    validate_array_types(result)
    return result


def validate_array_constructors(constructors: list[dict]) -> None:
    if not isinstance(constructors, list) or not constructors:
        raise ValueError("array constructor factor is absent")
    for entry in constructors:
        if (not isinstance(entry, dict)
                or set(entry) != {"depth", "length", "array_cast_context"}
                or type(entry["depth"]) is not int or entry["depth"] < 1
                or type(entry["length"]) is not int or entry["length"] < 0
                or type(entry["array_cast_context"]) is not bool
                or (entry["length"] == 0 and not entry["array_cast_context"])):
            raise ValueError("invalid array constructor observation")


def observe_array_constructors(parsed: dict) -> list[dict]:
    """Observe the closed constructor population, retaining expression nesting.

    Depth counts nested constructor expressions, not a PostgreSQL type rank.
    Cast context is inherited only through constructors, never through calls.
    No element type inference, shape equality, or function validity is claimed.
    """
    if not isinstance(parsed, dict) or set(parsed) != {"SelectStmt"}:
        raise ValueError("array constructor source must be a SELECT")
    result = []

    def walk(value, depth=0, array_cast=False):
        if isinstance(value, list):
            for child in value:
                walk(child, depth, array_cast)
        elif isinstance(value, dict):
            for kind, node in value.items():
                if not isinstance(node, dict):
                    walk(node, depth)
                    continue
                if kind == "SelectStmt" and any(node.get(field) for field in (
                        "fromClause", "withClause", "groupClause", "havingClause",
                        "larg", "rarg", "valuesLists", "lockingClause")):
                    raise ValueError("constructor population requires source-free SELECTs")
                if kind in {"A_Indices", "A_Indirection", "RowExpr", "SubLink"}:
                    raise ValueError("subscript/row/subquery belongs to a later constructor factor")
                if kind == "A_Expr" and node.get("kind") in {"AEXPR_OP_ANY", "AEXPR_OP_ALL"}:
                    raise ValueError("quantified comparison belongs to a later constructor factor")
                if kind == "TypeCast":
                    target = node.get("typeName", {})
                    walk(node.get("arg"), depth, bool(target.get("arrayBounds")))
                    walk(target, depth)
                elif kind == "A_ArrayExpr":
                    elements = node.get("elements", [])
                    if not isinstance(elements, list):
                        raise ValueError("array constructor elements must be a list")
                    result.append({"depth": depth + 1, "length": len(elements),
                                   "array_cast_context": array_cast})
                    walk(elements, depth + 1, array_cast)
                else:
                    walk(node, depth)

    walk(parsed)
    validate_array_constructors(result)
    return result


def validate_array_quantified(comparisons: list[dict]) -> None:
    if not isinstance(comparisons, list) or not comparisons:
        raise ValueError("array quantified factor is absent")
    for entry in comparisons:
        if (not isinstance(entry, dict)
                or set(entry) != {"operator", "source_operator", "quantifier", "right_form"}
                or not isinstance(entry["operator"], str)
                or entry["operator"] not in COMPARISON_OPERATORS
                or not isinstance(entry["source_operator"], str)
                or entry["source_operator"].replace("!=", "<>") != entry["operator"]
                or not isinstance(entry["quantifier"], str)
                or entry["quantifier"] not in {"any", "some", "all"}
                or not isinstance(entry["right_form"], str)
                or entry["right_form"] not in {"TypeCast", "A_Const", "ParamRef", "A_ArrayExpr"}):
            raise ValueError("invalid quantified-array observation")


def observe_array_quantified(parsed: dict, sql: str) -> list[dict]:
    """Observe source spelling as well as PostgreSQL's normalized ANY/ALL node.

    PostgreSQL JSON locations are UTF-8 byte offsets. The comment/string mask
    retains Python character positions, so convert offsets before matching.
    This screen does not resolve operator overloads, names, or application types.
    """
    if not isinstance(parsed, dict) or set(parsed) != {"SelectStmt"}:
        raise ValueError("quantified-array source must be a SELECT")
    result, masked, encoded = [], sql_code(sql), sql.encode("utf-8")

    def walk(value):
        if isinstance(value, list):
            for child in value:
                walk(child)
        elif isinstance(value, dict):
            for kind, node in value.items():
                if not isinstance(node, dict):
                    walk(node)
                    continue
                if kind in {"A_Indices", "A_Indirection", "RowExpr", "SubLink"}:
                    raise ValueError("subscript/row/subquery is outside the quantified-array population")
                if kind == "A_Expr" and node.get("kind") in {"AEXPR_OP_ANY", "AEXPR_OP_ALL"}:
                    names = [part.get("String", {}).get("sval") for part in node.get("name", [])]
                    if len(names) != 1 or names[0] not in COMPARISON_OPERATORS:
                        raise ValueError("custom quantified operator is outside this population")
                    location = node.get("location")
                    if type(location) is not int or not 0 <= location < len(encoded):
                        raise ValueError("invalid quantified operator byte location")
                    try:
                        offset = len(encoded[:location].decode("utf-8"))
                    except UnicodeDecodeError as error:
                        raise ValueError("invalid quantified operator byte location") from error
                    match = re.match(r"(<>|!=|<=|>=|=|<|>)\s*(ANY|SOME|ALL)\s*\(",
                                     masked[offset:], re.I)
                    if (match is None or match[1].replace("!=", "<>") != names[0]
                            or ((match[2].lower() == "all")
                                != (node["kind"] == "AEXPR_OP_ALL"))):
                        raise ValueError("quantified operator source spelling disagrees with raw AST")
                    right = node.get("rexpr", {})
                    if not isinstance(right, dict) or len(right) != 1:
                        raise ValueError("invalid quantified right operand observation")
                    result.append({"operator": names[0], "source_operator": match[1],
                                   "quantifier": match[2].lower(), "right_form": next(iter(right))})
                walk(node)

    walk(parsed)
    validate_array_quantified(result)
    return result


def validate_array_subscripts(groups: list[dict]) -> None:
    if not isinstance(groups, list) or not groups:
        raise ValueError("array subscript factor is absent")
    for group in groups:
        if (not isinstance(group, dict) or set(group) != {"depth", "dimensions"}
                or type(group["depth"]) is not int or group["depth"] < 1
                or not isinstance(group["dimensions"], list)
                or not 1 <= len(group["dimensions"]) <= 6):
            raise ValueError("invalid array subscript group")
        for dimension in group["dimensions"]:
            if (not isinstance(dimension, dict)
                    or set(dimension) != {"slice", "lower", "upper"}
                    or not all(type(value) is bool for value in dimension.values())
                    or (not dimension["slice"] and (dimension["lower"] or not dimension["upper"]))):
                raise ValueError("invalid array subscript bound observation")


def observe_array_subscripts(parsed: dict) -> list[dict]:
    """Retain index groups and optional slice bounds, without catalog inference.

    A chained group a[1][2] differs from the nested grouping (a[1])[2].
    Domain-backed source columns may contain nested arrays; this syntax screen
    neither assigns their types nor proves that an access succeeds.
    """
    if not isinstance(parsed, dict) or set(parsed) != {"SelectStmt"}:
        raise ValueError("array subscript source must be a SELECT")
    result = []

    def walk(value, depth=0):
        if isinstance(value, list):
            for child in value:
                walk(child, depth)
        elif isinstance(value, dict):
            for kind, node in value.items():
                if not isinstance(node, dict):
                    walk(node, depth)
                    continue
                if kind == "RowExpr" or (kind == "SubLink"
                        and node.get("subLinkType") != "EXPR_SUBLINK"):
                    raise ValueError("row/quantified/array subquery is outside this subscript population")
                if kind == "A_Indirection":
                    indices = node.get("indirection", [])
                    if not isinstance(indices, list) or not indices:
                        raise ValueError("empty array subscript group")
                    dimensions = []
                    for index in indices:
                        if not isinstance(index, dict) or set(index) != {"A_Indices"}:
                            raise ValueError("record-field indirection is outside this subscript population")
                        item = index["A_Indices"]
                        if not isinstance(item, dict):
                            raise ValueError("invalid array subscript bounds")
                        dimensions.append({"slice": item.get("is_slice", False),
                                           "lower": bool(item.get("lidx")),
                                           "upper": bool(item.get("uidx"))})
                    base = node.get("arg", {})
                    if ("FuncCall" in base
                            or ("TypeCast" in base and not base["TypeCast"].get("typeName", {}).get("arrayBounds"))):
                        raise ValueError("function/scalar-cast base is outside this subscript population")
                    result.append({"depth": depth + 1, "dimensions": dimensions})
                    walk(node, depth + 1)
                else:
                    walk(node, depth)

    walk(parsed)
    validate_array_subscripts(result)
    return result


def validate_row_comparisons(comparisons: list[dict]) -> None:
    if not isinstance(comparisons, list) or not comparisons:
        raise ValueError("row comparison factor is absent")
    for entry in comparisons:
        if (not isinstance(entry, dict)
                or set(entry) != {"operator", "arity", "left_form", "right_form"}
                or not isinstance(entry["operator"], str)
                or entry["operator"] not in COMPARISON_OPERATORS
                or type(entry["arity"]) is not int or entry["arity"] < 1
                or entry["left_form"] not in ("explicit", "implicit")
                or entry["right_form"] not in ("explicit", "implicit")):
            raise ValueError("invalid row comparison observation")


def observe_row_comparisons(parsed: dict) -> list[dict]:
    """Observe direct constructor comparisons, excluding other composite forms.

    Equal nonzero arities describe this finite source population. The observer
    does not infer field types, comparison operators, or runtime NULL behavior.
    Every row constructor must be a direct operand of an observed comparison.
    """
    if not isinstance(parsed, dict) or set(parsed) != {"SelectStmt"}:
        raise ValueError("row comparison source must be a SELECT")
    result, rows, consumed = [], [], set()
    forms = {"COERCE_EXPLICIT_CALL": "explicit", "COERCE_IMPLICIT_CAST": "implicit"}

    def walk(value):
        if isinstance(value, list):
            for child in value:
                walk(child)
        elif isinstance(value, dict):
            for kind, node in value.items():
                if not isinstance(node, dict):
                    walk(node)
                    continue
                if kind == "RowExpr":
                    rows.append(node)
                if kind == "SubLink" and node.get("subLinkType") in {
                        "ANY_SUBLINK", "ALL_SUBLINK", "ARRAY_SUBLINK", "ROWCOMPARE_SUBLINK"}:
                    raise ValueError("row/array/quantified subquery is outside this comparison population")
                if kind == "A_Expr":
                    left, right = node.get("lexpr", {}).get("RowExpr"), node.get("rexpr", {}).get("RowExpr")
                    names = [part.get("String", {}).get("sval") for part in node.get("name", [])]
                    if (node.get("kind") == "AEXPR_OP" and len(names) == 1
                            and names[0] in COMPARISON_OPERATORS
                            and isinstance(left, dict) and isinstance(right, dict)):
                        args = (left.get("args", []), right.get("args", []))
                        if (not all(isinstance(items, list) and items for items in args)
                                or len(args[0]) != len(args[1])):
                            raise ValueError("source comparison rows must have equal nonzero arities")
                        if left.get("row_format") not in forms or right.get("row_format") not in forms:
                            raise ValueError("unknown row constructor spelling observation")
                        consumed.update((id(left), id(right)))
                        result.append({"operator": names[0], "arity": len(args[0]),
                                       "left_form": forms[left["row_format"]],
                                       "right_form": forms[right["row_format"]]})
                walk(node)

    walk(parsed)
    if any(id(row) not in consumed for row in rows):
        raise ValueError("standalone/nested/IN/custom-operator row form is outside this population")
    validate_row_comparisons(result)
    return result


CONCATENATION_OPERAND_FORMS = {"A_Const", "A_Expr", "TypeCast", "FuncCall", "ColumnRef"}
CONCATENATION_DECLARED_TYPES = {"text", "pg_catalog.bpchar", "pg_catalog.varchar", "jsonb", "bytea"}


def validate_concatenations(entries: list[dict]) -> None:
    """Validate syntax observations, without assigning an overload or result type."""
    if not isinstance(entries, list) or not entries:
        raise ValueError("concatenation factor is absent")
    for entry in entries:
        if not isinstance(entry, dict) or set(entry) != {"left", "right"}:
            raise ValueError("invalid concatenation observation")
        for side in ("left", "right"):
            operand = entry[side]
            if (not isinstance(operand, dict) or set(operand) != {"form", "declared_type"}
                    or not isinstance(operand["form"], str)
                    or operand["form"] not in CONCATENATION_OPERAND_FORMS):
                raise ValueError("invalid concatenation operand observation")
            declared = operand["declared_type"]
            if operand["form"] == "TypeCast":
                if not isinstance(declared, str) or declared not in CONCATENATION_DECLARED_TYPES:
                    raise ValueError("invalid immediate concatenation cast observation")
            elif declared is not None:
                raise ValueError("concatenation source cannot invent an operand type")


def observe_concatenations(parsed: dict) -> list[dict]:
    """Observe this finite text/JSONB/BYTEA source population.

    Immediate cast declarations are retained. Function results and column
    types remain unknown; this source screen is not operator resolution.
    """
    if not isinstance(parsed, dict) or set(parsed) != {"SelectStmt"}:
        raise ValueError("concatenation source must be a SELECT")
    result = []

    def operand(value):
        if not isinstance(value, dict) or len(value) != 1:
            raise ValueError("concatenation requires two expression operands")
        form = next(iter(value))
        declared = None
        if form == "TypeCast":
            type_name = value[form].get("typeName", {})
            if type_name.get("arrayBounds"):
                raise ValueError("array concatenation is outside this source population")
            declared = ".".join(part.get("String", {}).get("sval", "")
                                for part in type_name.get("names", []))
        return {"form": form, "declared_type": declared}

    def walk(value):
        if isinstance(value, list):
            for child in value:
                walk(child)
        elif isinstance(value, dict):
            for kind, node in value.items():
                if not isinstance(node, dict):
                    walk(node)
                    continue
                if kind in {"A_ArrayExpr", "A_Indices", "A_Indirection", "RowExpr"}:
                    raise ValueError("array/row form is outside this concatenation population")
                if kind in {"TypeName", "typeName"} and node.get("arrayBounds"):
                    raise ValueError("array concatenation is outside this source population")
                if kind == "SubLink" and node.get("subLinkType") in {
                        "ANY_SUBLINK", "ALL_SUBLINK", "ARRAY_SUBLINK", "ROWCOMPARE_SUBLINK"}:
                    raise ValueError("array/quantified subquery is outside this concatenation population")
                if kind == "A_Expr" and node.get("kind") == "AEXPR_OP":
                    names = [part.get("String", {}).get("sval") for part in node.get("name", [])]
                    if names == ["||"]:
                        result.append({"left": operand(node.get("lexpr")),
                                       "right": operand(node.get("rexpr"))})
                    elif len(names) != 1 or names[0] not in COMPARISON_OPERATORS | {"+", "-", "*", "/"}:
                        raise ValueError("another extended operator is outside this concatenation population")
                walk(node)

    walk(parsed)
    validate_concatenations(result)
    return result


PATTERN_OPERATORS = {"ilike": {"ILIKE", "NOT ILIKE"}, "regex": {"~", "~*", "!~", "!~*"}}
PATTERN_OPERAND_FORMS = {"A_Const", "ColumnRef", "TypeCast", "A_Expr", "FuncCall"}


def validate_pattern_matches(entries: list[dict], factor: str) -> None:
    if factor not in PATTERN_OPERATORS:
        raise ValueError("unknown pattern source factor")
    if not isinstance(entries, list) or not entries:
        raise ValueError("pattern source factor is absent")
    for entry in entries:
        if (not isinstance(entry, dict) or set(entry) != {"operator", "left_form", "right_form"}
                or not isinstance(entry["operator"], str)
                or entry["operator"] not in PATTERN_OPERATORS[factor]
                or any(not isinstance(entry[side], str) or entry[side] not in PATTERN_OPERAND_FORMS
                       for side in ("left_form", "right_form"))):
            raise ValueError("invalid pattern source observation")


def observe_pattern_matches(parsed: dict, factor: str) -> list[dict]:
    """Observe literal operator syntax, not collation, type, or pattern validity."""
    if factor not in PATTERN_OPERATORS:
        raise ValueError("unknown pattern source factor")
    if not isinstance(parsed, dict) or set(parsed) != {"SelectStmt"}:
        raise ValueError("pattern source must be a SELECT")
    result = []
    ilike_names = {"~~*": "ILIKE", "!~~*": "NOT ILIKE"}

    def form(operand):
        if not isinstance(operand, dict) or len(operand) != 1:
            raise ValueError("pattern match requires two expression operands")
        return next(iter(operand))

    def walk(value):
        if isinstance(value, list):
            for child in value:
                walk(child)
        elif isinstance(value, dict):
            for kind, node in value.items():
                if not isinstance(node, dict):
                    walk(node)
                    continue
                if kind in {"A_ArrayExpr", "A_Indices", "A_Indirection", "RowExpr"}:
                    raise ValueError("array access/constructor or row is outside this pattern population")
                if kind in {"TypeName", "typeName"} and node.get("arrayBounds") and factor != "ilike":
                    raise ValueError("array types are outside this regex population")
                if kind == "SubLink" and node.get("subLinkType") in {
                        "ANY_SUBLINK", "ALL_SUBLINK", "ARRAY_SUBLINK", "ROWCOMPARE_SUBLINK"}:
                    raise ValueError("array/quantified subquery is outside this pattern population")
                if kind == "FuncCall" and [
                        part.get("String", {}).get("sval") for part in node.get("funcname", [])
                ] == ["pg_catalog", "like_escape"]:
                    raise ValueError("explicit ESCAPE is outside this pattern population")
                if kind == "A_Expr":
                    names = [part.get("String", {}).get("sval") for part in node.get("name", [])]
                    expr_kind = node.get("kind")
                    operator = None
                    if factor == "ilike" and expr_kind == "AEXPR_ILIKE":
                        if len(names) != 1 or names[0] not in ilike_names:
                            raise ValueError("unknown ILIKE source spelling")
                        operator = ilike_names[names[0]]
                    elif expr_kind == "AEXPR_OP":
                        if factor == "regex" and len(names) == 1 and names[0] in PATTERN_OPERATORS[factor]:
                            operator = names[0]
                        elif len(names) != 1 or names[0] not in COMPARISON_OPERATORS | {"+", "-", "*", "/", "||"}:
                            raise ValueError("another extended operator is outside this pattern population")
                    if operator is not None:
                        result.append({"operator": operator, "left_form": form(node.get("lexpr")),
                                       "right_form": form(node.get("rexpr"))})
                walk(node)

    walk(parsed)
    validate_pattern_matches(result, factor)
    return result


JSON_EXTRACTION_OPERATORS = {"->", "->>", "#>", "#>>"}


def validate_json_extractions(entries: list[dict]) -> None:
    if not isinstance(entries, list) or not entries:
        raise ValueError("JSON extraction factor is absent")
    keys = {"operator", "left_form", "left_cast", "right_form", "right_cast"}
    for entry in entries:
        if (not isinstance(entry, dict) or set(entry) != keys
                or not isinstance(entry["operator"], str)
                or entry["operator"] not in JSON_EXTRACTION_OPERATORS
                or entry["left_form"] not in ("TypeCast", "A_Expr")
                or entry["right_form"] not in ("A_Const", "A_ArrayExpr", "TypeCast")):
            raise ValueError("invalid JSON extraction observation")
        for side, declared in (("left", ("pg_catalog.json", "jsonb")),
                               ("right", ("text", "pg_catalog.int4"))):
            if entry[side + "_form"] == "TypeCast":
                if entry[side + "_cast"] not in declared:
                    raise ValueError("unexpected explicit JSON extraction cast")
            elif entry[side + "_cast"] is not None:
                raise ValueError("JSON extraction observation cannot invent an operand type")


def observe_json_extractions(parsed: dict) -> list[dict]:
    """Observe the finite source-free JSON/JSONB extraction population.

    Explicit type names are source declarations. No output type, operator
    signature, path interpretation, or result value is inferred here.
    """
    if not isinstance(parsed, dict) or set(parsed) != {"SelectStmt"}:
        raise ValueError("JSON extraction source must be a SELECT")
    result = []

    def operand(value):
        if not isinstance(value, dict) or len(value) != 1:
            raise ValueError("JSON extraction requires two expression operands")
        form = next(iter(value))
        declared = None
        if form == "TypeCast":
            name = value[form].get("typeName", {})
            if name.get("arrayBounds"):
                raise ValueError("explicit array cast is outside this JSON source population")
            declared = ".".join(part.get("String", {}).get("sval", "") for part in name.get("names", []))
        return form, declared

    def invalid_constant(value):
        raise ValueError(f"non-JSON numeric constant {value}")

    def walk(value):
        if isinstance(value, list):
            for child in value:
                walk(child)
        elif isinstance(value, dict):
            for kind, node in value.items():
                if not isinstance(node, dict):
                    walk(node)
                    continue
                if kind in {"ColumnRef", "ParamRef", "FuncCall", "SubLink", "RowExpr",
                            "A_Indirection", "A_Indices"}:
                    raise ValueError("catalog/call/subquery/row/access dependency is outside this JSON population")
                if kind == "SelectStmt" and any(node.get(key) for key in (
                        "fromClause", "withClause", "larg", "rarg", "valuesLists")):
                    raise ValueError("JSON extraction population requires source-free SELECTs")
                if kind == "TypeCast":
                    name = ".".join(part.get("String", {}).get("sval", "")
                                    for part in node.get("typeName", {}).get("names", []))
                    if name in {"pg_catalog.json", "jsonb"}:
                        literal = node.get("arg", {}).get("A_Const", {}).get("sval", {}).get("sval")
                        if not isinstance(literal, str):
                            raise ValueError("JSON source declaration requires a literal document")
                        # A finite malformed-literal screen, not PostgreSQL's
                        # runtime conversion or Unicode/numeric semantics.
                        json.loads(literal, parse_constant=invalid_constant)
                if kind == "A_Expr":
                    names = [part.get("String", {}).get("sval") for part in node.get("name", [])]
                    if (node.get("kind") != "AEXPR_OP" or len(names) != 1
                            or names[0] not in JSON_EXTRACTION_OPERATORS):
                        raise ValueError("another operator is outside this JSON extraction population")
                    left_form, left_cast = operand(node.get("lexpr"))
                    right_form, right_cast = operand(node.get("rexpr"))
                    result.append({"operator": names[0], "left_form": left_form, "left_cast": left_cast,
                                   "right_form": right_form, "right_cast": right_cast})
                walk(node)

    walk(parsed)
    validate_json_extractions(result)
    return result


def observe_oracle(sql: str, factor: str) -> dict:
    import pglast
    from pglast import ast, enums, parse_sql, parser, visitors

    if pglast.__version__ != "v7.21":
        raise ValueError("factor oracle requires pglast v7.21")
    tree = parse_sql(sql)
    if len(tree) != 1 or not isinstance(tree[0].stmt, ast.SelectStmt):
        raise ValueError("factor source must be one whole SELECT")

    class Observe(visitors.Visitor):
        def visit_TypeName(self, ancestors, node):
            names = [part.sval for part in node.names or ()]
            if (not names or names[-1] not in NEW_FAMILIES | OLD_FAMILIES
                    or len(names) > 2 or (len(names) == 2 and names[0] != "pg_catalog")
                    or (node.arrayBounds and factor not in ARRAY_FACTORS | {"row_comparisons", "ilike"})):
                raise ValueError("array/user-defined type belongs to a later factor")

        def visit_FuncCall(self, ancestors, node):
            names = [part.sval for part in node.funcname]
            if (len(names) != 1 or node.func_variadic or node.over or node.agg_order
                    or node.agg_within_group
                    or any(isinstance(arg, ast.NamedArgExpr) for arg in node.args or ())):
                raise ValueError("qualified/named/variadic/window/ordered calls belong to later factors")
            if names[0] not in AGGREGATES:
                if node.agg_distinct or node.agg_star:
                    raise ValueError("aggregate-style general calls belong to a later factor")
                self.functions.add(names[0])

        def visit_CaseExpr(self, ancestors, node):
            self.forms.add("searched-case" if node.arg is None else "simple-case")

        def visit_CoalesceExpr(self, ancestors, node):
            self.forms.add("coalesce")

        def visit_MinMaxExpr(self, ancestors, node):
            self.forms.add("greatest" if node.op == enums.MinMaxOp.IS_GREATEST else "least")

        def visit_A_Expr(self, ancestors, node):
            if node.kind == enums.A_Expr_Kind.AEXPR_NULLIF:
                self.forms.add("nullif")

        def visit_ParamRef(self, ancestors, node):
            self.slots.add(node.number)

        def visit_LockingClause(self, ancestors, node):
            strengths = {"LCS_FORUPDATE": "update", "LCS_FORNOKEYUPDATE": "no-key-update",
                         "LCS_FORSHARE": "share", "LCS_FORKEYSHARE": "key-share"}
            policies = {"LockWaitBlock": "default", "LockWaitError": "nowait",
                        "LockWaitSkip": "skip-locked"}
            if any(rel.schemaname or rel.catalogname for rel in node.lockedRels or ()):
                raise ValueError("qualified lock targets belong to a later factor")
            self.locks.append({"strength": strengths[node.strength.name],
                               "wait_policy": policies[node.waitPolicy.name],
                               "targets": [rel.relname for rel in node.lockedRels or ()]})

    observer = Observe()
    observer.functions, observer.forms, observer.slots = set(), set(), set()
    observer.locks = []
    observer(tree)
    allowed = {"general-function-call", "comma-from", "expression-limit-offset", "extended-type"}
    if factor in {"conditional", "locking", "derived_contract", "array_types", "array_quantified", "row_comparisons", "concatenation", "ilike", "regex"} | JOIN_FACTORS:
        allowed.add("conditional-expression")
    if factor in {"locking", "array_types", "row_comparisons"}:
        allowed.add("row-locking")
    if factor in ARRAY_FACTORS | {"row_comparisons", "ilike", "json_extraction"}:
        allowed.add("array-or-subscripting")
    if factor in {"array_quantified", "row_comparisons", "ilike"}:
        allowed.add("quantified-comparison")
    if factor == "row_comparisons":
        allowed.add("row-constructor")
    if factor in {"concatenation", "ilike", "regex", "json_extraction"}:
        allowed.add("extended-operator")
    unexpected = set(features(json.loads(parser.parse_sql_json(sql)))) - allowed
    if unexpected:
        raise ValueError(f"source has later-factor dependencies: {sorted(unexpected)}")
    if observer.slots != set(parameter_slots(sql)):
        raise ValueError("parameter-slot observer disagrees with PostgreSQL")
    observation = {"function_names": sorted(observer.functions),
                   "conditional_forms": sorted(observer.forms)}
    if factor == "functions" and (not observer.functions or observer.forms):
        raise ValueError("plain function source must exercise a general call without conditionals")
    if factor == "conditional" and not observer.forms:
        raise ValueError("conditional source does not exercise the factor")
    if factor == "locking":
        if not observer.locks:
            raise ValueError("locking source does not exercise the factor")
        observation["locking_clauses"] = observer.locks
    if factor in JOIN_FACTORS:
        query = tree[0].stmt
        if (query.withClause or query.distinctClause or query.groupClause
                or query.havingClause or query.larg or query.rarg or query.lockingClause
                or len(query.fromClause or ()) != 1
                or not isinstance(query.fromClause[0], ast.JoinExpr)):
            raise ValueError("join source must contain one base-table join tree")

        def join_tree(node):
            if isinstance(node, ast.RangeVar):
                if (node.schemaname or node.catalogname or node.inh is False
                        or (node.alias and node.alias.colnames)):
                    raise ValueError("qualified/ONLY/column-aliased sources are outside this population")
                return {"kind": "table", "name": node.relname,
                        "alias": node.alias.aliasname if node.alias else None}
            if (not isinstance(node, ast.JoinExpr) or node.join_using_alias or node.alias
                    or (factor == "join_contract" and (node.isNatural or node.usingClause))):
                raise ValueError("unsupported derived/aliased join or condition for this population")
            condition = ("natural" if node.isNatural else "using" if node.usingClause
                         else "on" if node.quals is not None else "none")
            kind = {"JOIN_INNER": "cross" if condition == "none" else "inner",
                    "JOIN_LEFT": "left", "JOIN_RIGHT": "right",
                    "JOIN_FULL": "full"}.get(node.jointype.name)
            if kind not in JOIN_KINDS or (kind != "cross" and condition == "none"):
                raise ValueError("join has no supported condition")
            result = {"kind": kind, "condition": condition,
                      "left": join_tree(node.larg), "right": join_tree(node.rarg)}
            if condition == "using":
                result["columns"] = [column.sval for column in node.usingClause]
            return result

        observation["join_tree"] = join_tree(query.fromClause[0])
        validate_join_tree(observation["join_tree"], allow_merged=factor in MERGED_FACTORS)
        if factor in MERGED_FACTORS and not merged_join_kinds(
                observation["join_tree"], MERGED_FACTORS[factor]):
            raise ValueError("source does not exercise its merged join factor")
    if factor == "derived_contract":
        parsed = json.loads(parser.parse_sql_json(sql))["stmts"][0]["stmt"]
        observation["derived_sources"] = observe_derived_queries(parsed)
        validate_derived_sources(observation["derived_sources"])
    if factor == "array_types":
        parsed = json.loads(parser.parse_sql_json(sql))["stmts"][0]["stmt"]
        observation["array_types"] = observe_array_types(parsed)
    if factor == "array_constructors":
        parsed = json.loads(parser.parse_sql_json(sql))["stmts"][0]["stmt"]
        observation["array_constructors"] = observe_array_constructors(parsed)
    if factor == "array_quantified":
        parsed = json.loads(parser.parse_sql_json(sql))["stmts"][0]["stmt"]
        observation["array_quantified"] = observe_array_quantified(parsed, sql)
    if factor == "array_subscripts":
        parsed = json.loads(parser.parse_sql_json(sql))["stmts"][0]["stmt"]
        observation["array_subscripts"] = observe_array_subscripts(parsed)
    if factor == "row_comparisons":
        parsed = json.loads(parser.parse_sql_json(sql))["stmts"][0]["stmt"]
        observation["row_comparisons"] = observe_row_comparisons(parsed)
    if factor == "concatenation":
        parsed = json.loads(parser.parse_sql_json(sql))["stmts"][0]["stmt"]
        observation["concatenations"] = observe_concatenations(parsed)
    if factor in PATTERN_OPERATORS:
        parsed = json.loads(parser.parse_sql_json(sql))["stmts"][0]["stmt"]
        observation["pattern_matches"] = observe_pattern_matches(parsed, factor)
    if factor == "json_extraction":
        parsed = json.loads(parser.parse_sql_json(sql))["stmts"][0]["stmt"]
        observation["json_extractions"] = observe_json_extractions(parsed)
    return observation


def validate_population(records: list[dict], factor: str) -> None:
    if len(records) != 50 or Counter(row["source"] for row in records) != POPULATIONS[factor]:
        raise ValueError("expected 50 statements with the pinned factor source population")
    for field in ("id", "sql"):
        if len({row[field] for row in records}) != 50:
            raise ValueError(f"duplicate factor {field}")
    if len({comparison_key(row["sql"]) for row in records}) != 50:
        raise ValueError("case/whitespace duplicate factor SQL")
    forms, names, strengths, policies, join_kinds = set(), set(), set(), set(), set()
    derived_alias_cases, derived_max_depth = 0, 0
    array_elements = set()
    constructor_count, constructor_empty, constructor_nested, constructor_depth = 0, 0, 0, 0
    quantified_ops, quantifiers, quantified_right = Counter(), Counter(), Counter()
    subscript_dimensions, subscript_groups = Counter(), Counter()
    subscript_nested = 0
    row_operators, row_arities, row_forms = Counter(), Counter(), Counter()
    concat_left, concat_right, concat_casts = Counter(), Counter(), Counter()
    pattern_operators, pattern_left, pattern_right = Counter(), Counter(), Counter()
    json_operators, json_left, json_right, json_left_casts, json_right_casts = (
        Counter(), Counter(), Counter(), Counter(), Counter())
    for row in records:
        if row["factor"] != factor or not re.match(r"(SELECT|WITH)\b", first_sql_text(row["sql"]), re.I):
            raise ValueError("factor/whole-query identity changed")
        if "\x00" in row["sql"] or row["sql"] != row["raw_sql"] or row["transformations"]:
            raise ValueError("concrete SQL text was changed")
        if row["observed_parameter_slots"] != parameter_slots(row["sql"]):
            raise ValueError("parameter-slot observation changed")
        if row["parameter_types"] is not None or row["application_schema_validity"] != "not-claimed":
            raise ValueError("concrete source must not invent application bindings")
        observation = row["observed_syntax"]
        expected_keys = {"function_names", "conditional_forms"}
        if factor == "locking":
            expected_keys.add("locking_clauses")
        if factor in JOIN_FACTORS:
            expected_keys.add("join_tree")
        if factor == "derived_contract":
            expected_keys.add("derived_sources")
        if factor == "array_types":
            expected_keys.add("array_types")
        if factor == "array_constructors":
            expected_keys.add("array_constructors")
        if factor == "array_quantified":
            expected_keys.add("array_quantified")
        if factor == "array_subscripts":
            expected_keys.add("array_subscripts")
        if factor == "row_comparisons":
            expected_keys.add("row_comparisons")
        if factor == "concatenation":
            expected_keys.add("concatenations")
        if factor in PATTERN_OPERATORS:
            expected_keys.add("pattern_matches")
        if factor == "json_extraction":
            expected_keys.add("json_extractions")
        if set(observation) != expected_keys:
            raise ValueError("unexpected factor observation")
        for key in ("function_names", "conditional_forms"):
            value = observation[key]
            if not isinstance(value, list) or value != sorted(set(value)):
                raise ValueError("factor observation must be a sorted unique list")
        if not set(observation["conditional_forms"]) <= CONDITIONAL_FORMS:
            raise ValueError("unknown conditional form")
        if factor == "functions" and (not observation["function_names"]
                                      or observation["conditional_forms"]):
            raise ValueError("plain function factor is missing or has later conditionals")
        if factor == "conditional" and not observation["conditional_forms"]:
            raise ValueError("conditional factor is absent")
        if factor == "locking":
            locks = observation["locking_clauses"]
            if not isinstance(locks, list) or not locks:
                raise ValueError("locking factor is absent")
            for lock in locks:
                if (set(lock) != {"strength", "wait_policy", "targets"}
                        or lock["strength"] not in LOCK_STRENGTHS
                        or lock["wait_policy"] not in LOCK_POLICIES
                        or not isinstance(lock["targets"], list)
                        or not all(isinstance(target, str) and target for target in lock["targets"])):
                    raise ValueError("invalid locking observation")
                strengths.add(lock["strength"])
                policies.add(lock["wait_policy"])
        if factor in JOIN_FACTORS:
            kinds = validate_join_tree(observation["join_tree"], allow_merged=factor in MERGED_FACTORS)
            if factor in MERGED_FACTORS:
                kinds = merged_join_kinds(observation["join_tree"], MERGED_FACTORS[factor])
                if not kinds:
                    raise ValueError("merged join factor is absent")
            join_kinds.update(kinds)
        if factor == "derived_contract":
            sources = observation["derived_sources"]
            validate_derived_sources(sources)
            derived_alias_cases += any(source["columns"] for source in sources)
            derived_max_depth = max(derived_max_depth, *(source["query_depth"] for source in sources))
        if factor == "array_types":
            validate_array_types(observation["array_types"])
            array_elements.update(entry["element_type"] for entry in observation["array_types"])
        if factor == "array_constructors":
            constructors = observation["array_constructors"]
            validate_array_constructors(constructors)
            constructor_count += len(constructors)
            constructor_empty += sum(entry["length"] == 0 for entry in constructors)
            constructor_nested += any(entry["depth"] > 1 for entry in constructors)
            constructor_depth = max(constructor_depth, *(entry["depth"] for entry in constructors))
        if factor == "array_quantified":
            comparisons = observation["array_quantified"]
            validate_array_quantified(comparisons)
            quantified_ops.update(entry["source_operator"] for entry in comparisons)
            quantifiers.update(entry["quantifier"] for entry in comparisons)
            quantified_right.update(entry["right_form"] for entry in comparisons)
        if factor == "array_subscripts":
            groups = observation["array_subscripts"]
            validate_array_subscripts(groups)
            subscript_groups.update(len(group["dimensions"]) for group in groups)
            subscript_nested += any(group["depth"] > 1 for group in groups)
            subscript_dimensions.update(
                "slice" if dimension["slice"] else "element"
                for group in groups for dimension in group["dimensions"])
        if factor == "row_comparisons":
            comparisons = observation["row_comparisons"]
            validate_row_comparisons(comparisons)
            row_operators.update(entry["operator"] for entry in comparisons)
            row_arities.update(entry["arity"] for entry in comparisons)
            row_forms.update((entry["left_form"], entry["right_form"]) for entry in comparisons)
        if factor == "concatenation":
            entries = observation["concatenations"]
            validate_concatenations(entries)
            concat_left.update(entry["left"]["form"] for entry in entries)
            concat_right.update(entry["right"]["form"] for entry in entries)
            concat_casts.update(entry[side]["declared_type"] for entry in entries for side in ("left", "right")
                                if entry[side]["declared_type"] is not None)
        if factor in PATTERN_OPERATORS:
            entries = observation["pattern_matches"]
            validate_pattern_matches(entries, factor)
            pattern_operators.update(entry["operator"] for entry in entries)
            pattern_left.update(entry["left_form"] for entry in entries)
            pattern_right.update(entry["right_form"] for entry in entries)
        if factor == "json_extraction":
            entries = observation["json_extractions"]
            validate_json_extractions(entries)
            json_operators.update(entry["operator"] for entry in entries)
            json_left.update(entry["left_form"] for entry in entries)
            json_right.update(entry["right_form"] for entry in entries)
            json_left_casts.update(entry["left_cast"] for entry in entries)
            json_right_casts.update(entry["right_cast"] for entry in entries)
        names.update(observation["function_names"])
        forms.update(observation["conditional_forms"])
    if factor == "conditional" and forms != CONDITIONAL_FORMS:
        raise ValueError("all six conditional forms must be represented")
    if factor == "functions" and len(names) < 20:
        raise ValueError("plain function corpus must retain at least twenty distinct function names")
    if factor == "locking" and (strengths != LOCK_STRENGTHS or policies != LOCK_POLICIES):
        raise ValueError("all four locking strengths and three wait policies must be represented")
    if factor == "join_contract" and join_kinds != JOIN_KINDS:
        raise ValueError("all five base-table join kinds must be represented")
    if factor in MERGED_FACTORS and join_kinds != JOIN_KINDS - {"cross"}:
        raise ValueError("all four merged join kinds must be represented")
    if factor == "derived_contract" and (derived_alias_cases < 4 or derived_max_depth < 3):
        raise ValueError("derived population must retain column aliases and depth-three nesting")
    if factor == "array_types" and array_elements != ARRAY_ELEMENT_FAMILIES:
        raise ValueError("array type population must retain all seven pinned element families")
    if factor == "array_constructors" and (
            constructor_count != 94 or constructor_empty != 1
            or constructor_nested != 12 or constructor_depth != 6):
        raise ValueError("constructor population must retain its 94 nodes, typed empty, and nesting")
    if factor == "array_quantified" and (
            quantified_ops != {"=": 45, ">=": 4, "!=": 1, ">": 1}
            or quantifiers != {"any": 41, "all": 10}
            or quantified_right != {"TypeCast": 34, "A_Const": 13, "ParamRef": 2, "A_ArrayExpr": 2}):
        raise ValueError("quantified population must retain its 51 nodes and source spellings")
    if factor == "array_subscripts" and (
            subscript_dimensions != {"element": 71, "slice": 46}
            or subscript_groups != {1: 47, 2: 17, 3: 12}
            or subscript_nested != 3):
        raise ValueError("subscript population must retain its 117 dimensions and nested groups")
    if factor == "row_comparisons" and (
            row_operators != {"=": 40, ">": 10, ">=": 9, "<=": 7, "<": 6}
            or row_arities != {2: 56, 3: 12, 4: 3, 5: 1}
            or row_forms != {("implicit", "implicit"): 71, ("explicit", "explicit"): 1}):
        raise ValueError("row comparison population must retain its 72 pairs and source forms")
    if factor == "concatenation" and (
            concat_left != {"A_Expr": 35, "TypeCast": 30, "A_Const": 15, "FuncCall": 5, "ColumnRef": 1}
            or concat_right != {"A_Const": 39, "FuncCall": 25, "TypeCast": 20, "A_Expr": 2}
            or concat_casts != {"jsonb": 42, "text": 4, "pg_catalog.bpchar": 2,
                                "pg_catalog.varchar": 1, "bytea": 1}):
        raise ValueError("concatenation population must retain its 86 nodes and declared casts")
    if factor == "ilike" and (
            pattern_operators != {"ILIKE": 43, "NOT ILIKE": 7}
            or pattern_left != {"ColumnRef": 26, "A_Const": 24}
            or pattern_right != {"A_Const": 40, "ColumnRef": 7, "A_Expr": 2, "FuncCall": 1}):
        raise ValueError("ILIKE population must retain its 50 nodes and operand forms")
    if factor == "regex" and (
            pattern_operators != {"~": 42, "~*": 6, "!~": 1, "!~*": 1}
            or pattern_left != {"A_Const": 27, "ColumnRef": 22, "TypeCast": 1}
            or pattern_right != {"A_Const": 49, "ColumnRef": 1}):
        raise ValueError("regex population must retain its 50 nodes and operand forms")
    if factor == "json_extraction" and (
            json_operators != {"->": 15, "->>": 11, "#>": 12, "#>>": 14}
            or json_left != {"TypeCast": 50, "A_Expr": 2}
            or json_right != {"A_Const": 27, "A_ArrayExpr": 17, "TypeCast": 8}
            or json_left_casts != {"pg_catalog.json": 25, "jsonb": 25, None: 2}
            or json_right_casts != {None: 44, "text": 4, "pg_catalog.int4": 4}):
        raise ValueError("JSON extraction population must retain its 52 nodes and declared casts")


def extract(manifest: dict, factor: str, root: Path = ROOT) -> list[dict]:
    if (factor not in POPULATIONS or manifest.get("format_version") != 1
            or manifest.get("factor") != factor or manifest.get("expected_count") != 50
            or manifest.get("expected_sources") != POPULATIONS[factor]
            or set(manifest["sources"]) != set(POPULATIONS[factor])):
        raise ValueError("unexpected factor source manifest")
    files, spans = {}, {}
    for name, metadata in manifest["sources"].items():
        if not re.fullmatch(r"[0-9a-f]{40}", metadata["commit"]):
            raise ValueError("source revision is not a full commit pin")
        checked_file(root, metadata["license_file"], metadata["license_sha256"])
        for entry in metadata["files"]:
            key = (name, entry["path"])
            if key in files:
                raise ValueError("duplicate source input")
            files[key] = checked_file(root, entry["local_path"], entry["sha256"]).decode("utf-8")
            if factor in {"locking", "derived_contract", "row_comparisons", "concatenation", "json_extraction"} | ARRAY_FACTORS | JOIN_FACTORS | PATTERN_OPERATORS.keys():
                spans[key] = statement_spans(files[key]) if entry["path"].endswith(".sql") else []
    records, used = [], set()
    for selection in manifest["selections"]:
        name, path = selection["source"], selection["path"]
        key = (name, path)
        if key not in files:
            raise ValueError("selection has no pinned source input")
        used.add(key)
        if selection["selector"]["kind"] == "tcl_sql_statement":
            if factor not in {*MERGED_FACTORS, "row_comparisons"} or name != "sqlite":
                raise ValueError("Tcl SQL selection is outside its explicit source factors")
            sql, line, detail = selected_tcl_sql(files[key], selection["selector"])
        elif selection["selector"]["kind"] == "sqllogic_query":
            if factor not in {"array_subscripts", "ilike"} or name != "duckdb":
                raise ValueError("SQLLogicTest selection is outside its explicit source factor")
            sql, line, detail = selected_sqllogic_sql(files[key], selection["selector"])
        elif factor in {"locking", "derived_contract", "row_comparisons", "concatenation", "json_extraction"} | ARRAY_FACTORS | JOIN_FACTORS | PATTERN_OPERATORS.keys():
            sql, line, detail = selected_sql(files[key], selection["selector"], spans[key])
        else:
            sql, line, detail = select_sql(files[key], selection["selector"])
        if sha256(sql.encode()) != selection["sql_sha256"]:
            raise ValueError("selected SQL hash mismatch")
        metadata = manifest["sources"][name]
        suffix = (f"tcl-{detail['command_start']}-statement-{detail['statement_index']}"
                  if detail.get("extraction") == "tcl_sql_statement"
                  else f"sqllogic-query-{detail['header_line']}"
                  if detail.get("extraction") == "sqllogic_query"
                  else detail.get("symbol", f"statement-{detail.get('statement_index')}"))
        records.append({
            "id": f"{factor}:{name}:{path}:{suffix}", "factor": factor,
            "source": name, "source_kind": metadata["source_kind"],
            **({"source_dialect": metadata["source_dialect"]} if "source_dialect" in metadata else {}),
            "source_file": path, "line": line,
            "source_url": f"{metadata['repository']}/blob/{metadata['commit']}/{path}#L{line}",
            "commit": metadata["commit"], "license": metadata["license"], **detail,
            "observed_syntax": selection["observed_syntax"],
            "observed_parameter_slots": parameter_slots(sql),
            "parameter_types": None, "application_schema_validity": "not-claimed",
            "raw_sql": sql, "sql": sql, "sql_sha256": selection["sql_sha256"],
            "transformations": [],
        })
    if used != set(files):
        raise ValueError("unused pinned source input")
    validate_population(records, factor)
    return records


def render(records: list[dict]) -> str:
    return "".join(json.dumps(row, ensure_ascii=False) + "\n" for row in records)


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--factor", choices=tuple(POPULATIONS), required=True)
    parser.add_argument("--check", action="store_true")
    parser.add_argument("--oracle", action="store_true")
    args = parser.parse_args()
    directory = ROOT / "fixtures" / args.factor
    records = extract(json.loads((directory / "concrete_sources.json").read_text()), args.factor)
    if args.oracle:
        for row in records:
            if observe_oracle(row["sql"], args.factor) != row["observed_syntax"]:
                raise ValueError(f"{row['id']}: factor observation disagrees with PostgreSQL")
    output, text = directory / "concrete.jsonl", render(records)
    if args.check:
        if not output.is_file() or output.read_text() != text:
            raise ValueError("stale factor concrete corpus")
    else:
        output.write_text(text)
    print(f"{args.factor}: 50 unchanged whole SELECTs; source hashes verified"
          + ("; PostgreSQL factor/dependency observations verified" if args.oracle else ""))
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
