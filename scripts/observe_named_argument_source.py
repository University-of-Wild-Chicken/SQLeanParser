"""Finite observations of unchanged named-call sources and pinned sqlc inputs.

This is a source-population observer, not function overload/default resolution.
Only the two registered generated interfaces provide parameter declarations.
"""
from __future__ import annotations

import re

from extract_application_corpus import decode_constants, first_sql_text, go_tokens
from extract_extended_type_corpus import sql_code
from extract_pagination_corpus import comparison_key, sha256

INTERFACE_PATH = "internal/endtoend/testdata/func_args/pgx/v5/go/query.sql.go"
QUERY_PATH = "internal/endtoend/testdata/func_args/pgx/v5/query.sql"
INTERFACE_CASES = {
    f"named_arguments:sqlc:{QUERY_PATH}:statement-1":
        ("MakeIntervalSecs", "makeIntervalSecs", "secs", "float64", "double precision"),
    f"named_arguments:sqlc:{QUERY_PATH}:statement-2":
        ("MakeIntervalDays", "makeIntervalDays", "dollar_1", "int32", "integer"),
}


def position(sql: str, byte_location: int) -> int:
    if type(byte_location) is not int or not 0 <= byte_location < len(sql.encode()):
        raise ValueError("named-call source location is absent/out of bounds")
    try:
        return len(sql.encode()[:byte_location].decode())
    except UnicodeDecodeError as error:
        raise ValueError("named-call source location splits a UTF-8 character") from error


def identifier_at(sql: str, name: str, byte_location: int, suffix: str) -> None:
    if not isinstance(name, str) or not re.fullmatch(r"[a-z_][a-z_0-9$]*", name):
        raise ValueError("finite named-call observer requires an unquoted identifier")
    offset, code = position(sql, byte_location), sql_code(sql)
    if ((offset and (code[offset - 1].isalnum() or code[offset - 1] in "_$."))
            or not re.match(re.escape(name) + r"(?![A-Za-z_0-9$])\s*" + suffix,
                            code[offset:], re.I)):
        raise ValueError("named-call observation disagrees with source spelling")


def validate_named_arguments(observation: dict, sql: str | None = None) -> None:
    if type(observation.get("source_free")) is not bool:
        raise ValueError("named-call source-free observation must be Boolean")
    calls = observation.get("named_calls")
    if not isinstance(calls, list) or not calls:
        raise ValueError("named-argument factor is absent")
    locations = []
    for call in calls:
        if (not isinstance(call, dict)
                or set(call) != {"function", "byte_location", "argument_names", "named_arguments"}
                or type(call["byte_location"]) is not int or call["byte_location"] < 0):
            raise ValueError("invalid named-call observation")
        names, arguments = call["argument_names"], call["named_arguments"]
        if (not isinstance(names, list) or not names
                or not all(name is None or isinstance(name, str) and name for name in names)
                or not isinstance(arguments, list) or not arguments):
            raise ValueError("invalid named/positional argument order")
        named_names = [name for name in names if name is not None]
        if len(named_names) != len(set(named_names)):
            raise ValueError("duplicate named arguments are outside this positive population")
        seen_named = False
        for name in names:
            if name is not None:
                seen_named = True
            elif seen_named:
                raise ValueError("positional argument follows a named argument")
        expected_ordinals = [i for i, name in enumerate(names) if name is not None]
        if len(arguments) != len(expected_ordinals):
            raise ValueError("named argument inventory is incomplete")
        previous_location = call["byte_location"]
        for ordinal, argument in zip(expected_ordinals, arguments):
            if (not isinstance(argument, dict)
                    or set(argument) != {"ordinal", "name", "notation", "byte_location"}
                    or type(argument["ordinal"]) is not int or argument["ordinal"] != ordinal
                    or argument["name"] != names[ordinal] or argument["notation"] not in {":=", "=>"}
                    or type(argument["byte_location"]) is not int
                    or argument["byte_location"] <= previous_location):
                raise ValueError("named argument identity/order is inconsistent")
            previous_location = argument["byte_location"]
            if sql is not None:
                identifier_at(sql, argument["name"], argument["byte_location"],
                              re.escape(argument["notation"]))
        locations.append(call["byte_location"])
        if sql is not None:
            identifier_at(sql, call["function"], call["byte_location"], r"\(")
    if len(locations) != len(set(locations)):
        raise ValueError("duplicate named call observation")


def observe_named_arguments(parsed: dict, sql: str) -> dict:
    if set(parsed) != {"SelectStmt"}:
        raise ValueError("named-call source must be one whole SELECT")
    calls, source_free = [], True

    def walk(value):
        nonlocal source_free
        if isinstance(value, list):
            for item in value:
                walk(item)
        elif isinstance(value, dict):
            for kind, node in value.items():
                if kind in {"RangeVar", "ColumnRef", "RangeFunction", "SubLink", "WindowDef",
                            "A_Indirection", "RowExpr", "CollateClause", "SQLValueFunction",
                            "InsertStmt", "UpdateStmt", "DeleteStmt", "MergeStmt"}:
                    raise ValueError("dependency is outside this closed named-call population")
                if kind == "ParamRef":
                    source_free = False
                if kind == "FuncCall":
                    names = [part.get("String", {}).get("sval") for part in node["funcname"]]
                    if (len(names) != 1 or any(node.get(key) for key in (
                            "agg_order", "agg_filter", "over", "agg_star", "agg_distinct",
                            "agg_within_group", "func_variadic"))):
                        raise ValueError("modified/qualified calls are outside this population")
                    arguments, argument_names = [], []
                    for ordinal, argument in enumerate(node.get("args", [])):
                        named = argument.get("NamedArgExpr")
                        argument_names.append(named["name"] if named else None)
                        if named:
                            offset = position(sql, named.get("location"))
                            match = re.match(r"[A-Za-z_][A-Za-z_0-9$]*\s*(=>|:=)",
                                             sql_code(sql)[offset:])
                            if not match:
                                raise ValueError("named argument notation is absent")
                            arguments.append({"ordinal": ordinal, "name": named["name"],
                                              "notation": match[1],
                                              "byte_location": named["location"]})
                    if arguments:
                        calls.append({"function": names[0], "byte_location": node.get("location"),
                                      "argument_names": argument_names,
                                      "named_arguments": arguments})
                walk(node)

    walk(parsed)
    result = {"source_free": source_free, "named_calls": calls}
    validate_named_arguments(result, sql)
    return result


def interface_evidence(case_id: str, sql: str, source: str, source_url: str) -> dict:
    """Check the two fixed generated methods; never infer a routine catalog."""
    if case_id not in INTERFACE_CASES:
        raise ValueError("unregistered generated interface")
    method, constant, parameter, go_type, pg_type = INTERFACE_CASES[case_id]
    declarations = {row["symbol"]: row for row in decode_constants(source)}
    declaration = declarations.get(constant, {})
    decoded = first_sql_text(declaration.get("raw_sql", "")).strip().rstrip(";")
    if comparison_key(decoded) != comparison_key(sql.strip().rstrip(";")):
        raise ValueError("generated constant does not contain the selected source query")
    tokens = [token for token in go_tokens(source) if token.kind != "newline"]
    expected = [token.text for token in go_tokens(
        f"func ( q * Queries ) {method} ( ctx context . Context , {parameter} {go_type} ) "
        f"( pgtype . Interval , error ) {{ row := q . db . QueryRow ( ctx , {constant} , "
        f"{parameter} )"
    )]
    matches = [tokens[i] for i in range(len(tokens) - len(expected) + 1)
               if [token.text for token in tokens[i:i + len(expected)]] == expected]
    if len(matches) != 1:
        raise ValueError("fixed generated method signature/call does not match")
    line = source.count("\n", 0, matches[0].start) + 1
    return {"kind": "pinned-generated-sqlc-interface", "method": method,
            "parameter_name": parameter, "go_type": go_type, "postgres_type": pg_type,
            "source_file": INTERFACE_PATH, "line": line,
            "source_url": source_url + f"#L{line}", "sha256": sha256(source.encode())}
