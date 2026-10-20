"""Written COLLATE and declaration observations without catalog resolution.

Raw parser names, declaration options and type spellings are provenance only.
No provider, object OID, effective search path, implicit default or installed
locale is inferred by this module.
"""
from __future__ import annotations

import json
import re

from extract_extended_type_corpus import sql_code
from observe_qualified_name_source import source_name


def char_index(sql, byte_location):
    if type(byte_location) is not int or not 0 <= byte_location < len(sql.encode()):
        raise ValueError("invalid UTF-8 source position")
    try:
        return len(sql.encode()[:byte_location].decode())
    except UnicodeDecodeError as error:
        raise ValueError("source position splits a UTF-8 character") from error


def skip_space(sql, index):
    while index < len(sql):
        if sql[index].isspace():
            index += 1
        elif sql.startswith("--", index):
            end = sql.find("\n", index + 2)
            index = len(sql) if end < 0 else end + 1
        elif sql.startswith("/*", index):
            depth, index = 1, index + 2
            while depth and index < len(sql):
                if sql.startswith("/*", index):
                    depth, index = depth + 1, index + 2
                elif sql.startswith("*/", index):
                    depth, index = depth - 1, index + 2
                else:
                    index += 1
            if depth:
                raise ValueError("unterminated comment after COLLATE")
        else:
            break
    return index


def written_collation(sql, location):
    index, code = char_index(sql, location), sql_code(sql)
    if (code[index:index + 7].lower() != "collate"
            or (index and re.match(r"[A-Za-z_0-9$]", code[index - 1]))
            or (index + 7 < len(code) and re.match(r"[A-Za-z_0-9$]", code[index + 7]))):
        raise ValueError("CollateClause location does not identify a COLLATE token")
    start = skip_space(sql, index + 7)
    name_location = len(sql[:start].encode())
    name = source_name(sql, name_location)
    if len(name["parts"]) not in {1, 2} or "*" in name["parts"]:
        raise ValueError("unselected collation name shape")
    return {**name, "byte_location": location, "name_byte_location": name_location}


def validate_observation(value, sql):
    if (not isinstance(value, dict)
            or set(value) != {"collations", "relations", "parameter_slots", "source_free"}
            or not isinstance(value["collations"], list) or not value["collations"]
            or not isinstance(value["relations"], list) or value["parameter_slots"] != []
            or type(value["source_free"]) is not bool):
        raise ValueError("invalid COLLATE source observation")
    positions = []
    for entry in value["collations"]:
        if (not isinstance(entry, dict)
                or set(entry) != {"parts", "quoted", "spelling", "byte_location",
                                  "name_byte_location", "argument_kind"}
                or not isinstance(entry["quoted"], list)
                or any(type(flag) is not bool for flag in entry["quoted"])
                or type(entry["name_byte_location"]) is not int
                or entry["argument_kind"] not in {"A_Const", "ColumnRef", "A_ArrayExpr"}):
            raise ValueError("unselected COLLATE argument observation")
        if {k: v for k, v in entry.items() if k != "argument_kind"} != written_collation(sql, entry["byte_location"]):
            raise ValueError("COLLATE source spelling/position changed")
        positions.append(entry["byte_location"])
    if positions != sorted(set(positions)):
        raise ValueError("COLLATE occurrences must be unique and in lexical order")
    locations = []
    for entry in value["relations"]:
        if (set(entry) != {"parts", "quoted", "spelling", "byte_location"}
                or not isinstance(entry["quoted"], list)
                or any(type(flag) is not bool for flag in entry["quoted"])
                or {k: v for k, v in entry.items() if k != "byte_location"}
                != source_name(sql, entry["byte_location"])):
            raise ValueError("relation spelling/position changed")
        if len(entry["parts"]) not in {1, 2} or "*" in entry["parts"]:
            raise ValueError("unselected relation name shape")
        locations.append(entry["byte_location"])
    if (locations != sorted(set(locations))
            or value["source_free"] != (not value["relations"])):
        raise ValueError("incorrect lexical table/parameter dependency observation")


def observe_collations(parsed, sql):
    if not isinstance(parsed, dict) or set(parsed) != {"SelectStmt"}:
        raise ValueError("collation source must be one complete SELECT")
    root = parsed["SelectStmt"]
    if (root.get("op", "SETOP_NONE") != "SETOP_NONE"
            or any(root.get(k) for k in ("withClause", "valuesLists", "groupClause", "havingClause",
                                        "distinctClause", "windowClause", "intoClause", "lockingClause"))):
        raise ValueError("unselected query dependency in COLLATE source")
    collations, relations = [], []

    def walk(value):
        if isinstance(value, list):
            for child in value:
                walk(child)
        elif isinstance(value, dict):
            for kind, node in value.items():
                if kind in {"SelectStmt", "SubLink", "RangeSubselect", "RangeFunction", "RangeTableSample",
                            "WindowDef", "FuncCall", "ParamRef"}:
                    raise ValueError("unselected nested/function/parameter dependency")
                if kind == "CollateClause":
                    spelling = written_collation(sql, node["location"])
                    if spelling["parts"] != [p["String"]["sval"] for p in node["collname"]]:
                        raise ValueError("raw COLLATE name disagrees with its source spelling")
                    if not isinstance(node["arg"], dict) or len(node["arg"]) != 1:
                        raise ValueError("unexpected COLLATE argument")
                    collations.append({**spelling, "argument_kind": next(iter(node["arg"]))})
                elif kind == "RangeVar":
                    if node.get("catalogname"):
                        raise ValueError("database-qualified source is outside this population")
                    spelling = source_name(sql, node["location"])
                    names = ([node["schemaname"]] if node.get("schemaname") else []) + [node["relname"]]
                    if spelling["parts"] != names:
                        raise ValueError("raw relation name disagrees with its source spelling")
                    relations.append({**spelling, "byte_location": node["location"]})
                walk(node)
    walk(root)
    result = {
        "collations": sorted(collations, key=lambda c: c["byte_location"]),
        "relations": sorted(relations, key=lambda r: r["byte_location"]),
        "parameter_slots": [], "source_free": not relations,
    }
    validate_observation(result, sql)
    return result


def strings(nodes):
    return [n["String"]["sval"] for n in nodes]


def observe_declaration(parsed):
    """Record only explicitly written declaration properties."""
    if set(parsed) == {"CreateSchemaStmt"}:
        node = parsed["CreateSchemaStmt"]
        if set(node) != {"schemaname"}:
            raise ValueError("unselected schema declaration")
        return {"kind": "schema", "name": node["schemaname"]}
    if set(parsed) == {"VariableSetStmt"}:
        node = parsed["VariableSetStmt"]
        if (node["name"] != "search_path" or node["kind"] != "VAR_SET_VALUE"
                or node.get("is_local") or len(node.get("args", [])) != 1):
            raise ValueError("unselected session declaration")
        return {"kind": "search_path", "written_value": node["args"][0]["A_Const"]["sval"]["sval"]}
    if set(parsed) == {"DefineStmt"}:
        node = parsed["DefineStmt"]
        if node["kind"] != "OBJECT_COLLATION":
            raise ValueError("unselected object declaration")
        options = []
        for wrapped in node.get("definition", []):
            entry, argument = wrapped["DefElem"], wrapped["DefElem"]["arg"]
            if set(argument) == {"String"}:
                value = argument["String"]["sval"]
            elif set(argument) == {"Boolean"}:
                value = argument["Boolean"]["boolval"]
            elif set(argument) == {"TypeName"} and len(argument["TypeName"]["names"]) == 1:
                value = strings(argument["TypeName"]["names"])[0]
            else:
                raise ValueError("unselected collation option value")
            options.append({"name": entry["defname"], "value": value})
        if (not options or len({o["name"] for o in options}) != len(options)
                or any(o["name"] not in {"provider", "locale", "deterministic", "rules"} for o in options)):
            raise ValueError("unselected collation declaration options")
        return {"kind": "collation", "name": strings(node["defnames"]), "written_options": options}
    if set(parsed) == {"CreateStmt"}:
        node, columns = parsed["CreateStmt"], []
        if any(node.get(k) for k in ("inhRelations", "partspec", "ofTypename", "constraints", "options")):
            raise ValueError("unselected table declaration")
        for wrapped in node.get("tableElts", []):
            if set(wrapped) != {"ColumnDef"}:
                raise ValueError("unselected table field declaration")
            column = wrapped["ColumnDef"]
            constraints = [c["Constraint"]["contype"] for c in column.get("constraints", [])]
            if any(c != "CONSTR_NOTNULL" for c in constraints) or column["typeName"].get("typmods"):
                raise ValueError("unselected field constraint/modifier")
            columns.append({
                "name": column["colname"],
                "raw_type_name": strings(column["typeName"]["names"]),
                "written_array_bounds": [b["Integer"].get("ival", 0) for b in column["typeName"].get("arrayBounds", [])],
                "written_not_null": "CONSTR_NOTNULL" in constraints,
                "written_collation": strings(column["collClause"]["collname"]) if column.get("collClause") else None,
            })
        if not columns:
            raise ValueError("empty table declaration")
        relation = node["relation"]
        return {"kind": "table", "name": ([relation["schemaname"]] if relation.get("schemaname") else [])
                + [relation["relname"]], "columns": columns}
    raise ValueError("unselected declaration context")


def oracle(sql, *, declaration=False):
    import pglast
    from pglast import parser
    if pglast.__version__ != "v7.21":
        raise ValueError("observation oracle requires pinned pglast v7.21")
    statements = json.loads(parser.parse_sql_json(sql))["stmts"]
    if len(statements) != 1:
        raise ValueError("source must contain one complete statement")
    parsed = statements[0]["stmt"]
    return observe_declaration(parsed) if declaration else observe_collations(parsed, sql)
