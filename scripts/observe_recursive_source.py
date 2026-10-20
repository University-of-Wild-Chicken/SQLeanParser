"""Lexical observations for pinned, unchanged recursive SELECT inputs.

These observations resolve CTE relation names, not columns or types. In
particular, source_free does not imply eligibility for an independent static
certificate, successful PostgreSQL analysis, or terminating execution.
"""
from __future__ import annotations

from collections import Counter
import json

from observe_qualified_name_source import source_name


def validate_observation(value, sql=None):
    if (not isinstance(value, dict)
            or set(value) != {"ctes", "relations", "parameter_slots", "source_free",
                              "dependencies", "functions", "actual_recursive_count"}):
        raise ValueError("invalid recursive source observations")
    definitions, references = value["ctes"], value["relations"]
    if not isinstance(definitions, list) or not definitions or not isinstance(references, list):
        raise ValueError("missing recursive CTE definitions/references")
    by_location = {}
    for entry in definitions:
        if (set(entry) != {"name", "column_aliases", "byte_location", "query_depth",
                          "with_recursive", "operator", "all", "self_references",
                          "anchor_references", "step_references"}
                or not isinstance(entry["name"], str) or not entry["name"]
                or not isinstance(entry["column_aliases"], list)
                or any(not isinstance(n, str) or not n for n in entry["column_aliases"])
                or any(type(entry[k]) is not int or entry[k] < 0 for k in
                       ("byte_location", "query_depth", "self_references",
                        "anchor_references", "step_references"))
                or type(entry["with_recursive"]) is not bool or type(entry["all"]) is not bool
                or entry["operator"] not in {"none", "union", "intersect", "except"}
                or entry["byte_location"] in by_location):
            raise ValueError("invalid recursive definition")
        if sql is not None and source_name(sql, entry["byte_location"])["parts"] != [entry["name"]]:
            raise ValueError("CTE name does not match its UTF-8 source position")
        by_location[entry["byte_location"]] = entry
    seen = set()
    for entry in references:
        if (set(entry) != {"parts", "byte_location", "definition_byte_location", "contexts"}
                or not isinstance(entry["parts"], list) or len(entry["parts"]) not in {1, 2}
                or any(not isinstance(n, str) or not n for n in entry["parts"])
                or type(entry["byte_location"]) is not int or entry["byte_location"] < 0
                or entry["byte_location"] in seen or not isinstance(entry["contexts"], list)):
            raise ValueError("invalid recursive relation reference")
        seen.add(entry["byte_location"])
        binding = entry["definition_byte_location"]
        if binding is not None and (type(binding) is not int or binding not in by_location
                                    or entry["parts"] != [by_location[binding]["name"]]):
            raise ValueError("reference does not match its recorded lexical CTE binding")
        context_ids = set()
        for context in entry["contexts"]:
            if (set(context) != {"definition_byte_location", "arm"}
                    or type(context["definition_byte_location"]) is not int
                    or context["definition_byte_location"] not in by_location
                    or context["definition_byte_location"] in context_ids
                    or context["arm"] not in {"body", "anchor", "step"}):
                raise ValueError("invalid containing CTE reference context")
            context_ids.add(context["definition_byte_location"])
        if sql is not None and source_name(sql, entry["byte_location"])["parts"] != entry["parts"]:
            raise ValueError("relation does not match its UTF-8 source position")
    for location, entry in by_location.items():
        contexts = [c for r in references if r["definition_byte_location"] == location
                    for c in r["contexts"] if c["definition_byte_location"] == location]
        if (entry["self_references"] != len(contexts)
                or entry["anchor_references"] != sum(c["arm"] == "anchor" for c in contexts)
                or entry["step_references"] != sum(c["arm"] == "step" for c in contexts)
                or (entry["self_references"] and not entry["with_recursive"])):
            raise ValueError("recursive counts disagree with lexical reference observations")
    slots = value["parameter_slots"]
    if (not isinstance(slots, list)
            or any(type(n) is not int or n < 1 for n in slots)
            or len(slots) != len(set(slots))
            or type(value["source_free"]) is not bool
            or value["source_free"] != (not slots and all(r["definition_byte_location"] is not None
                                                        for r in references))
            or type(value["actual_recursive_count"]) is not int
            or value["actual_recursive_count"] != sum(bool(c["self_references"]) for c in definitions)):
        raise ValueError("recursive source-free/parameter/count observations disagree")
    if (not isinstance(value["dependencies"], dict)
            or any(not isinstance(k, str) or type(v) is not int or v < 1
                   for k, v in value["dependencies"].items())
            or not isinstance(value["functions"], list)
            or any(not isinstance(f, str) or not f for f in value["functions"])
            or value["functions"] != sorted(set(value["functions"]))):
        raise ValueError("invalid recorded prerequisite dependencies")


def observe_recursive(parsed, sql):
    if not isinstance(parsed, dict) or set(parsed) != {"SelectStmt"}:
        raise ValueError("recursive input must be one complete SELECT")
    definitions, references, parameters = [], [], []
    dependencies, functions = Counter(), set()

    def query(node, outer, depth, contexts, owner=None):
        for key in ("valuesLists", "groupClause", "havingClause", "distinctClause",
                    "windowClause", "intoClause", "lockingClause"):
            if node.get(key):
                dependencies[key] += 1
        with_ = node.get("withClause", {})
        recursive = bool(with_.get("recursive", False))
        ctes, local = [], set()
        for wrapped in with_.get("ctes", []):
            if set(wrapped) != {"CommonTableExpr"}:
                raise ValueError("unexpected CTE definition node")
            cte = wrapped["CommonTableExpr"]
            if cte["ctename"] in local or set(cte["ctequery"]) != {"SelectStmt"}:
                raise ValueError("duplicate/modifying CTE is outside this source population")
            local.add(cte["ctename"])
            body = cte["ctequery"]["SelectStmt"]
            if cte.get("ctematerialized", "CTEMaterializeDefault") != "CTEMaterializeDefault":
                dependencies["materialized"] += 1
            for key in ("search_clause", "cycle_clause"):
                if cte.get(key):
                    dependencies[key] += 1
            entry = {
                "name": cte["ctename"],
                "column_aliases": [n["String"]["sval"] for n in cte.get("aliascolnames", [])],
                "byte_location": cte.get("location"), "query_depth": depth,
                "with_recursive": recursive,
                "operator": body.get("op", "SETOP_NONE").removeprefix("SETOP_").lower(),
                "all": bool(body.get("all", False)),
                "self_references": 0, "anchor_references": 0, "step_references": 0,
            }
            definitions.append(entry)
            ctes.append((cte, entry))
        visible = dict(outer)
        # PostgreSQL WITH RECURSIVE makes sibling names visible throughout the
        # group. This records forward references without claiming support for
        # their dependency ordering or mutual recursion in the strong profile.
        if recursive:
            visible.update((entry["name"], entry["byte_location"]) for _, entry in ctes)
        for cte, entry in ctes:
            location = entry["byte_location"]
            query(cte["ctequery"]["SelectStmt"], visible, depth + 1,
                  contexts + [{"definition_byte_location": location, "arm": "body"}], location)
            visible[entry["name"]] = location

        for key, arm in (("larg", "anchor"), ("rarg", "step")):
            if key in node:
                child = node[key]
                if not isinstance(child, dict) or "op" not in child:
                    raise ValueError("unexpected raw SELECT set operand")
                nested_contexts = [{**c, "arm": arm} if c["definition_byte_location"] == owner
                                   else c for c in contexts]
                query(child, visible, depth + 1, nested_contexts)

        def walk(value):
            if isinstance(value, list):
                for child in value:
                    walk(child)
            elif isinstance(value, dict):
                if "SelectStmt" in value:
                    query(value["SelectStmt"], visible, depth + 1, contexts)
                    return
                if "RangeVar" in value:
                    relation = value["RangeVar"]
                    if relation.get("catalogname"):
                        raise ValueError("database-qualified relation outside this source population")
                    parts = ([relation["schemaname"]] if relation.get("schemaname") else []) + [relation["relname"]]
                    references.append({
                        "parts": parts, "byte_location": relation.get("location"),
                        "definition_byte_location": visible.get(parts[0]) if len(parts) == 1 else None,
                        "contexts": contexts,
                    })
                    return
                for kind, child in value.items():
                    if kind in {"SubLink", "RangeFunction", "RangeTableSample", "WindowDef", "CollateClause"}:
                        dependencies[kind] += 1
                    if kind == "RangeSubselect" and child.get("lateral"):
                        dependencies["lateral"] += 1
                    if kind == "ParamRef":
                        if type(child.get("location")) is not int or child["location"] < 0:
                            raise ValueError("parameter lacks its source position")
                        parameters.append((child["location"], child["number"]))
                    if kind == "FuncCall":
                        functions.add(".".join(n["String"]["sval"] for n in child["funcname"]))
                    walk(child)
        # JoinExpr larg/rarg are ordinary expressions within fromClause, while
        # SelectStmt larg/rarg above are raw SELECTs with their own WITH scopes.
        walk({k: v for k, v in node.items() if k not in {"withClause", "larg", "rarg"}})

    query(parsed["SelectStmt"], {}, 0, [])
    for entry in definitions:
        location = entry["byte_location"]
        contexts = [c for r in references if r["definition_byte_location"] == location
                    for c in r["contexts"] if c["definition_byte_location"] == location]
        entry.update(self_references=len(contexts),
                     anchor_references=sum(c["arm"] == "anchor" for c in contexts),
                     step_references=sum(c["arm"] == "step" for c in contexts))
    for name in functions:
        dependencies["aggregate" if name.rsplit(".", 1)[-1] in
                     {"count", "sum", "avg", "min", "max", "array_agg", "string_agg",
                      "bool_and", "bool_or"} else "function_calls"] += 1
    result = {
        "ctes": definitions, "relations": references,
        "parameter_slots": list(dict.fromkeys(n for _, n in sorted(parameters))),
        "source_free": not parameters and all(r["definition_byte_location"] is not None for r in references),
        "dependencies": dict(sorted(dependencies.items())), "functions": sorted(functions),
        "actual_recursive_count": sum(bool(c["self_references"]) for c in definitions),
    }
    validate_observation(result, sql)
    return result


def oracle(sql):
    import pglast
    from pglast import parser
    if pglast.__version__ != "v7.21":
        raise ValueError("source observation oracle requires pinned pglast v7.21")
    statements = json.loads(parser.parse_sql_json(sql))["stmts"]
    if len(statements) != 1:
        raise ValueError("source must contain one complete statement")
    return observe_recursive(statements[0]["stmt"], sql)
