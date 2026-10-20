"""Finite lexical observations for unchanged nonrecursive SELECT CTE sources.

This resolves relation spellings against visible CTE definitions only. It
neither consults an application catalog nor infers output/column types.
"""
from __future__ import annotations

from observe_qualified_name_source import source_name


def validate_ctes(observation, sql=None):
    definitions, references = observation.get("ctes"), observation.get("cte_relations")
    if (not isinstance(definitions, list) or not definitions or not isinstance(references, list)
            or type(observation.get("source_free")) is not bool):
        raise ValueError("missing nonrecursive CTE source observations")
    locations = {}
    for entry in definitions:
        if (set(entry) != {"name", "column_aliases", "byte_location", "query_depth", "shadows_visible"}
                or not isinstance(entry["name"], str) or not entry["name"]
                or not isinstance(entry["column_aliases"], list)
                or any(not isinstance(n, str) or not n for n in entry["column_aliases"])
                or type(entry["byte_location"]) is not int or entry["byte_location"] < 0
                or type(entry["query_depth"]) is not int or entry["query_depth"] < 0
                or type(entry["shadows_visible"]) is not bool
                or entry["byte_location"] in locations):
            raise ValueError("invalid CTE definition observation")
        if sql is not None and source_name(sql, entry["byte_location"])["parts"] != [entry["name"]]:
            raise ValueError("CTE name differs from its source byte position")
        locations[entry["byte_location"]] = entry["name"]
    seen = set()
    for entry in references:
        if (set(entry) != {"parts", "byte_location", "definition_byte_location"}
                or not isinstance(entry["parts"], list) or len(entry["parts"]) not in {1, 2}
                or any(not isinstance(n, str) or not n for n in entry["parts"])
                or type(entry["byte_location"]) is not int or entry["byte_location"] < 0
                or entry["byte_location"] in seen):
            raise ValueError("invalid CTE relation observation")
        definition = entry["definition_byte_location"]
        if definition is not None and (type(definition) is not int or definition not in locations
                                       or len(entry["parts"]) != 1
                                       or entry["parts"][0] != locations[definition]):
            raise ValueError("reference does not name a recorded CTE definition")
        if sql is not None and source_name(sql, entry["byte_location"])["parts"] != entry["parts"]:
            raise ValueError("relation name differs from its source byte position")
        seen.add(entry["byte_location"])
    if observation["source_free"] and any(e["definition_byte_location"] is None for e in references):
        raise ValueError("an external relation cannot be marked source-free")


def observe_ctes(parsed, sql):
    if not isinstance(parsed, dict) or set(parsed) != {"SelectStmt"}:
        raise ValueError("CTE source must be one SELECT")
    definitions, references, parameters = [], [], []

    def query(node, outer, depth):
        if (node.get("op", "SETOP_NONE") != "SETOP_NONE"
                or any(node.get(k) for k in ("valuesLists", "groupClause", "havingClause",
                                            "distinctClause", "windowClause", "intoClause"))):
            raise ValueError("set, grouped, VALUES or utility query is outside this population")
        with_ = node.get("withClause", {})
        if with_.get("recursive"):
            raise ValueError("recursive syntax is outside the nonrecursive CTE population")
        visible, local = dict(outer), set()
        for wrapper in with_.get("ctes", []):
            if set(wrapper) != {"CommonTableExpr"}:
                raise ValueError("unexpected CTE definition node")
            cte = wrapper["CommonTableExpr"]
            if (cte.get("ctematerialized", "CTEMaterializeDefault") != "CTEMaterializeDefault"
                    or set(cte["ctequery"]) != {"SelectStmt"} or cte.get("search_clause")
                    or cte.get("cycle_clause") or cte["ctename"] in local):
                raise ValueError("materialized, modifying, duplicate or recursive CTE is outside this population")
            location, name = cte.get("location"), cte["ctename"]
            definitions.append({
                "name": name, "column_aliases": [n["String"]["sval"] for n in cte.get("aliascolnames", [])],
                "byte_location": location, "query_depth": depth, "shadows_visible": name in visible,
            })
            # Nonrecursive siblings become visible only after their definition;
            # a same-named outer CTE remains visible inside a shadowing definition.
            query(cte["ctequery"]["SelectStmt"], visible, depth + 1)
            visible[name] = location
            local.add(name)

        def walk(value):
            if isinstance(value, list):
                for child in value:
                    walk(child)
            elif isinstance(value, dict):
                if "SelectStmt" in value:
                    query(value["SelectStmt"], visible, depth + 1)
                    return
                if "RangeVar" in value:
                    relation = value["RangeVar"]
                    if relation.get("catalogname"):
                        raise ValueError("database-qualified source is outside this population")
                    parts = ([relation["schemaname"]] if relation.get("schemaname") else []) + [relation["relname"]]
                    references.append({
                        "parts": parts, "byte_location": relation.get("location"),
                        "definition_byte_location": visible.get(parts[0]) if len(parts) == 1 else None,
                    })
                    return
                for kind, child in value.items():
                    if kind in {"SubLink", "RangeFunction", "RangeTableSample", "WindowDef", "CollateClause",
                                "InsertStmt", "UpdateStmt", "DeleteStmt", "MergeStmt", "FuncCall"}:
                        raise ValueError("unselected expression/function dependency in CTE source")
                    if kind == "RangeSubselect" and child.get("lateral"):
                        raise ValueError("LATERAL is outside this source population")
                    if kind == "ParamRef":
                        parameters.append(child["number"])
                    if kind != "withClause":
                        walk(child)
        walk(node)

    query(parsed["SelectStmt"], {}, 0)
    result = {
        "ctes": definitions, "cte_relations": references,
        "source_free": not parameters and all(r["definition_byte_location"] is not None for r in references),
    }
    validate_ctes(result, sql)
    return result
