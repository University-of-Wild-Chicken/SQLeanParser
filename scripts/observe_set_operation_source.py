"""Raw PostgreSQL-tree observations; no catalog lookup or inferred output types."""
from __future__ import annotations

from collections import Counter

from observe_qualified_name_source import source_name

FACTORS = {"union", "intersect", "except"}


def validate_observation(observation, factor, sql=None):
    if (factor not in FACTORS or set(observation) != {
            "set_operations", "relations", "source_free", "dependencies", "parameter_slots"}
            or type(observation["source_free"]) is not bool
            or not isinstance(observation["set_operations"], list)
            or not observation["set_operations"]):
        raise ValueError("invalid set-operation observations")
    seen = set()
    for entry in observation["set_operations"]:
        if (set(entry) != {"operator", "all", "path", "order_items", "limit", "offset"}
                or entry["operator"] not in FACTORS or type(entry["all"]) is not bool
                or not isinstance(entry["path"], str) or not entry["path"].startswith("$")
                or entry["path"] in seen or type(entry["order_items"]) is not int
                or entry["order_items"] < 0 or type(entry["limit"]) is not bool
                or type(entry["offset"]) is not bool):
            raise ValueError("invalid set-operation tree observation")
        seen.add(entry["path"])
    if factor not in {entry["operator"] for entry in observation["set_operations"]}:
        raise ValueError("query does not exercise its assigned syntactic factor")
    dependencies = observation["dependencies"]
    if (not isinstance(dependencies, dict)
            or not set(dependencies) <= {"aggregate", "distinct", "scalar_subquery"}
            or any(type(n) is not int or n < 1 for n in dependencies.values())):
        raise ValueError("unregistered set-operation prerequisite")
    slots = observation["parameter_slots"]
    if (not isinstance(slots, list) or any(type(n) is not int or n < 1 for n in slots)
            or slots != sorted(set(slots))):
        raise ValueError("invalid set-operation parameter observation")
    relations = observation["relations"]
    if not isinstance(relations, list):
        raise ValueError("invalid relation observations")
    positions = set()
    for entry in relations:
        if (set(entry) != {"parts", "byte_location", "cte"}
                or not isinstance(entry["parts"], list) or len(entry["parts"]) not in {1, 2}
                or any(not isinstance(p, str) or not p for p in entry["parts"])
                or type(entry["byte_location"]) is not int or entry["byte_location"] < 0
                or entry["byte_location"] in positions or type(entry["cte"]) is not bool
                or entry["cte"] and len(entry["parts"]) != 1):
            raise ValueError("invalid set-operation relation observation")
        if sql is not None and source_name(sql, entry["byte_location"])["parts"] != entry["parts"]:
            raise ValueError("relation observation differs from source spelling")
        positions.add(entry["byte_location"])
    if observation["source_free"] != (not slots and all(r["cte"] for r in relations)):
        raise ValueError("source-free observation disagrees with relation/input footprint")


def observe(parsed, sql, factor):
    if not isinstance(parsed, dict) or set(parsed) != {"SelectStmt"}:
        raise ValueError("set-operation input must be one SELECT")
    operations, relations, slots, dependencies = [], [], set(), Counter()

    def query(node, outer, path):
        if any(node.get(k) for k in ("valuesLists", "groupClause", "havingClause", "windowClause",
                                     "intoClause", "lockingClause")):
            raise ValueError("unselected VALUES/group/window/utility/locking prerequisite")
        if node.get("distinctClause"):
            if node["distinctClause"] != [{}]:
                raise ValueError("DISTINCT ON is outside this source population")
            dependencies["distinct"] += 1
        visible, local = set(outer), set()
        with_ = node.get("withClause", {})
        if with_.get("recursive"):
            raise ValueError("recursive WITH is outside this population")
        for i, wrapper in enumerate(with_.get("ctes", [])):
            cte = wrapper["CommonTableExpr"]
            if (cte.get("ctematerialized", "CTEMaterializeDefault") != "CTEMaterializeDefault"
                    or set(cte["ctequery"]) != {"SelectStmt"} or cte["ctename"] in local
                    or cte.get("search_clause") or cte.get("cycle_clause")):
                raise ValueError("unselected CTE prerequisite")
            query(cte["ctequery"]["SelectStmt"], visible, f"{path}.cte[{i}]")
            visible.add(cte["ctename"])
            local.add(cte["ctename"])
        op = node.get("op", "SETOP_NONE")
        if op != "SETOP_NONE":
            operator = op.removeprefix("SETOP_").lower()
            if operator not in FACTORS or not isinstance(node.get("larg"), dict) or not isinstance(node.get("rarg"), dict):
                raise ValueError("malformed set-operation tree")
            operations.append({
                "operator": operator, "all": bool(node.get("all", False)), "path": path,
                "order_items": len(node.get("sortClause", [])),
                "limit": node.get("limitCount") is not None, "offset": node.get("limitOffset") is not None,
            })
            query(node["larg"], visible, path + ".left")
            query(node["rarg"], visible, path + ".right")

        def walk(value, position):
            if isinstance(value, list):
                for i, child in enumerate(value):
                    walk(child, f"{position}[{i}]")
            elif isinstance(value, dict):
                if "SelectStmt" in value:
                    query(value["SelectStmt"], visible, position + ".query")
                    return
                if "RangeVar" in value:
                    rel = value["RangeVar"]
                    if rel.get("catalogname"):
                        raise ValueError("database-qualified relation is outside this population")
                    parts = ([rel["schemaname"]] if rel.get("schemaname") else []) + [rel["relname"]]
                    relations.append({"parts": parts, "byte_location": rel.get("location"),
                                      "cte": len(parts) == 1 and parts[0] in visible})
                    return
                for kind, child in value.items():
                    if kind in {"RangeFunction", "RangeTableSample", "WindowDef", "CollateClause",
                                "InsertStmt", "UpdateStmt", "DeleteStmt", "MergeStmt"}:
                        raise ValueError("unselected set-operation dependency")
                    if kind == "RangeSubselect" and child.get("lateral"):
                        raise ValueError("LATERAL is outside this population")
                    if kind == "FuncCall":
                        if ([n["String"]["sval"] for n in child["funcname"]] != ["count"]
                                or not child.get("agg_star") or child.get("over")
                                or child.get("agg_order") or child.get("agg_filter")):
                            raise ValueError("unselected ordinary or aggregate call")
                        dependencies["aggregate"] += 1
                    if kind == "SubLink":
                        if child.get("subLinkType") != "EXPR_SUBLINK":
                            raise ValueError("only the two recorded scalar-subquery prerequisites are admitted")
                        dependencies["scalar_subquery"] += 1
                    if kind == "ParamRef":
                        slots.add(child["number"])
                    walk(child, position + "." + kind)
        # larg/rarg are also JoinExpr field names; exclude only this SELECT's
        # already visited set children, never similarly named nested fields.
        walk({k: v for k, v in node.items() if k not in {"withClause", "larg", "rarg"}}, path)

    query(parsed["SelectStmt"], set(), "$")
    result = {"set_operations": operations, "relations": relations,
              "source_free": not slots and all(r["cte"] for r in relations),
              "dependencies": dict(sorted(dependencies.items())), "parameter_slots": sorted(slots)}
    validate_observation(result, factor, sql)
    return result


def oracle(sql, factor):
    import json
    import pglast
    from pglast import parser
    if pglast.__version__ != "v7.21":
        raise ValueError("source oracle requires pglast v7.21")
    statements = json.loads(parser.parse_sql_json(sql))["stmts"]
    if len(statements) != 1:
        raise ValueError("source must contain exactly one statement")
    return observe(statements[0]["stmt"], sql, factor)
