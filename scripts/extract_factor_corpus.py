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
    NEW_FAMILIES, OLD_FAMILIES, parameter_slots, select_sql,
)
from extract_pagination_corpus import checked_file, comparison_key, sha256
from extract_statement_corpus import selected_sql, statement_spans
from extract_tcl_sql import selected_tcl_sql

ROOT = Path(__file__).resolve().parents[1]
POPULATIONS = {
    "functions": {"hatchet": 20, "sqlc": 10, "postgres": 20},
    "conditional": {"hatchet": 11, "sqlc": 13, "postgres": 26},
    "locking": {"temporal": 15, "hatchet": 8, "sqlc": 2, "postgres": 25},
    "join_contract": {"hatchet": 1, "sqlc": 19, "postgres": 30},
    "using_contract": {"postgres": 16, "sqlc": 3, "sqlite": 31},
    "natural_contract": {"postgres": 6, "sqlite": 44},
    "derived_contract": {"postgres": 47, "sqlc": 3},
}
CONDITIONAL_FORMS = {"searched-case", "simple-case", "coalesce", "nullif", "greatest", "least"}
AGGREGATES = {"count", "sum", "avg", "min", "max"}
LOCK_STRENGTHS = {"update", "no-key-update", "share", "key-share"}
LOCK_POLICIES = {"default", "nowait", "skip-locked"}
JOIN_KINDS = {"cross", "inner", "left", "right", "full"}
MERGED_FACTORS = {"using_contract": "using", "natural_contract": "natural"}
JOIN_FACTORS = {"join_contract", *MERGED_FACTORS}


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
                    or node.arrayBounds):
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
    if factor in {"conditional", "locking", "derived_contract"} | JOIN_FACTORS:
        allowed.add("conditional-expression")
    if factor == "locking":
        allowed.add("row-locking")
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
            if factor in {"locking", "derived_contract"} | JOIN_FACTORS:
                spans[key] = statement_spans(files[key]) if entry["path"].endswith(".sql") else []
    records, used = [], set()
    for selection in manifest["selections"]:
        name, path = selection["source"], selection["path"]
        key = (name, path)
        if key not in files:
            raise ValueError("selection has no pinned source input")
        used.add(key)
        if selection["selector"]["kind"] == "tcl_sql_statement":
            if factor not in MERGED_FACTORS or name != "sqlite":
                raise ValueError("Tcl SQL selection is outside its explicit source factors")
            sql, line, detail = selected_tcl_sql(files[key], selection["selector"])
        elif factor in {"locking", "derived_contract"} | JOIN_FACTORS:
            sql, line, detail = selected_sql(files[key], selection["selector"], spans[key])
        else:
            sql, line, detail = select_sql(files[key], selection["selector"])
        if sha256(sql.encode()) != selection["sql_sha256"]:
            raise ValueError("selected SQL hash mismatch")
        metadata = manifest["sources"][name]
        suffix = (f"tcl-{detail['command_start']}-statement-{detail['statement_index']}"
                  if detail.get("extraction") == "tcl_sql_statement"
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
