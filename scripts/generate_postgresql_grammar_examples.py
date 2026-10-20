#!/usr/bin/env python3
"""Generate bounded grammar-derived examples, never execute their SQL.

The requested target is 50 statements per outer family. Distinct parameter,
identifier, and literal values count as separate examples; whitespace, comments,
and keyword casing do not. Families with fewer available spellings retain an
explicit shortfall. Structural template counts are reported separately.
"""
from __future__ import annotations

import argparse
from collections import defaultdict
import hashlib
import json
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
FIXTURES = ROOT / "fixtures/postgresql_grammar"
TARGET = 50


def grammar():
    document = json.loads((FIXTURES / "inventory.json").read_text())
    rules = document["productions"]
    by_lhs = defaultdict(list)
    for rule in rules:
        by_lhs[rule["lhs"]].append(rule)
    # Minimize terminal count, then derivation height; the second component
    # prevents zero-token recursive alternatives from creating infinite trees.
    ranks, chosen = {}, {}
    for _ in range(len(by_lhs) + 1):
        changed = False
        for rule in rules:
            if any(symbol in by_lhs and symbol not in ranks for symbol in rule["rhs"]):
                continue
            children = [ranks[s] if s in by_lhs else (1, 0) for s in rule["rhs"]]
            rank = (sum(x[0] for x in children), 1 + max((x[1] for x in children), default=0))
            if rule["lhs"] not in ranks or rank < ranks[rule["lhs"]]:
                ranks[rule["lhs"]], chosen[rule["lhs"]] = rank, rule
                changed = True
        if not changed:
            break
    if set(ranks) != set(by_lhs):
        raise ValueError("grammar contains an unproductive nonterminal")
    return document, by_lhs, ranks, chosen


def tree(rule, by_lhs, chosen):
    return (rule["id"], tuple(
        tree(chosen[symbol], by_lhs, chosen) if symbol in by_lhs else symbol
        for symbol in rule["rhs"]))


def production_ids(node):
    if isinstance(node, str):
        return []
    return [node[0]] + [p for child in node[1] for p in production_ids(child)]


def terminals(node):
    if isinstance(node, str):
        return [node]
    return [terminal for child in node[1] for terminal in terminals(child)]


def replacements(node, by_lhs, chosen, rules, depth=0):
    if isinstance(node, str) or depth > 10:
        return
    current = rules[node[0]]
    for alternative in by_lhs[current["lhs"]]:
        if alternative["id"] != node[0]:
            yield tree(alternative, by_lhs, chosen)
    for index, child in enumerate(node[1]):
        for replacement in replacements(child, by_lhs, chosen, rules, depth + 1):
            children = list(node[1])
            children[index] = replacement
            yield (node[0], tuple(children))


def templates(family, by_lhs, chosen, rules):
    initial = [tree(rule, by_lhs, chosen) for rule in by_lhs[family]]
    result, seen = [], set()
    # A breadth-first single-subtree mutation explores whole root alternatives
    # before optional clauses and nested alternatives. This is not exhaustive.
    queue = list(initial)
    while queue and len(result) < 160:
        candidate = queue.pop(0)
        key = tuple(production_ids(candidate))
        if key in seen or len(terminals(candidate)) > 100:
            continue
        seen.add(key)
        result.append(candidate)
        if len(result) <= 24:
            queue.extend(replacements(candidate, by_lhs, chosen, rules))
    return result


def spell(tokens, keywords, variant):
    special = {
        "IDENT": f"witness_{variant}", "SCONST": f"'value_{variant}'",
        "ICONST": str(variant), "FCONST": f"{variant}.25", "PARAM": f"${variant}",
        "BCONST": "B'" + format(variant, "b") + "'",
        "XCONST": "X'" + format(variant, "x") + "'",
        "Op": "~", "TYPECAST": "::", "DOT_DOT": "..", "COLON_EQUALS": ":=",
        "EQUALS_GREATER": "=>", "LESS_EQUALS": "<=", "GREATER_EQUALS": ">=",
        "NOT_EQUALS": "<>", "FORMAT_LA": "FORMAT", "NOT_LA": "NOT",
        "NULLS_LA": "NULLS", "WITH_LA": "WITH", "WITHOUT_LA": "WITHOUT",
    }
    result = []
    for token in tokens:
        if token in special:
            result.append(special[token])
        elif token in keywords:
            result.append(keywords[token].upper())
        elif token.startswith("'") and token.endswith("'"):
            result.append(token[1:-1])
        else:
            raise ValueError(f"non-source terminal in ordinary statement: {token}")
    return " ".join(result) + ";"


def build():
    document, by_lhs, _, chosen = grammar()
    rules = document["productions"]
    keywords = {k["token"]: k["spelling"] for k in document["keywords"]}
    cases, coverage = [], []
    for family in document["statement_families"]:
        name = family["name"]
        patterns = templates(name, by_lhs, chosen, rules)
        family_cases, seen = [], set()
        for variant in range(1, TARGET + 1):
            for pattern in patterns:
                sql = spell(terminals(pattern), keywords, variant)
                if sql in seen:
                    continue
                seen.add(sql)
                ids = production_ids(pattern)
                template = hashlib.sha256(json.dumps(ids).encode()).hexdigest()[:16]
                family_cases.append({
                    "id": f"grammar-{name}-{len(family_cases) + 1:03}",
                    "source": "synthetic:pinned-grammar", "grammar_family": name,
                    "sql": sql, "grammar_template": template,
                    "grammar_rule_ids": ids, "static_validity": "not-claimed",
                    "upstream_action_status": "not-checked",
                })
                if len(family_cases) == TARGET:
                    break
            if len(family_cases) == TARGET:
                break
        count = len(family_cases)
        coverage.append({
            "grammar_family": name, "target": TARGET, "examples": count,
            "structural_templates": len({c["grammar_template"] for c in family_cases}),
            "shortfall": TARGET - count,
            "note": ("Finite generator found fewer distinct nontrivia spellings; "
                     "keyword-case/comment/whitespace padding is excluded.") if count < TARGET else None,
        })
        cases.extend(family_cases)
    summary = {
        "upstream_commit": document["upstream"]["commit"],
        "postgresql_version": document["upstream"]["version"],
        "target_per_family": TARGET, "statement_families": len(coverage),
        "examples": len(cases), "structural_templates": sum(c["structural_templates"] for c in coverage),
        "families_meeting_target": sum(c["shortfall"] == 0 for c in coverage),
        "boundary": "Grammar-derived syntax examples only. C semantic actions, catalog/type validity, "
                    "execution, and universal renderer semantics are not established.",
        "families": coverage,
    }
    return cases, summary


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--check", action="store_true")
    args = parser.parse_args()
    cases, summary = build()
    for name, value in [("synthetic.json", cases), ("synthetic_inventory.json", summary)]:
        content = json.dumps(value, indent=2, ensure_ascii=False) + "\n"
        path = FIXTURES / name
        if args.check:
            if not path.is_file() or path.read_text() != content:
                raise SystemExit(f"stale generated grammar examples: {path}")
        else:
            path.write_text(content)
    print(f"PASS: {len(cases)} synthetic grammar examples across {len(summary['families'])} families; "
          f"{summary['families_meeting_target']} families reach {TARGET}")


if __name__ == "__main__":
    main()
