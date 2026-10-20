#!/usr/bin/env python3
"""Reproduce unchanged public statement-family witnesses and explicit gaps.

Default checks are offline and do not execute SQL. --oracle uses pinned pglast
7.21 only to reproduce raw-parser observations, which are not PG16 validity.
"""
from __future__ import annotations

import argparse
from collections import Counter
import json
from pathlib import Path
import re

from extract_extended_type_corpus import sql_code
from extract_pagination_corpus import (
    checked_file, comparison_key, extract_selection, sha256,
)

ROOT = Path(__file__).resolve().parents[1]
DIRECTORY = ROOT / "fixtures/statement_families"
COMMIT = "f0595c3d839debdb140903621c1b44a4f4d86256"


def statement_spans(source: str) -> list[tuple[int, int]]:
    """Complete semicolon-terminated SQL, retaining SQL routine bodies.

    This finite-source scanner masks quotes/comments, then keeps semicolons
    inside BEGIN ATOMIC bodies. CASE/END nesting prevents an expression's END
    from closing the routine body. It is not a psql script interpreter.
    """
    code = sql_code(source)
    tokens = list(re.finditer(r"[A-Za-z_][A-Za-z_0-9$]*|;", code))
    stack, spans, previous = [], [], 0
    for index, token in enumerate(tokens):
        word = token[0].upper()
        if (word == "BEGIN" and index + 1 < len(tokens)
                and tokens[index + 1][0].upper() == "ATOMIC"
                and not code[token.end():tokens[index + 1].start()].strip()):
            stack.append("atomic")
        elif word == "CASE" and stack:
            stack.append("case")
        elif word == "END" and stack:
            stack.pop()
        elif word == ";" and not stack:
            first = re.search(r"\S", code[previous:token.start()])
            if first:
                spans.append((previous + first.start(), token.end()))
            previous = token.end()
    if stack:
        raise ValueError("unterminated BEGIN ATOMIC routine body")
    return spans


def selected_sql(source: str, selector: dict, spans: list[tuple[int, int]]) -> tuple[str, int, dict]:
    if selector["kind"] == "go_constant":
        return extract_selection(source, selector)
    if selector["kind"] != "sql_slice":
        raise ValueError("unknown statement source selector")
    start, end, index = (selector[key] for key in ("start", "end", "statement_index"))
    if any(type(value) is not int for value in (start, end, index)):
        raise ValueError("SQL positions must be integers")
    if index < 0 or index >= len(spans) or spans[index] != (start, end):
        raise ValueError("selected SQL slice is not the pinned complete statement")
    return source[start:end], source.count("\n", 0, start) + 1, {
        "statement_index": index, "source_start": start, "source_end": end,
        "extraction": "unchanged complete SQL statement substring",
    }


def validate_population(positive: list[dict], negative: list[dict],
                        manifest: dict, families: dict[str, int]) -> None:
    if (len(positive) != manifest["expected_count"]
            or len(negative) != manifest["expected_negative_count"]):
        raise ValueError("statement population count changed")
    records = positive + negative
    for field in ("id", "sql"):
        if len({row[field] for row in records}) != len(records):
            raise ValueError(f"duplicate statement {field}")
    if len({comparison_key(row["sql"]) for row in records}) != len(records):
        raise ValueError("case/whitespace duplicate statement SQL")
    counts = Counter(row["grammar_family"] for row in positive)
    population = manifest["family_population"]
    if set(population) != set(families):
        raise ValueError("every pinned grammar family must have an explicit count")
    mined = manifest["mining_population"]
    if (not set(mined["outer_family_counts"]) <= set(families)
            or sum(mined["outer_family_counts"].values()) != mined["grammar_accepted"]
            or mined["unique_raw_parser_accepted"] !=
            mined["grammar_accepted"] + mined["grammar_rejected"]
            or mined["grammar_rejected"] != len(negative)):
        raise ValueError("inconsistent complete mining disposition")
    for family, entry in population.items():
        available, selected = entry["available"], entry["selected"]
        if (type(available) is not int or type(selected) is not int
                or available < 0 or selected != min(available, 50)
                or counts[family] != selected
                or available != mined["outer_family_counts"].get(family, 0)):
            raise ValueError(f"inconsistent source population for {family}")
    for row in records:
        if (not row["sql"].strip() or "\x00" in row["sql"]
                or row["raw_sql"] != row["sql"] or row["transformations"]):
            raise ValueError("concrete statement text was changed")
        if row["sql_sha256"] != sha256(row["sql"].encode()):
            raise ValueError("statement content digest changed")
        if row["static_validity"] != "not-claimed" or row["execution"] != "not-performed":
            raise ValueError("source corpus must not claim static validity or execution")
        if "parameter_types" in row or "parameter_values" in row:
            raise ValueError("application bindings must not be invented")
        if row["expected_status"] == "grammar-accepted":
            family = row["grammar_family"]
            if family not in families or row["entry_production"] != families[family]:
                raise ValueError("statement family/entry production changed")
        elif row["expected_status"] == "grammar-rejected":
            if row["grammar_family"] is not None or row["entry_production"] is not None:
                raise ValueError("negative source must not invent an accepted family")
            if not row["rejection_reason"] or not row["diagnostic_contains"]:
                raise ValueError("negative source must explain its expected rejection")
        else:
            raise ValueError("unexpected grammar disposition")


def extract(manifest: dict, root: Path = ROOT) -> tuple[list[dict], list[dict], dict]:
    if (manifest.get("format_version") != 1
            or manifest.get("factor") != "postgresql-statement-families"
            or manifest.get("per_family_limit") != 50):
        raise ValueError("unexpected statement source manifest")
    mining = manifest["mining_catalog"]
    checked_file(root, mining["path"], mining["sha256"])
    if manifest["mining_population"]["source_catalog_sha256"] != mining["sha256"]:
        raise ValueError("source mining population is not bound to its input catalog")
    grammar = manifest["grammar_inventory"]
    inventory = json.loads(checked_file(root, grammar["path"], grammar["sha256"]))
    if inventory["upstream"]["commit"] != COMMIT:
        raise ValueError("statement inventory does not use the pinned PG16 grammar")
    family_records = inventory["statement_families"]
    families = {row["name"]: row["entry_production"] for row in family_records}
    if len(families) != 125:
        raise ValueError("expected the pinned 125 outer statement families")
    files, spans = {}, {}
    for name, metadata in manifest["sources"].items():
        if not re.fullmatch(r"[0-9a-f]{40}", metadata["commit"]):
            raise ValueError("source revision is not a full commit pin")
        checked_file(root, metadata["license_file"], metadata["license_sha256"])
        for entry in metadata["files"]:
            key = (name, entry["path"])
            if key in files:
                raise ValueError("duplicate pinned source input")
            source = checked_file(root, entry["local_path"], entry["sha256"]).decode("utf-8")
            files[key] = source
            spans[key] = statement_spans(source) if entry["path"].endswith(".sql") else []
    records, used = [], set()
    for selection in manifest["selections"]:
        name, path = selection["source"], selection["path"]
        key = (name, path)
        if key not in files:
            raise ValueError("selection has no pinned source input")
        used.add(key)
        sql, line, detail = selected_sql(files[key], selection["selector"], spans[key])
        if sha256(sql.encode()) != selection["sql_sha256"]:
            raise ValueError("selected statement hash mismatch")
        metadata = manifest["sources"][name]
        suffix = detail.get("symbol", f"statement-{detail.get('statement_index')}")
        row = {
            "id": f"statement-family:{name}:{path}:{suffix}",
            "source": name, "source_kind": metadata["source_kind"],
            "source_file": path, "line": line,
            "source_url": f"{metadata['repository']}/blob/{metadata['commit']}/{path}#L{line}",
            "commit": metadata["commit"], "license": metadata["license"], **detail,
            "grammar_family": selection["grammar_family"],
            "entry_production": selection["entry_production"],
            "postgres_ast_kind": selection["postgres_ast_kind"],
            "expected_status": selection["expected_status"],
            "static_validity": "not-claimed", "execution": "not-performed",
            "raw_sql": sql, "sql": sql, "sql_sha256": selection["sql_sha256"],
            "transformations": [],
        }
        if selection["expected_status"] == "grammar-rejected":
            row["rejection_reason"] = selection["rejection_reason"]
            row["diagnostic_contains"] = selection["diagnostic_contains"]
        records.append(row)
    if used != set(files):
        raise ValueError("unused pinned source input")
    positive = [row for row in records if row["expected_status"] == "grammar-accepted"]
    negative = [row for row in records if row["expected_status"] == "grammar-rejected"]
    validate_population(positive, negative, manifest, families)
    summary = {
        "format_version": 1, "postgresql_grammar_commit": COMMIT,
        "scope": "finite unchanged source statements; no static validity or execution claim",
        "mining_population": manifest["mining_population"],
        "selected_count": len(positive), "negative_count": len(negative),
        "source_counts": dict(sorted(Counter(row["source"] for row in positive).items())),
        "families_with_fifty_sources": sum(x["selected"] == 50
                                          for x in manifest["family_population"].values()),
        "families_with_any_sources": sum(x["selected"] > 0
                                        for x in manifest["family_population"].values()),
        "families": [
            {"name": family["name"], "category": family["category"],
             "entry_production": family["entry_production"],
             **manifest["family_population"][family["name"]],
             "shortfall_to_fifty": 50 - manifest["family_population"][family["name"]]["selected"],
             "coverage_claim": "finite-witnesses-only"}
            for family in family_records
        ],
    }
    return positive, negative, summary


def oracle(records: list[dict]) -> None:
    import pglast
    from pglast import parser
    if pglast.__version__ != "v7.21":
        raise ValueError("statement oracle requires pglast v7.21")
    for row in records:
        statements = json.loads(parser.parse_sql_json(row["sql"]))["stmts"]
        if len(statements) != 1 or list(statements[0]["stmt"]) != [row["postgres_ast_kind"]]:
            raise ValueError(f"{row['id']}: PostgreSQL raw-parser observation changed")


def render(records: list[dict]) -> str:
    return "".join(json.dumps(row, ensure_ascii=False) + "\n" for row in records)


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--check", action="store_true")
    parser.add_argument("--oracle", action="store_true")
    args = parser.parse_args()
    manifest = json.loads((DIRECTORY / "concrete_sources.json").read_text())
    positive, negative, summary = extract(manifest)
    if args.oracle:
        # The negatives deliberately expose PG17-raw-parser/PG16-grammar
        # differences: their PG17 acceptance is also a pinned observation.
        oracle(positive + negative)
    outputs = {
        "concrete.jsonl": render(positive), "negative.jsonl": render(negative),
        "inventory.json": json.dumps(summary, ensure_ascii=False, indent=2) + "\n",
    }
    for name, text in outputs.items():
        path = DIRECTORY / name
        if args.check:
            if not path.is_file() or path.read_text() != text:
                raise ValueError(f"stale statement source artifact: {name}")
        else:
            path.write_text(text)
    print(f"{len(positive)} unchanged whole statements across "
          f"{summary['families_with_any_sources']}/125 families; "
          f"{summary['families_with_fifty_sources']} families have 50 sources; "
          f"{len(negative)} explicit negative witnesses")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
