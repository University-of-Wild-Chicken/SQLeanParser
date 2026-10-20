#!/usr/bin/env python3
"""Reproduce unchanged COLLATE queries and their written declaration context.

All default checks are offline. --oracle recomputes raw-parser observations
with pinned pglast 7.21. Neither path executes SQL, setup, or psql controls.
"""
from __future__ import annotations

import argparse
from collections import Counter
import json
from pathlib import Path
import re

from extract_pagination_corpus import checked_file, comparison_key, sha256
from extract_statement_corpus import selected_sql, statement_spans
from observe_collation_source import oracle, validate_observation

ROOT = Path(__file__).resolve().parents[1]
DIRECTORY = ROOT / "fixtures/collations"
PIN = "f0595c3d839debdb140903621c1b44a4f4d86256"
SOURCE_COUNTS = {
    "src/test/regress/sql/collate.icu.utf8.sql": 37,
    "src/test/regress/sql/collate.linux.utf8.sql": 10,
    "src/test/regress/sql/collate.sql": 3,
}
CONTEXT_SHA256 = "20c57b8317d9127fe1c086ddaedaca83ff8a9b2f64e2c9af604bd568a53d58b2"


def context_id(path, index):
    return f"collations:postgres:{path}:context-statement-{index}"


def selected_declaration(source, selector, spans):
    if selector["kind"] == "sql_slice":
        return selected_sql(source, selector, spans)
    keys = {"kind", "container_start", "start", "end", "statement_index"}
    if (set(selector) != keys or selector["kind"] != "psql_describe_then_declaration"
            or any(type(selector[k]) is not int for k in keys - {"kind"})):
        raise ValueError("invalid declaration container selector")
    container, start, end, index = (selector[k] for k in
                                    ("container_start", "start", "end", "statement_index"))
    if (not 0 <= index < len(spans) or spans[index] != (container, end)
            or not container < start < end):
        raise ValueError("declaration is not within its pinned complete source container")
    prefix, sql = source[container:start], source[start:end]
    # Exactly one retained psql describe command precedes the selected CREATE
    # TABLE in this finite source population. The command is data, not executed.
    if (re.fullmatch(r"\\d collate_test_like\r?\n[ \t\r\n]*", prefix) is None
            or not sql.startswith("CREATE TABLE collate_test2 (")
            or statement_spans(sql) != [(0, len(sql))]):
        raise ValueError("unselected psql prefix or incomplete declaration")
    return sql, source.count("\n", 0, start) + 1, {
        "statement_index": index, "source_start": start, "source_end": end,
        "container_start": container, "source_prefix": prefix,
        "extraction": "unchanged CREATE TABLE following retained psql describe command",
    }


def source_context(row, contexts):
    """Link written declarations without claiming they executed or resolved."""
    available = [c for c in contexts if c["source_file"] == row["source_file"]
                 and c["source_end"] <= row["source_start"]]
    declarations = {}
    for entry in available:
        value = entry["observed_declaration"]
        if value["kind"] in {"table", "collation"}:
            declarations[(value["kind"], tuple(value["name"]))] = entry
    relations = []
    names = {}
    for entry in row["observed_syntax"]["collations"]:
        names.setdefault(tuple(entry["parts"]), set()).add("explicit-expression")
    for entry in row["observed_syntax"]["relations"]:
        key = tuple(entry["parts"])
        declaration = declarations.get(("table", key))
        if declaration is None:
            raise ValueError("selected relation has no preceding written source declaration")
        binding = {"parts": entry["parts"], "declaration_id": declaration["id"]}
        if binding not in relations:
            relations.append(binding)
        for column in declaration["observed_declaration"]["columns"]:
            if column["written_collation"] is not None:
                names.setdefault(tuple(column["written_collation"]), set()).add("table-field")
    collations = []
    for name, uses in sorted(names.items()):
        declaration = declarations.get(("collation", name))
        collations.append({
            "parts": list(name), "uses": sorted(uses),
            "declaration_id": declaration["id"] if declaration is not None else None,
            "origin": "written-create-collation" if declaration is not None else "unresolved-catalog-reference",
            "runtime_catalog_resolution": "not-performed",
        })
    session = [c["id"] for c in available if c["observed_declaration"]["kind"] in {"schema", "search_path"}]
    if len(session) != 2:
        raise ValueError("expected the original schema/search_path declaration pair")
    return {"session_declaration_ids": session, "relation_declarations": relations,
            "collation_dependencies": collations,
            "preamble_id": "collations:postgres:" + row["source_file"] + ":preamble"}


def validate_context(context):
    if (set(context) != {"declarations", "preambles"}
            or sha256(json.dumps(context, sort_keys=True, separators=(",", ":")).encode()) != CONTEXT_SHA256):
        raise ValueError("fixed written declaration/preamble provenance changed")
    if (len(context["declarations"]) != 28 or len(context["preambles"]) != 3
            or Counter(c["observed_declaration"]["kind"] for c in context["declarations"])
            != {"collation": 14, "table": 8, "schema": 3, "search_path": 3}):
        raise ValueError("written source declaration inventory changed")


def validate_population(records, contexts):
    if (len(records) != 50 or Counter(r["source_file"] for r in records) != SOURCE_COUNTS
            or any(len({r[k] for r in records}) != 50 for k in ("id", "sql"))
            or len({comparison_key(r["sql"]).rstrip(";").strip() for r in records}) != 50):
        raise ValueError("fixed COLLATE source identity/population changed")
    for row in records:
        validate_observation(row["observed_syntax"], row["sql"])
        if (row["source"] != "postgres" or row["commit"] != PIN
                or row["source_kind"] != "engine-regression"
                or row["sql"] != row["raw_sql"] or row["transformations"] != []
                or row["observed_parameter_slots"] != [] or row["parameter_types"] is not None
                or row["application_schema_validity"] != "not-claimed"
                or "parameter_values" in row or "expected_value" in row):
            raise ValueError("source SQL or catalog/runtime assumptions changed")
        if row["declaration_provenance"] != source_context(row, contexts):
            raise ValueError("query declaration provenance disagrees with retained source context")
    if (sum(r["observed_syntax"]["source_free"] for r in records) != 34
            or sum(len(r["observed_syntax"]["collations"]) for r in records) != 67
            or len({tuple(c["parts"]) for r in records for c in r["observed_syntax"]["collations"]}) != 26):
        raise ValueError("fixed 67-clause/34-closed COLLATE population changed")


def extract(manifest, root=ROOT):
    if (manifest.get("format_version") != 1 or manifest.get("factor") != "collations"
            or manifest.get("expected_count") != 50 or manifest.get("expected_files") != SOURCE_COUNTS
            or set(manifest.get("sources", {})) != {"postgres"}):
        raise ValueError("unexpected collation source manifest")
    metadata = manifest["sources"]["postgres"]
    if metadata["commit"] != PIN or metadata["license"] != "PostgreSQL":
        raise ValueError("unexpected PostgreSQL source pin/license")
    checked_file(root, metadata["license_file"], metadata["license_sha256"])
    files, spans = {}, {}
    for entry in metadata["files"]:
        path = entry["path"]
        if path in files or path not in SOURCE_COUNTS:
            raise ValueError("unexpected or duplicate pinned source file")
        files[path] = checked_file(root, entry["local_path"], entry["sha256"]).decode("utf-8")
        spans[path] = statement_spans(files[path])
    if set(files) != set(SOURCE_COUNTS):
        raise ValueError("missing pinned collation source")
    contexts = []
    for selection in manifest["declaration_contexts"]:
        path = selection["path"]
        sql, line, detail = selected_declaration(files[path], selection["selector"], spans[path])
        if sha256(sql.encode()) != selection["sql_sha256"]:
            raise ValueError("original declaration SQL hash mismatch")
        contexts.append({
            "id": context_id(path, detail["statement_index"]), "source_file": path, "line": line,
            "source_url": f"{metadata['repository']}/blob/{PIN}/{path}#L{line}",
            **detail, "sql": sql, "sql_sha256": selection["sql_sha256"],
            "observed_declaration": selection["observed_declaration"],
            "execution": "not-performed", "runtime_catalog_resolution": "not-performed",
        })
    if len({c["id"] for c in contexts}) != len(contexts):
        raise ValueError("duplicate source declaration")
    preambles = []
    for selection in manifest["preambles"]:
        path, end = selection["path"], selection["end"]
        schemas = [c for c in contexts if c["source_file"] == path
                   and c["observed_declaration"]["kind"] == "schema"]
        if (selection["start"] != 0 or len(schemas) != 1 or type(end) is not int
                or end != schemas[0]["source_start"]):
            raise ValueError("preamble must end at the first retained CREATE SCHEMA statement")
        text = files[path][:end]
        if sha256(text.encode()) != selection["sha256"]:
            raise ValueError("source preamble hash mismatch")
        preambles.append({
            "id": f"collations:postgres:{path}:preamble", "source_file": path,
            "start": 0, "end": end, "text": text, "sha256": selection["sha256"],
            "execution": "not-performed",
        })
    if {p["source_file"] for p in preambles} != set(files) or len(preambles) != 3:
        raise ValueError("missing original environment preamble")
    context = {"declarations": contexts, "preambles": preambles}
    validate_context(context)
    records = []
    for selection in manifest["selections"]:
        path = selection["path"]
        sql, line, detail = selected_sql(files[path], selection["selector"], spans[path])
        if sha256(sql.encode()) != selection["sql_sha256"]:
            raise ValueError("original query SQL hash mismatch")
        row = {
            "id": f"collations:postgres:{path}:statement-{detail['statement_index']}",
            "factor": "collations", "source": "postgres", "source_kind": "engine-regression",
            "source_file": path, "line": line, **detail,
            "source_url": f"{metadata['repository']}/blob/{PIN}/{path}#L{line}",
            "commit": PIN, "license": "PostgreSQL",
            "observed_syntax": selection["observed_syntax"],
            "observed_parameter_slots": [], "parameter_types": None,
            "application_schema_validity": "not-claimed",
            "raw_sql": sql, "sql": sql, "sql_sha256": selection["sql_sha256"], "transformations": [],
        }
        row["declaration_provenance"] = source_context(row, contexts)
        records.append(row)
    validate_population(records, contexts)
    return records, context


def render(records):
    return "".join(json.dumps(row, ensure_ascii=False) + "\n" for row in records)


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--check", action="store_true")
    parser.add_argument("--oracle", action="store_true")
    args = parser.parse_args()
    records, context = extract(json.loads((DIRECTORY / "concrete_sources.json").read_text()))
    from collation_source_contracts import load_observed_source_contracts
    load_observed_source_contracts()
    if args.oracle:
        for row in records:
            if oracle(row["sql"]) != row["observed_syntax"]:
                raise ValueError(f"{row['id']}: COLLATE raw-tree observation changed")
        for row in context["declarations"]:
            if oracle(row["sql"], declaration=True) != row["observed_declaration"]:
                raise ValueError(f"{row['id']}: written declaration observation changed")
    outputs = {
        DIRECTORY / "concrete.jsonl": render(records),
        DIRECTORY / "declaration_contexts.json": json.dumps(context, indent=2, ensure_ascii=False) + "\n",
    }
    for path, content in outputs.items():
        if args.check:
            if not path.exists() or path.read_text() != content:
                raise ValueError(f"stale collation source output: {path.name}")
        else:
            path.write_text(content)
    print("collations: 50 unchanged queries, 67 COLLATE clauses, retained declaration context"
          + ("; pinned raw-parser observations verified" if args.oracle else ""))
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
