#!/usr/bin/env python3
"""Reproduce 50 unchanged public inputs for each set-operation factor.

Offline extraction checks pinned bytes and complete source spans. The optional
oracle parses with pglast 7.21; neither mode executes SQL or source programs.
"""
from __future__ import annotations

import argparse
from collections import Counter
import json
from pathlib import Path
import re

from extract_extended_type_corpus import parameter_slots
from extract_pagination_corpus import checked_file, comparison_key, sha256
from extract_setop_sqllogic_sql import selected_setop_sqllogic
from extract_statement_corpus import selected_sql, statement_spans
from extract_tcl_sql import selected_tcl_sql
from observe_set_operation_source import FACTORS, oracle, validate_observation

ROOT = Path(__file__).resolve().parents[1]
DIRECTORY = ROOT / "fixtures/set_operations"
POPULATIONS = {
    "union": {"postgres": 20, "duckdb": 23, "sqlite": 7},
    "intersect": {"postgres": 17, "materialize": 11, "duckdb": 7, "sqlite": 14, "sqlc": 1},
    "except": {"postgres": 30, "materialize": 15, "duckdb": 4, "sqlc": 1},
}
SOURCE_COUNTS = dict(sum((Counter(p) for p in POPULATIONS.values()), Counter()))
REGISTRY_SHA256 = "cdcb59a9619748976cb6103fc02eacb9e855403ad4eb23c14e632db980579ec1"


def validate_registry(records, registry):
    """Bind the inspected output registry, separately from the syntax observer."""
    if (not isinstance(registry, dict) or set(registry) != FACTORS
            or sha256(json.dumps(registry, sort_keys=True, separators=(",", ":")).encode()) != REGISTRY_SHA256):
        raise ValueError("fixed independently inspected source output registry changed")
    by_id = {row["id"]: row for row in records}
    for factor, entries in registry.items():
        if len(entries) != (50 if factor == "union" else 6):
            raise ValueError("source certificate population changed")
        for entry in entries:
            source = by_id.get(entry["id"])
            if (set(entry) != {"id", "output_columns"} or source is None
                    or source["factor"] != factor or not source["observed_syntax"]["source_free"]
                    or source["observed_syntax"]["dependencies"]
                    or not isinstance(entry["output_columns"], list) or not entry["output_columns"]):
                raise ValueError("source output registry disagrees with its fixed closed population")
            for column in entry["output_columns"]:
                if (set(column) != {"name", "type", "nullable"}
                        or not isinstance(column["name"], str) or not column["name"]
                        or not isinstance(column["type"], str) or not column["type"]
                        or type(column["nullable"]) is not bool):
                    raise ValueError("invalid exact source output metadata")
    registered = [r["id"] for entries in registry.values() for r in entries]
    if (len(registered) != 62 or len(set(registered)) != 62
            or set(registered) != {r["id"] for r in records if r["observed_syntax"]["source_free"]}
            or sum(len(r["output_columns"]) for entries in registry.values() for r in entries) != 83):
        raise ValueError("fixed 62-query/83-column source registry changed")


def validate_population(records):
    if len(records) != 150 or Counter(r["factor"] for r in records) != dict.fromkeys(FACTORS, 50):
        raise ValueError("expected exactly 50 inputs per set-operation factor")
    for field in ("id", "sql"):
        if len({r[field] for r in records}) != 150:
            raise ValueError("duplicate global set-operation identity")
    if len({comparison_key(r["sql"]).rstrip(";").strip() for r in records}) != 150:
        raise ValueError("case/whitespace duplicate across set-operation populations")
    for factor, sources in POPULATIONS.items():
        rows = [r for r in records if r["factor"] == factor]
        if Counter(r["source"] for r in rows) != sources:
            raise ValueError("set-operation source population changed")
        for row in rows:
            validate_observation(row["observed_syntax"], factor, row["sql"])
            if (row["raw_sql"] != row["sql"] or row["transformations"] != []
                    or row["parameter_types"] is not None
                    or row["observed_parameter_slots"] != row["observed_syntax"]["parameter_slots"]
                    or row["observed_parameter_slots"] != []
                    or row["application_schema_validity"] != "not-claimed"):
                raise ValueError("source SQL, binding or application assumptions changed")
        expected_closed = 50 if factor == "union" else 6
        if sum(r["observed_syntax"]["source_free"] for r in rows) != expected_closed:
            raise ValueError("fixed source-free population changed")
        with_all = sum(any(e["operator"] == factor and e["all"]
                           for e in r["observed_syntax"]["set_operations"]) for r in rows)
        if with_all != {"union": 28, "intersect": 7, "except": 12}[factor]:
            raise ValueError("fixed ALL spelling population changed")
        dependencies = sum((Counter(r["observed_syntax"]["dependencies"]) for r in rows), Counter())
        if dependencies != ({"aggregate": 1, "distinct": 1, "scalar_subquery": 2}
                            if factor == "intersect" else {}):
            raise ValueError("fixed source prerequisite population changed")


def extract(manifest, root=ROOT):
    if (manifest.get("format_version") != 1 or manifest.get("population") != "set_operations"
            or manifest.get("expected_count") != 150
            or manifest.get("expected_factors") != POPULATIONS
            or set(manifest["sources"]) != set(SOURCE_COUNTS)):
        raise ValueError("unexpected set-operation manifest")
    files, spans = {}, {}
    for name, metadata in manifest["sources"].items():
        if not re.fullmatch(r"[0-9a-f]{40}", metadata["commit"]):
            raise ValueError("source revision must be a complete commit pin")
        checked_file(root, metadata["license_file"], metadata["license_sha256"])
        for notice in metadata.get("additional_notices", []):
            checked_file(root, notice["local_path"], notice["sha256"])
        for entry in metadata["files"]:
            key = name, entry["path"]
            if key in files:
                raise ValueError("duplicate pinned source input")
            files[key] = checked_file(root, entry["local_path"], entry["sha256"]).decode("utf-8")
            if entry["path"].endswith(".sql"):
                spans[key] = statement_spans(files[key])
    records, used = [], set()
    for selection in manifest["selections"]:
        factor, name, path = selection["factor"], selection["source"], selection["path"]
        key, selector = (name, path), selection["selector"]
        if factor not in FACTORS or key not in files:
            raise ValueError("selection has no registered factor/source")
        used.add(key)
        if selector["kind"] == "sql_slice":
            if name not in {"postgres", "sqlc"} or key not in spans:
                raise ValueError("SQL statement selection outside pinned SQL files")
            sql, line, detail = selected_sql(files[key], selector, spans[key])
            suffix = f"statement-{detail['statement_index']}"
        elif selector["kind"] == "tcl_sql_statement":
            if name != "sqlite":
                raise ValueError("Tcl selection outside SQLite")
            sql, line, detail = selected_tcl_sql(files[key], selector)
            suffix = f"tcl-{detail['command_start']}-statement-{detail['statement_index']}"
        elif selector["kind"] == "setop_sqllogic_query":
            if name not in {"duckdb", "materialize"}:
                raise ValueError("SQLLogicTest selection outside its pinned source families")
            sql, line, detail = selected_setop_sqllogic(files[key], selector)
            suffix = f"sqllogic-query-{detail['header_line']}"
        else:
            raise ValueError("unregistered set-operation source selector")
        if sha256(sql.encode("utf-8")) != selection["sql_sha256"]:
            raise ValueError("selected source SQL hash mismatch")
        metadata = manifest["sources"][name]
        records.append({
            "id": f"{factor}:{name}:{path}:{suffix}", "factor": factor,
            "source": name, "source_kind": metadata["source_kind"],
            **({"source_dialect": metadata["source_dialect"]} if "source_dialect" in metadata else {}),
            "source_file": path, "line": line,
            "source_url": f"{metadata['repository']}/blob/{metadata['commit']}/{path}#L{line}",
            "commit": metadata["commit"], "license": metadata["license"], **detail,
            "observed_syntax": selection["observed_syntax"],
            "observed_parameter_slots": parameter_slots(sql), "parameter_types": None,
            "application_schema_validity": "not-claimed",
            "raw_sql": sql, "sql": sql, "sql_sha256": selection["sql_sha256"], "transformations": [],
        })
    if used != set(files):
        raise ValueError("unused pinned source input")
    validate_population(records)
    return records


def render(records):
    return "".join(json.dumps(row, ensure_ascii=False) + "\n" for row in records)


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--check", action="store_true")
    parser.add_argument("--oracle", action="store_true")
    args = parser.parse_args()
    records = extract(json.loads((DIRECTORY / "concrete_sources.json").read_text()))
    validate_registry(records, json.loads((DIRECTORY / "source_contracts.json").read_text()))
    if args.oracle:
        for row in records:
            if oracle(row["sql"], row["factor"]) != row["observed_syntax"]:
                raise ValueError(f"{row['id']}: PostgreSQL raw-tree observations changed")
    output, text = DIRECTORY / "concrete.jsonl", render(records)
    if args.check:
        if not output.exists() or output.read_text() != text:
            raise ValueError("stale set-operation corpus")
    else:
        output.write_text(text)
    print("set_operations: 150 unchanged whole SELECTs; 50 per factor; source hashes verified"
          + ("; PostgreSQL raw-tree observations verified" if args.oracle else ""))
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
