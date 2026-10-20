#!/usr/bin/env python3
"""Reproduce 50 unchanged actual-recursion queries without executing SQL.

The default check is offline. --oracle additionally compares lexical raw-tree
observations using pinned pglast 7.21; it is not a PostgreSQL semantic analyzer.
"""
from __future__ import annotations

import argparse
from collections import Counter
import json
from pathlib import Path
import re

from extract_extended_type_corpus import parameter_slots
from extract_pagination_corpus import checked_file, comparison_key, sha256
from extract_recursive_sqllogic_sql import selected_recursive_sqllogic
from extract_statement_corpus import selected_sql, statement_spans
from observe_recursive_source import oracle, validate_observation

ROOT = Path(__file__).resolve().parents[1]
DIRECTORY = ROOT / "fixtures/recursive_contract"
SOURCE_COUNTS = {"postgres": 14, "duckdb": 31, "sqlc": 4, "hatchet": 1}
REGISTRY_SHA256 = "d87e149470535fe4aec010bf0c7e9f08fffd6beb9045f1ff4723056e68e4f281"


def validate_registry(records, registry):
    """Require the preregistered independent ID/ordered-output expectations."""
    if (not isinstance(registry, list)
            or sha256(json.dumps(registry, sort_keys=True, separators=(",", ":")).encode()) != REGISTRY_SHA256):
        raise ValueError("fixed independent recursive source output registry changed")
    eligible = {r["id"] for r in records
                if r["observed_syntax"]["source_free"] and not r["observed_syntax"]["dependencies"]}
    if (len(registry) != 21 or len({r["id"] for r in registry}) != 21
            or {r["id"] for r in registry} != eligible):
        raise ValueError("fixed recursive certificate population changed")
    columns = []
    for entry in registry:
        if (set(entry) != {"id", "output_columns"}
                or not isinstance(entry["output_columns"], list) or not entry["output_columns"]):
            raise ValueError("invalid exact recursive output metadata")
        for column in entry["output_columns"]:
            if (set(column) != {"name", "type", "nullable"}
                    or not isinstance(column["name"], str) or not column["name"]
                    or not isinstance(column["type"], str)
                    or type(column["nullable"]) is not bool or not column["nullable"]):
                raise ValueError("invalid recursive name/type/nullability declaration")
            columns.append(column)
    if len(columns) != 24 or Counter(c["type"] for c in columns) != {
        "int32": 20, "text": 2, "integer[]": 1, "bigint": 1,
    }:
        raise ValueError("fixed 21-query/24-column recursive registry changed")


def validate_population(records):
    if len(records) != 50 or Counter(r["source"] for r in records) != SOURCE_COUNTS:
        raise ValueError("fixed 50-query recursive source population changed")
    if (any(len({r[key] for r in records}) != 50 for key in ("id", "sql"))
            or len({comparison_key(r["sql"]).rstrip(";").strip() for r in records}) != 50):
        raise ValueError("duplicate recursive source identity")
    for row in records:
        value = row["observed_syntax"]
        validate_observation(value, row["sql"])
        actual = [c for c in value["ctes"] if c["self_references"]]
        if (not actual or any(c["operator"] != "union" or c["anchor_references"] != 0
                              or c["step_references"] != 1 or c["self_references"] != 1
                              for c in actual)):
            raise ValueError("every source must retain an actual linear anchor/step recursion")
        if (row["raw_sql"] != row["sql"] or row["transformations"] != []
                or row["parameter_types"] is not None
                or "parameter_values" in row or "expected_value" in row
                or row["observed_parameter_slots"] != value["parameter_slots"]
                or row["application_schema_validity"] != "not-claimed"):
            raise ValueError("source SQL or undeclared application assumptions changed")
    if (sum(r["observed_syntax"]["actual_recursive_count"] for r in records) != 55
            or sum(r["observed_syntax"]["source_free"] for r in records) != 31
            or sum(any(c["self_references"] and c["all"] for c in r["observed_syntax"]["ctes"])
                   for r in records) != 33
            or Counter(k for r in records for k in r["observed_syntax"]["dependencies"])
            != {"SubLink": 5, "aggregate": 5, "function_calls": 3, "distinctClause": 2}):
        raise ValueError("fixed recursive/dependency source inventory changed")


def extract(manifest, root=ROOT):
    if (manifest.get("format_version") != 1 or manifest.get("factor") != "recursive_contract"
            or manifest.get("expected_count") != 50
            or manifest.get("expected_sources") != SOURCE_COUNTS
            or set(manifest["sources"]) != set(SOURCE_COUNTS)):
        raise ValueError("unexpected recursive source manifest")
    files, spans = {}, {}
    for name, metadata in manifest["sources"].items():
        if not re.fullmatch(r"[0-9a-f]{40}", metadata["commit"]):
            raise ValueError("source revision must be a complete commit pin")
        checked_file(root, metadata["license_file"], metadata["license_sha256"])
        for entry in metadata["files"]:
            key = name, entry["path"]
            if key in files:
                raise ValueError("duplicate pinned source input")
            files[key] = checked_file(root, entry["local_path"], entry["sha256"]).decode("utf-8")
            spans[key] = statement_spans(files[key]) if entry["path"].endswith(".sql") else []
    records, used = [], set()
    for selection in manifest["selections"]:
        name, path = selection["source"], selection["path"]
        key, selector = (name, path), selection["selector"]
        if key not in files:
            raise ValueError("selection has no pinned source input")
        used.add(key)
        if selector["kind"] == "sql_slice":
            if name not in {"postgres", "sqlc"} or not path.endswith(".sql"):
                raise ValueError("SQL slice outside its pinned source family")
            sql, line, detail = selected_sql(files[key], selector, spans[key])
            suffix = f"statement-{detail['statement_index']}"
        elif selector["kind"] == "go_constant":
            if name != "hatchet" or not path.endswith(".sql.go"):
                raise ValueError("Go constant outside its pinned source family")
            sql, line, detail = selected_sql(files[key], selector, [])
            suffix = detail["symbol"]
        elif selector["kind"] == "sqllogic_query":
            if name != "duckdb":
                raise ValueError("SQLLogicTest query outside its pinned source family")
            sql, line, detail = selected_recursive_sqllogic(files[key], selector)
            suffix = f"sqllogic-query-{detail['header_line']}"
        else:
            raise ValueError("unregistered recursive source selector")
        if sha256(sql.encode("utf-8")) != selection["sql_sha256"]:
            raise ValueError("selected original SQL hash mismatch")
        metadata = manifest["sources"][name]
        records.append({
            "id": f"recursive_contract:{name}:{path}:{suffix}", "factor": "recursive_contract",
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
            if oracle(row["sql"]) != row["observed_syntax"]:
                raise ValueError(f"{row['id']}: recursive raw-tree observation changed")
    output, content = DIRECTORY / "concrete.jsonl", render(records)
    if args.check:
        if not output.exists() or output.read_text() != content:
            raise ValueError("stale recursive source corpus")
    else:
        output.write_text(content)
    print("recursive_contract: 50 unchanged actual-recursion SELECTs; pinned source hashes verified"
          + ("; PostgreSQL raw-tree observations verified" if args.oracle else ""))
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
