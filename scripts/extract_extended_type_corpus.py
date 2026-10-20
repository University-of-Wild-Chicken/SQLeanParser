#!/usr/bin/env python3
"""Reproduce 50 unchanged public SELECTs exercising extended built-in types.

Standard-library extraction verifies vendored source/license hashes and exact
constant/statement selections. --oracle additionally checks pglast 7.21 syntax,
type-family observations, and parameter slots. No upstream code or SQL runs.
"""
from __future__ import annotations

import argparse
from collections import Counter
import json
from pathlib import Path
import re

from extract_application_corpus import first_sql_text
from extract_pagination_corpus import checked_file, comparison_key, extract_selection, sha256

ROOT = Path(__file__).resolve().parents[1]
DIRECTORY = ROOT / "fixtures/extended_types"
EXPECTED_SOURCES = {"hatchet": 20, "sqlc": 1, "postgres": 29}
NEW_FAMILIES = {
    "int2", "bpchar", "date", "time", "timetz", "timestamp", "timestamptz",
    "interval", "uuid", "json", "jsonb", "bytea",
}
OLD_FAMILIES = {"int4", "int8", "text", "varchar", "bool", "float4", "float8", "numeric"}


def sql_code(source: str) -> str:
    """Mask PostgreSQL lexical data/comments while preserving character offsets.

    E strings additionally escape the next character with backslash. Ordinary
    strings use standard_conforming_strings=on. No runtime SET is evaluated.
    Selected queries do not depend on a different lexical setting.
    """
    output = list(source)
    index = 0
    while index < len(source):
        start = index
        if source.startswith("--", index):
            end = source.find("\n", index + 2)
            index = len(source) if end < 0 else end
        elif source.startswith("/*", index):
            depth = 1
            index += 2
            while index < len(source) and depth:
                if source.startswith("/*", index):
                    depth += 1
                    index += 2
                elif source.startswith("*/", index):
                    depth -= 1
                    index += 2
                else:
                    index += 1
            if depth:
                raise ValueError("unterminated source block comment")
        elif source[index] in "'\"":
            quote = source[index]
            escaped = (quote == "'" and index > 0 and source[index - 1] in "Ee"
                       and (index < 2 or not (source[index - 2].isalnum()
                                             or source[index - 2] in "_$")))
            index += 1
            while index < len(source):
                if escaped and source[index] == "\\":
                    index += 2
                elif source[index] == quote:
                    index += 1
                    if index < len(source) and source[index] == quote:
                        index += 1
                    else:
                        break
                else:
                    index += 1
            else:
                raise ValueError("unterminated source quoted text")
        elif match := re.match(r"\$(?:[A-Za-z_][A-Za-z_0-9]*)?\$", source[index:]):
            marker = match[0]
            end = source.find(marker, index + len(marker))
            if end < 0:
                raise ValueError("unterminated source dollar quote")
            index = end + len(marker)
        else:
            index += 1
            continue
        for position in range(start, min(index, len(source))):
            if output[position] != "\n":
                output[position] = " "
    return "".join(output)


def sql_spans(source: str) -> list[tuple[int, int]]:
    code = sql_code(source)
    previous, spans = 0, []
    for match in re.finditer(";", code):
        first = re.search(r"\S", code[previous:match.start()])
        if first:
            spans.append((previous + first.start(), match.end()))
        previous = match.end()
    return spans


def parameter_slots(sql: str) -> list[int]:
    """Observe first-occurrence slot IDs without assigning parameter types."""
    slots = []
    for match in re.finditer(r"[A-Za-z_][A-Za-z_0-9$]*|\$([1-9][0-9]*)", sql_code(sql)):
        if match[1] is not None:
            slot = int(match[1])
            if slot not in slots:
                slots.append(slot)
    return slots


def select_sql(source: str, selector: dict) -> tuple[str, int, dict]:
    if selector["kind"] == "go_constant":
        return extract_selection(source, selector)
    if selector["kind"] != "sql_slice":
        raise ValueError("unknown extended-type extraction kind")
    start, end, index = (selector[key] for key in ("start", "end", "statement_index"))
    if any(type(value) is not int for value in (start, end, index)):
        raise ValueError("SQL positions must be integers")
    spans = sql_spans(source)
    if index < 0 or index >= len(spans) or spans[index] != (start, end):
        raise ValueError("selected SQL slice is not the pinned complete statement")
    return source[start:end], source.count("\n", 0, start) + 1, {
        "statement_index": index, "source_start": start, "source_end": end,
        "extraction": "unchanged complete SQL statement substring",
    }


def validate_population(records: list[dict]) -> None:
    if len(records) != 50 or Counter(row["source"] for row in records) != EXPECTED_SOURCES:
        raise ValueError("expected 50 statements with the pinned extended-type source population")
    for field in ("id", "sql"):
        if len({row[field] for row in records}) != 50:
            raise ValueError(f"duplicate extended-type {field}")
    if len({comparison_key(row["sql"]) for row in records}) != 50:
        raise ValueError("case/whitespace duplicate extended-type SQL")
    found = set()
    for row in records:
        sql = row["sql"]
        if not re.match(r"(?:SELECT|WITH)\b", first_sql_text(sql), re.I):
            raise ValueError("expected an unchanged whole SELECT")
        if "\x00" in sql or row["raw_sql"] != sql or row["transformations"]:
            raise ValueError("concrete SQL text was changed")
        families = row["new_type_families"]
        if not families or families != sorted(set(families)) or not set(families) <= NEW_FAMILIES:
            raise ValueError("invalid new-type family observation")
        found.update(families)
        if row["observed_parameter_slots"] != parameter_slots(sql):
            raise ValueError("parameter-slot observation changed")
        if row["parameter_types"] is not None or row["application_schema_validity"] != "not-claimed":
            raise ValueError("concrete source must not invent parameter/schema validity")
    if found != NEW_FAMILIES:
        raise ValueError("the twelve new built-in type families are not all represented")


def extract(manifest: dict, root: Path = ROOT) -> list[dict]:
    if (manifest.get("format_version") != 1 or manifest.get("factor") != "extended-types"
            or manifest.get("expected_count") != 50
            or manifest.get("expected_sources") != EXPECTED_SOURCES
            or set(manifest["sources"]) != set(EXPECTED_SOURCES)):
        raise ValueError("unexpected extended-type source manifest")
    files = {}
    for name, metadata in manifest["sources"].items():
        if not re.fullmatch(r"[0-9a-f]{40}", metadata["commit"]):
            raise ValueError("source revision is not a full commit pin")
        checked_file(root, metadata["license_file"], metadata["license_sha256"])
        for entry in metadata["files"]:
            key = (name, entry["path"])
            if key in files:
                raise ValueError("duplicate pinned source input")
            files[key] = checked_file(root, entry["local_path"], entry["sha256"]).decode("utf-8")
    records, used = [], set()
    for selection in manifest["selections"]:
        name, path = selection["source"], selection["path"]
        key = (name, path)
        if key not in files:
            raise ValueError("selection has no pinned source input")
        used.add(key)
        metadata = manifest["sources"][name]
        sql, line, detail = select_sql(files[key], selection["selector"])
        if sha256(sql.encode()) != selection["sql_sha256"]:
            raise ValueError("selected SQL hash mismatch")
        suffix = detail.get("symbol", f"statement-{detail.get('statement_index')}")
        records.append({
            "id": f"extended-types:{name}:{path}:{suffix}",
            "source": name, "source_kind": metadata["source_kind"],
            "source_file": path, "line": line,
            "source_url": f"{metadata['repository']}/blob/{metadata['commit']}/{path}#L{line}",
            "commit": metadata["commit"], "license": metadata["license"],
            "factor": "extended-types", **detail,
            "new_type_families": selection["new_type_families"],
            "observed_parameter_slots": parameter_slots(sql),
            "parameter_types": None,
            "application_schema_validity": "not-claimed",
            "raw_sql": sql, "sql": sql, "sql_sha256": selection["sql_sha256"],
            "transformations": [],
        })
    if used != set(files):
        raise ValueError("unused pinned source input")
    validate_population(records)
    return records


def check_oracle(records: list[dict]) -> None:
    import pglast
    from pglast import ast, parse_sql, visitors

    if pglast.__version__ != "v7.21":
        raise ValueError("extended-type oracle requires pglast v7.21")

    class Observe(visitors.Visitor):
        def visit_TypeName(self, ancestors, node):
            names = [part.sval for part in node.names or ()]
            if (not names or names[-1] not in NEW_FAMILIES | OLD_FAMILIES
                    or len(names) > 2 or (len(names) == 2 and names[0] != "pg_catalog")
                    or node.arrayBounds):
                raise ValueError("selected source depends on an array or user-defined type")
            if names[-1] in NEW_FAMILIES:
                self.families.add(names[-1])

        def visit_ParamRef(self, ancestors, node):
            self.slots.add(node.number)

    for row in records:
        tree = parse_sql(row["sql"])
        if len(tree) != 1 or not isinstance(tree[0].stmt, ast.SelectStmt):
            raise ValueError(f"{row['id']}: oracle did not parse one SELECT")
        observer = Observe()
        observer.families, observer.slots = set(), set()
        observer(tree)
        if sorted(observer.families) != row["new_type_families"]:
            raise ValueError(f"{row['id']}: type-family observation disagrees with PostgreSQL")
        if observer.slots != set(row["observed_parameter_slots"]):
            raise ValueError(f"{row['id']}: parameter slots disagree with PostgreSQL")


def render(records: list[dict]) -> str:
    return "".join(json.dumps(row, ensure_ascii=False) + "\n" for row in records)


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--check", action="store_true")
    parser.add_argument("--oracle", action="store_true")
    args = parser.parse_args()
    manifest = json.loads((DIRECTORY / "concrete_sources.json").read_text())
    records = extract(manifest)
    if args.oracle:
        check_oracle(records)
    output, text = DIRECTORY / "concrete.jsonl", render(records)
    if args.check:
        if not output.is_file() or output.read_text() != text:
            raise ValueError("stale extended-type concrete corpus")
    else:
        output.write_text(text)
    print("Extended types: 50 unchanged SELECTs; 20 application constants, "
          "1 compiler regression, 29 engine regressions; 12 new type families"
          + "; source hashes verified" + ("; PostgreSQL grammar verified" if args.oracle else ""))
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
