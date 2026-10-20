#!/usr/bin/env python3
"""Reproduce 50 unchanged public SELECT statements with expression pagination.

Extraction and --check use only the standard library and vendored, hash-pinned
sources. --oracle additionally checks PostgreSQL syntax with pinned pglast 7.21.
No source programs, templates, or SQL statements are executed.
"""
from __future__ import annotations

import argparse
from collections import Counter
import hashlib
import json
from pathlib import Path
import re

from extract_application_corpus import decode_constants, first_sql_text, sql_code

ROOT = Path(__file__).resolve().parents[1]
DIRECTORY = ROOT / "fixtures/pagination"
EXPECTED_SOURCES = {"temporal": 20, "river": 1, "cadence": 21, "sqlc": 8}


def sha256(data: bytes) -> str:
    return hashlib.sha256(data).hexdigest()


def checked_file(root: Path, local_path: str, digest: str) -> bytes:
    path = root / local_path
    if not path.resolve().is_relative_to(root.resolve()):
        raise ValueError(f"source path escapes repository: {local_path}")
    data = path.read_bytes()
    if sha256(data) != digest:
        raise ValueError(f"source hash mismatch: {local_path}")
    return data


def sql_spans(source: str) -> list[tuple[int, int]]:
    """Find complete semicolon-terminated statement spans, preserving their bytes.

    Quoted strings/identifiers, dollar quotes, and nested PostgreSQL comments
    are masked only when locating semicolons. Leading comments are outside the
    selected statement; comments inside a statement remain unchanged.
    """
    code = sql_code(source)
    result = []
    previous = 0
    for match in re.finditer(";", code):
        first = re.search(r"\S", code[previous:match.start()])
        if first:
            result.append((previous + first.start(), match.end()))
        previous = match.end()
    return result


def extract_selection(source: str, selector: dict) -> tuple[str, int, dict]:
    if selector["kind"] == "go_constant":
        symbol = selector["symbol"]
        records = [record for record in decode_constants(source)
                   if record["symbol"] == symbol]
        if len(records) != 1 or "raw_sql" not in records[0]:
            raise ValueError(f"selected Go constant is missing or undecodable: {symbol}")
        record = records[0]
        return record["raw_sql"], record["line"], {
            "symbol": symbol,
            "source_expression": record["source_expression"],
            "go_constant_folding": record["go_constant_folding"],
            "extraction": "decode the original Go string constant",
        }
    if selector["kind"] == "sql_slice":
        start, end, index = (selector[key] for key in ("start", "end", "statement_index"))
        if any(type(value) is not int for value in (start, end, index)):
            raise ValueError("SQL slice positions must be integers")
        spans = sql_spans(source)
        if index < 0 or index >= len(spans) or spans[index] != (start, end):
            raise ValueError("selected SQL slice is not the pinned complete statement")
        return source[start:end], source.count("\n", 0, start) + 1, {
            "statement_index": index,
            "source_start": start,
            "source_end": end,
            "extraction": "unchanged complete SQL statement substring",
        }
    raise ValueError(f"unknown extraction kind: {selector['kind']}")


def comparison_key(sql: str) -> str:
    """Conservative extra deduplication for this finite selected population.

    Folding case/whitespace even inside data can reject additional statements,
    but cannot allow a duplicate to inflate the count. This is not SQL semantic
    equivalence or an unrestricted SQL lexer.
    """
    return re.sub(r"\s+", " ", sql).strip().lower()


def validate_population(records: list[dict]) -> None:
    if len(records) != 50:
        raise ValueError(f"expected exactly 50 concrete statements, found {len(records)}")
    if Counter(record["source"] for record in records) != EXPECTED_SOURCES:
        raise ValueError("unexpected concrete source population")
    for field in ("id", "sql"):
        if len({record[field] for record in records}) != len(records):
            raise ValueError(f"duplicate concrete {field}")
    if len({comparison_key(record["sql"]) for record in records}) != len(records):
        raise ValueError("case/whitespace duplicate concrete SQL")
    for record in records:
        sql = record["sql"]
        if not re.match(r"SELECT\b", first_sql_text(sql), re.I):
            raise ValueError(f"{record['id']}: expected a whole SELECT statement")
        if not re.search(r"\b(?:LIMIT|OFFSET)\s+\$[1-9][0-9]*\b", sql_code(sql), re.I):
            raise ValueError(f"{record['id']}: selected pagination factor is absent")
        if "\x00" in sql or record["transformations"] or record["raw_sql"] != sql:
            raise ValueError(f"{record['id']}: SQL text was changed")


def extract(manifest: dict, root: Path = ROOT) -> list[dict]:
    if (manifest.get("format_version") != 1
            or manifest.get("factor") != "expression-limit-offset"
            or manifest.get("expected_count") != 50
            or manifest.get("expected_sources") != EXPECTED_SOURCES
            or set(manifest["sources"]) != set(EXPECTED_SOURCES)):
        raise ValueError("unexpected pagination source manifest")
    files = {}
    for name, metadata in manifest["sources"].items():
        if not re.fullmatch(r"[0-9a-f]{40}", metadata["commit"]):
            raise ValueError(f"{name}: source revision is not a full commit pin")
        checked_file(root, metadata["license_file"], metadata["license_sha256"])
        for entry in metadata["files"]:
            key = (name, entry["path"])
            if key in files:
                raise ValueError(f"duplicate source input: {key}")
            files[key] = checked_file(root, entry["local_path"], entry["sha256"]).decode("utf-8")

    records = []
    used = set()
    for selection in manifest["selections"]:
        name, path = selection["source"], selection["path"]
        metadata = manifest["sources"][name]
        key = (name, path)
        if key not in files:
            raise ValueError(f"selection has no pinned source input: {key}")
        used.add(key)
        sql, line, detail = extract_selection(files[key], selection["selector"])
        if sha256(sql.encode()) != selection["sql_sha256"]:
            raise ValueError(f"selected SQL hash mismatch: {key}, {selection['selector']}")
        suffix = detail.get("symbol", f"statement-{detail.get('statement_index')}")
        record = {
            "id": f"pagination:{name}:{path}:{suffix}",
            "source": name,
            "source_kind": metadata["source_kind"],
            "source_file": path,
            "line": line,
            "source_url": f"{metadata['repository']}/blob/{metadata['commit']}/{path}#L{line}",
            "commit": metadata["commit"],
            "license": metadata["license"],
            "factor": "expression-limit-offset",
            **detail,
            "raw_sql": sql,
            "sql": sql,
            "sql_sha256": selection["sql_sha256"],
            "transformations": [],
        }
        if name == "river":
            record["template_form"] = "unexpanded upstream constant; schema comment retained"
        records.append(record)
    if used != set(files):
        raise ValueError("manifest includes source inputs unused by its selections")
    validate_population(records)
    return records


def check_oracle(records: list[dict]) -> None:
    import pglast
    from pglast import ast, parse_sql, visitors

    if pglast.__version__ != "v7.21":
        raise ValueError(f"expected pglast v7.21, found {pglast.__version__}")

    class Pagination(visitors.Visitor):
        def visit_SelectStmt(self, ancestors, node):
            for key in ("limitCount", "limitOffset"):
                value = getattr(node, key)
                if value is not None and not isinstance(value, ast.A_Const):
                    self.found = True

    for record in records:
        tree = parse_sql(record["sql"])
        if len(tree) != 1 or not isinstance(tree[0].stmt, ast.SelectStmt):
            raise ValueError(f"{record['id']}: PostgreSQL did not parse one SELECT")
        observer = Pagination()
        observer.found = False
        observer(tree)
        if not observer.found:
            raise ValueError(f"{record['id']}: PostgreSQL found no pagination expression")


def render(records: list[dict]) -> str:
    return "".join(json.dumps(record, ensure_ascii=False) + "\n" for record in records)


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--check", action="store_true", help="fail if checked-in output differs")
    parser.add_argument("--oracle", action="store_true", help="also check pinned PostgreSQL grammar")
    args = parser.parse_args()
    manifest = json.loads((DIRECTORY / "concrete_sources.json").read_text())
    records = extract(manifest)
    if args.oracle:
        check_oracle(records)
    output = DIRECTORY / "concrete.jsonl"
    text = render(records)
    if args.check:
        if not output.is_file() or output.read_text() != text:
            raise ValueError(f"stale extracted pagination corpus: {output}")
    else:
        output.write_text(text)
    print("Pagination concrete corpus: 50 unchanged unique SELECTs "
          "(42 application constants, 8 compiler regressions); source hashes verified"
          + ("; PostgreSQL grammar verified" if args.oracle else ""))
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
