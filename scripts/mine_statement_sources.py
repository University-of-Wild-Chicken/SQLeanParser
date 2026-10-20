#!/usr/bin/env python3
"""Reproduce the finite statement source search, without executing SQL.

Requires pinned pglast 7.21 and a built sqlean_pg_grammar. Source restoration
downloads only commit-pinned, hash-verified files when --download is explicit.
Outputs a complete exclusion ledger and exact outer-family observations.
"""
from __future__ import annotations

import argparse
from collections import Counter
import json
from pathlib import Path
import re
import subprocess
from urllib.request import urlopen

from extract_application_corpus import decode_constants, first_sql_text
from extract_pagination_corpus import checked_file, comparison_key, sha256
from extract_statement_corpus import COMMIT, DIRECTORY, ROOT, statement_spans


def input_bytes(metadata: dict, entry: dict, cache: Path, download: bool) -> bytes:
    if entry.get("local_path") and (ROOT / entry["local_path"]).is_file():
        return checked_file(ROOT, entry["local_path"], entry["sha256"])
    path = cache / metadata["cache_directory"] / entry["path"]
    if not path.is_file() and download:
        url = f"{metadata['repository'].replace('https://github.com/', 'https://raw.githubusercontent.com/')}/{metadata['commit']}/{entry['path']}"
        with urlopen(url, timeout=60) as response:
            data = response.read()
        if sha256(data) != entry["sha256"]:
            raise ValueError(f"downloaded source hash mismatch: {url}")
        path.parent.mkdir(parents=True, exist_ok=True)
        path.write_bytes(data)
    data = path.read_bytes()
    if sha256(data) != entry["sha256"]:
        raise ValueError(f"cached source hash mismatch: {path}")
    return data


def candidates(source: str, path: str):
    if path.endswith(".sql.go"):
        for record in decode_constants(source):
            if "raw_sql" not in record:
                yield {"decode_error": record["decode_error"], "symbol": record["symbol"]}
                continue
            sql = record["raw_sql"]
            if not re.match(r"(SELECT|WITH|INSERT|UPDATE|DELETE|CREATE|ALTER|DROP)\b",
                            first_sql_text(sql), re.I):
                continue
            yield {"sql": sql, "line": record["line"],
                   "selector": {"kind": "go_constant", "symbol": record["symbol"]}}
    else:
        for index, (start, end) in enumerate(statement_spans(source)):
            yield {"sql": source[start:end], "line": source.count("\n", 0, start) + 1,
                   "selector": {"kind": "sql_slice", "start": start, "end": end,
                                "statement_index": index}}


def mine(catalog: dict, cache: Path, download: bool) -> tuple[list[dict], list[dict], dict]:
    import pglast
    from pglast import parser
    if pglast.__version__ != "v7.21":
        raise ValueError("statement mining requires pglast v7.21")
    rows, excluded, seen = [], [], {}
    file_count = 0
    for name, metadata in catalog["sources"].items():
        if not re.fullmatch(r"[0-9a-f]{40}", metadata["commit"]):
            raise ValueError("source revision must be a full commit pin")
        for entry in metadata["files"]:
            file_count += 1
            path = entry["path"]
            origin = {"source": name, "source_kind": metadata["source_kind"],
                      "source_file": path, "commit": metadata["commit"],
                      "source_sha256": entry["sha256"]}
            data = input_bytes(metadata, entry, cache, download)
            try:
                source = data.decode("utf-8")
                extracted = list(candidates(source, path))
            except (UnicodeDecodeError, ValueError) as error:
                excluded.append({**origin, "disposition": "source-extraction-failure",
                                 "diagnostic": str(error)})
                continue
            for candidate in extracted:
                if "decode_error" in candidate:
                    excluded.append({**origin, **candidate,
                                     "disposition": "constant-extraction-failure"})
                    continue
                selector = candidate["selector"]
                suffix = selector.get("symbol", f"statement-{selector.get('statement_index')}")
                sql = candidate["sql"]
                row = {
                    **origin, **candidate, "id": f"statement-pool:{name}:{path}:{suffix}",
                    "sql_sha256": sha256(sql.encode()),
                    "source_url": f"{metadata['repository']}/blob/{metadata['commit']}/{path}#L{candidate['line']}",
                }
                try:
                    statements = json.loads(parser.parse_sql_json(sql))["stmts"]
                    if len(statements) != 1:
                        raise ValueError("expected one complete raw-parser statement")
                    row["postgres_ast_kind"] = next(iter(statements[0]["stmt"]))
                except Exception as error:
                    excluded.append({**row, "raw_sql": sql,
                                     "disposition": "raw-parser-rejected",
                                     "diagnostic": str(error)})
                    continue
                key = comparison_key(sql)
                if key in seen:
                    excluded.append({**row, "disposition": "conservative-duplicate",
                                     "duplicate_of": seen[key]})
                    continue
                seen[key] = row["id"]
                rows.append(row)
    summary = {
        "input_files": file_count, "raw_parser": "pglast v7.21 / PostgreSQL 17.7",
        "unique_raw_parser_accepted": len(rows),
        "by_source": dict(sorted(Counter(row["source"] for row in rows).items())),
        "exclusions": dict(sorted(Counter(row["disposition"] for row in excluded).items())),
        "boundary": "finite pinned file search; psql meta-commands are not interpreted; no SQL execution",
    }
    return rows, excluded, summary


def classify(rows: list[dict], executable: Path, directory: Path) -> tuple[list[dict], list[dict]]:
    pool = directory / "pool.jsonl"
    by_id = {row["id"]: row for row in rows}
    if len(by_id) != len(rows):
        raise ValueError("duplicate candidate identity")
    accepted, rejected, seen = [], [], set()
    with pool.open() as source, (directory / "grammar-stderr.log").open("w") as errors:
        process = subprocess.Popen([str(executable), "--jsonl"], stdin=source,
                                   stdout=subprocess.PIPE, stderr=errors, text=True)
        assert process.stdout is not None
        for line in process.stdout:
            report = json.loads(line)
            ident, result = report["id"], report["result"]
            if ident not in by_id or ident in seen:
                process.kill()
                raise ValueError("unknown or duplicate grammar result")
            seen.add(ident)
            if result["postgresqlCommit"] != COMMIT:
                raise ValueError("grammar classifier uses the wrong PostgreSQL revision")
            row = by_id[ident]
            if result["status"] == "grammar-accepted":
                if (result["sql"] != row["sql"] or result["sourcePreservation"] != "exact"
                        or result["evidence"] != "context-free-derivation"
                        or result["staticValidity"] != "not-checked"
                        or result["grammarSemanticActions"] != "not-checked"
                        or len(result["statementFamilies"]) != 1):
                    raise ValueError("grammar result changed source or outer statement identity")
                accepted.append({**row, "grammar_family": result["statementFamilies"][0],
                                 "production_ids": result["productionIds"]})
            elif result["status"] == "grammar-rejected":
                rejected.append({**row, "diagnostic": result["diagnostic"]})
            else:
                raise ValueError(f"grammar classification was inconclusive: {ident}")
        code = process.wait()
    if len(seen) != len(rows) or code != (1 if rejected else 0):
        raise ValueError("grammar process did not classify the complete source population")
    return accepted, rejected


def jsonl(path: Path, records: list[dict]) -> None:
    path.write_text("".join(json.dumps(row, ensure_ascii=False) + "\n" for row in records))


def select_sources(rows: list[dict], family_order: list[str]) -> list[dict]:
    """Cap each family at 50, greedily retaining diverse grammar derivations.

    Newly visited production IDs take priority, followed by application,
    compiler and engine provenance, then shorter source and stable identity.
    This selects existing whole statements; it does not generate variants.
    """
    groups = {family: [] for family in family_order}
    priority = {"application-constant": 0, "compiler-regression": 1, "engine-regression": 2}
    for row in rows:
        groups[row["grammar_family"]].append(row)
    selected = []
    for family in family_order:
        remaining = [(row, sum(1 << n for n in set(row["production_ids"])))
                     for row in groups[family]]
        covered = 0
        for _ in range(min(50, len(remaining))):
            index = min(range(len(remaining)), key=lambda i: (
                -(remaining[i][1] & ~covered).bit_count(),
                priority[remaining[i][0]["source_kind"]],
                len(remaining[i][0]["sql"]), remaining[i][0]["id"]))
            row, mask = remaining.pop(index)
            selected.append(row)
            covered |= mask
    return selected


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--source-cache", type=Path, required=True)
    parser.add_argument("--output-dir", type=Path, required=True)
    parser.add_argument("--download", action="store_true")
    parser.add_argument("--grammar-exe", type=Path, default=ROOT / ".lake/build/bin/sqlean_pg_grammar")
    args = parser.parse_args()
    catalog_path = DIRECTORY / "mining_sources.json"
    catalog = json.loads(catalog_path.read_text())
    if catalog.get("format_version") != 1:
        raise ValueError("unexpected mining source catalog")
    args.output_dir.mkdir(parents=True, exist_ok=True)
    rows, excluded, summary = mine(catalog, args.source_cache, args.download)
    jsonl(args.output_dir / "pool.jsonl", rows)
    jsonl(args.output_dir / "exclusions.jsonl", excluded)
    accepted, rejected = classify(rows, args.grammar_exe.resolve(), args.output_dir)
    jsonl(args.output_dir / "accepted.jsonl", accepted)
    jsonl(args.output_dir / "rejected.jsonl", rejected)
    grammar = json.loads((ROOT / "fixtures/postgresql_grammar/inventory.json").read_text())
    selected = select_sources(accepted, [row["name"] for row in grammar["statement_families"]])
    jsonl(args.output_dir / "selected.jsonl", selected)
    summary.update({
        "source_catalog_sha256": sha256(catalog_path.read_bytes()),
        "grammar_accepted": len(accepted), "grammar_rejected": len(rejected),
        "outer_family_counts": dict(sorted(Counter(row["grammar_family"] for row in accepted).items())),
        "selected_count": len(selected),
        "selection": "cap 50 per outer family; greedy new production IDs, source kind, SQL length, stable ID",
    })
    (args.output_dir / "summary.json").write_text(json.dumps(summary, indent=2) + "\n")
    print(json.dumps(summary, indent=2))
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
