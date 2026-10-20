#!/usr/bin/env python3
"""Extract pinned shipping PostgreSQL queries without running upstream code.

Requires pglast 7.21. Sources and licenses are vendored and hash-checked.
Only Go string constants, literal concatenation, and references to other string
constants in the same source file are decoded. Runtime templates, named sqlx
bindings, and incomplete fragments are recorded explicitly, never repaired.
"""
from __future__ import annotations

import argparse
from collections import Counter
from dataclasses import dataclass
import hashlib
import json
from pathlib import Path
import re
import urllib.request

ROOT = Path(__file__).resolve().parents[1]
DIRECTORY = ROOT / "fixtures/external_postgresql"
TOKEN = re.compile(
    r"(?P<space>[ \t\r]+)|(?P<newline>\n)|(?P<line>//[^\n]*)|"
    r"(?P<block>/\*.*?\*/)|(?P<raw>`[^`]*`)|"
    r'(?P<string>"(?:\\.|[^"\\])*")|(?P<rune>\'(?:\\.|[^\'\\])*\')|'
    r"(?P<name>[A-Za-z_][A-Za-z_0-9]*)|(?P<symbol>.)", re.S)
SQL_START = re.compile(r"^(?:SELECT|INSERT|UPDATE|DELETE|WITH|CREATE|ALTER|DROP|TRUNCATE|VACUUM)\b", re.I)


@dataclass(frozen=True)
class Token:
    kind: str
    text: str
    start: int
    end: int


def go_tokens(source):
    result = []
    for match in TOKEN.finditer(source):
        kind = match.lastgroup
        if kind in ("space", "line"):
            continue
        if kind == "block":
            if "\n" not in match[0]:
                continue
            kind = "newline"
        result.append(Token(kind, match[0], match.start(), match.end()))
    return result


def constant_specs(source):
    """Read top-level const blocks with Go lexical regions kept intact."""
    tokens = go_tokens(source)
    i = 0
    while i < len(tokens):
        if tokens[i].kind != "name" or tokens[i].text != "const":
            i += 1
            continue
        i += 1
        block = i < len(tokens) and tokens[i].text == "("
        if block:
            i += 1
        depth, current = 0, []
        while i < len(tokens):
            token = tokens[i]
            if block and token.text == ")" and depth == 0:
                if current:
                    yield current
                i += 1
                break
            if token.kind == "newline" or token.text == ";":
                i += 1
                if depth or (current and current[-1].text == "+"):
                    continue
                if current:
                    yield current
                    current = []
                    if not block:
                        break
                continue
            if token.text == "(":
                depth += 1
            elif token.text == ")":
                depth -= 1
            current.append(token)
            i += 1


def decode_constants(source):
    declarations = {}
    for spec in constant_specs(source):
        equal = next((i for i, token in enumerate(spec) if token.text == "="), None)
        if equal is None or spec[0].kind != "name":
            continue
        # Single-name constants only; multi-name declarations stay explicit.
        name = spec[0].text
        assert name not in declarations, ("duplicate constant", name)
        declarations[name] = (spec, spec[equal + 1:])

    def evaluate(name, visiting=()):
        if name in visiting or name not in declarations:
            raise ValueError("unresolved or cyclic constant reference")
        expression = declarations[name][1]
        if not expression:
            raise ValueError("empty constant expression")
        parts = []
        for index, token in enumerate(expression):
            if index % 2:
                if token.text != "+":
                    raise ValueError("non-string-constant expression")
            elif token.kind == "raw":
                parts.append(token.text[1:-1].replace("\r", ""))
            elif token.kind == "string":
                try:
                    parts.append(json.loads(token.text))
                except (ValueError, TypeError) as error:
                    raise ValueError("unsupported Go quoted-string escape") from error
            elif token.kind == "name":
                parts.append(evaluate(token.text, (*visiting, name)))
            else:
                raise ValueError("non-string-constant expression")
        if len(expression) % 2 == 0:
            raise ValueError("incomplete constant concatenation")
        return "".join(parts)

    for name, (spec, expression) in declarations.items():
        record = {"symbol": name, "line": source.count("\n", 0, spec[0].start) + 1,
                  "source_expression": source[expression[0].start:expression[-1].end] if expression else ""}
        try:
            record["raw_sql"] = evaluate(name)
        except ValueError as error:
            record["decode_error"] = str(error)
        record["go_constant_folding"] = any(token.text == "+" or token.kind == "name" for token in expression)
        yield record


def first_sql_text(sql):
    return re.sub(r"^(?:\s|--[^\n]*(?:\n|$)|/\*.*?\*/)*", "", sql, flags=re.S)


def sql_code(sql):
    """Mask quoted data and PostgreSQL comments before observing bind syntax."""
    out = list(sql)
    i = 0
    while i < len(sql):
        start = i
        if sql.startswith("--", i):
            end = sql.find("\n", i + 2)
            i = len(sql) if end < 0 else end
        elif sql.startswith("/*", i):
            depth = 1
            i += 2
            while i < len(sql) and depth:
                if sql.startswith("/*", i):
                    depth += 1
                    i += 2
                elif sql.startswith("*/", i):
                    depth -= 1
                    i += 2
                else:
                    i += 1
        elif sql[i] in "'\"":
            quote = sql[i]
            i += 1
            while i < len(sql):
                if sql[i] == quote:
                    i += 1
                    if i < len(sql) and sql[i] == quote:
                        i += 1
                    else:
                        break
                else:
                    i += 1
        elif match := re.match(r"\$(?:[A-Za-z_][A-Za-z_0-9]*)?\$", sql[i:]):
            marker = match[0]
            end = sql.find(marker, i + len(marker))
            i = len(sql) if end < 0 else end + len(marker)
        else:
            i += 1
            continue
        out[start:i] = " " * (i - start)
    return "".join(out)


def formatted_constants(source):
    """Identify actual fmt.Sprintf first arguments, outside strings/comments."""
    tokens = [token.text for token in go_tokens(source) if token.kind != "newline"]
    return {tokens[index + 4] for index in range(len(tokens) - 4)
            if tokens[index:index + 4] == ["fmt", ".", "Sprintf", "("]}


def digest(data):
    return hashlib.sha256(data).hexdigest()


def verify_sources(manifest, fetch=False):
    for app, metadata in manifest.items():
        repo = metadata["repository"].removeprefix("https://github.com/")
        records = [(f"sources/{app}/{entry['path']}", entry["path"], entry["sha256"])
                   for entry in metadata["files"]]
        records.append((metadata["license_file"], "LICENSE", metadata["license_sha256"]))
        for local, upstream, expected in records:
            destination = DIRECTORY / local
            if fetch:
                url = f"https://raw.githubusercontent.com/{repo}/{metadata['commit']}/{upstream}"
                with urllib.request.urlopen(url, timeout=30) as response:
                    content = response.read()
                assert digest(content) == expected, ("downloaded source hash changed", app, upstream)
                destination.parent.mkdir(parents=True, exist_ok=True)
                destination.write_bytes(content)
            assert digest(destination.read_bytes()) == expected, ("vendored source hash changed", app, upstream)


def extract(manifest):
    import pglast
    assert pglast.__version__ == "v7.21", ("requires pinned pglast 7.21", pglast.__version__)
    outputs, ledgers = {}, {}
    for app, metadata in manifest.items():
        included, dispositions, seen = [], [], {}
        for entry in metadata["files"]:
            if not entry["extract"]:
                continue
            path = entry["path"]
            source = (DIRECTORY / "sources" / app / path).read_text(encoding="utf-8")
            formatted = formatted_constants(source)
            if app == "river":
                assert "//   sqlc v1.31.1" in source, ("SQLC provenance changed", path)
            for decoded in decode_constants(source):
                identifier = f"{app}:{path}:{decoded['symbol']}"
                common = {
                    "id": identifier, "source": app, "source_file": path, "line": decoded["line"],
                    "source_url": f"{metadata['repository']}/blob/{metadata['commit']}/{path}#L{decoded['line']}",
                    "commit": metadata["commit"], "license": metadata["license"],
                    **decoded,
                }
                sql = decoded.get("raw_sql", "")
                reason = None
                if "decode_error" in decoded:
                    reason = decoded["decode_error"]
                elif not SQL_START.match(first_sql_text(sql)):
                    reason = "non-statement constant or SQL fragment"
                elif re.search(r"(?:Base|Part|Prefix|Suffix)$", decoded["symbol"]):
                    reason = "named base/part/prefix/suffix; not a submitted full query"
                elif decoded["symbol"] in formatted:
                    reason = "runtime fmt.Sprintf call requires substitution"
                elif re.search(r"(?<!:):[A-Za-z_]", sql_code(sql)):
                    reason = "sqlx named binding required; no invented slot mapping"
                else:
                    try:
                        parsed = pglast.parse_sql(sql)
                        if len(parsed) != 1:
                            reason = "not exactly one PostgreSQL statement"
                    except pglast.Error as error:
                        reason = "PostgreSQL raw-parser rejection; excluded from valid SQL population"
                        common["oracle_error"] = str(error)
                if reason is None and sql in seen:
                    reason = "duplicate SQL of " + seen[sql]
                if reason is not None:
                    dispositions.append({**common, "disposition": "excluded", "reason": reason})
                    continue
                seen[sql] = identifier
                templates = sorted(set(re.findall(r"/\*\s*TEMPLATE(?:_BEGIN)?:\s*([a-z_]+)\s*\*/", sql)))
                row = {**common, "sql": sql, "transformations": [],
                       "extraction": "decode Go string constants; SQL bytes preserved",
                       "template_markers": templates,
                       "template_form": "unexpanded upstream constant" if templates else "none",
                       "oracle_statement": type(parsed[0].stmt).__name__}
                if app == "river":
                    row["parameter_provenance"] = "upstream committed SQLC v1.31.1 output; no rebinding"
                    row["sql_source_file"] = path.removesuffix(".go")
                included.append(row)
                dispositions.append({"id": identifier, "source_file": path, "line": decoded["line"],
                                     "disposition": "included", "sql_sha256": digest(sql.encode())})
        if app == "river":
            materialized = {re.search(r"-- name:\s+(\w+)", case["sql"])[1] for case in included}
            for entry in metadata["files"]:
                if not entry["path"].endswith(".sql"):
                    continue
                path = entry["path"]
                source = (DIRECTORY / "sources" / app / path).read_text()
                markers = list(re.finditer(r"(?m)^-- name:\s+(\w+)\s+:(\w+)", source))
                for index, marker in enumerate(markers):
                    if marker[1] in materialized:
                        continue
                    assert marker[2] == "copyfrom", ("unaccounted SQLC command", path, marker[1])
                    end = markers[index + 1].start() if index + 1 < len(markers) else len(source)
                    line = source.count("\n", 0, marker.start()) + 1
                    dispositions.append({
                        "id": f"river:{path}:{marker[1]}", "source_file": path, "line": line,
                        "source_url": f"{metadata['repository']}/blob/{metadata['commit']}/{path}#L{line}",
                        "raw_sql": source[marker.start():end], "disposition": "excluded",
                        "reason": "SQLC :copyfrom command uses the binary-copy API, not a submitted SQL constant",
                    })
        outputs[app] = included
        ledgers[app] = {"commit": metadata["commit"], "candidate_count": len(dispositions),
                        "included": len(included), "excluded": len(dispositions) - len(included),
                        "oracle": "pglast 7.21 / PostgreSQL 17 grammar",
                        "scope": "syntax only; no execution or application-schema validity claim",
                        "dispositions": dispositions}
        if "expected_included" in metadata:
            assert len(included) == metadata["expected_included"], (app, "included inventory changed")
            assert len(dispositions) == metadata["expected_candidates"], (app, "candidate inventory changed")
    return outputs, ledgers


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--check", action="store_true", help="verify exact checked-in extraction")
    parser.add_argument("--fetch", action="store_true", help="refetch pinned source bytes before verification")
    args = parser.parse_args()
    manifest = json.loads((DIRECTORY / "application_sources.json").read_text())
    verify_sources(manifest, args.fetch)
    outputs, ledgers = extract(manifest)
    for app, cases in outputs.items():
        files = {
            DIRECTORY / f"{app}.jsonl": "".join(json.dumps(case, ensure_ascii=False) + "\n" for case in cases),
            DIRECTORY / f"{app}_extraction.json": json.dumps(ledgers[app], indent=2, ensure_ascii=False) + "\n",
        }
        for path, content in files.items():
            if args.check:
                assert path.read_text() == content, ("extraction differs", path)
            else:
                path.write_text(content, encoding="utf-8")
        print(f"PASS: {app}: {len(cases)} shipping-query constants; "
              f"{ledgers[app]['excluded']} explicitly recorded exclusions; "
              f"{dict(Counter(case['oracle_statement'] for case in cases))}")


if __name__ == "__main__":
    main()
