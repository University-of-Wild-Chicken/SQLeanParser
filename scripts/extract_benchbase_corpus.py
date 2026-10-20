#!/usr/bin/env python3
"""Extract pinned BenchBase SQLStmt templates without running upstream code.

Six workload families are covered, including their PostgreSQL overrides. This
is a source/template corpus, not a database execution benchmark. The evaluator
supports only Java literals, literal-valued static defaults, concatenation and
String.formatted(%s). Other expressions become explicit skipped inputs.

Regenerate from a local checkout:
  python3 scripts/extract_benchbase_corpus.py --source-root /path/to/benchbase
Download only the pinned input files, then regenerate:
  python3 scripts/extract_benchbase_corpus.py --download-to /tmp/benchbase-inputs
Offline integrity/provenance checks:
  python3 scripts/extract_benchbase_corpus.py --check
Re-extraction comparison (also verifies every input SHA-256):
  python3 scripts/extract_benchbase_corpus.py --source-root /path/to/benchbase --check
"""

from __future__ import annotations

import argparse
from collections import Counter
from dataclasses import dataclass
import hashlib
import json
from pathlib import Path
import re
import sys
from urllib.request import urlopen
import xml.parsers.expat

REPOSITORY = "https://github.com/cmu-db/benchbase"
REVISION = "33c00473807ebd49304d114a6d769d2d2b2bbb34"
ROOT = Path(__file__).resolve().parents[1]
OUTPUT = ROOT / "fixtures/external_postgresql"
JAVA_ROOT = "src/main/java/com/oltpbenchmark/benchmarks"
RESOURCE_ROOT = "src/main/resources/benchmarks"
FAMILIES = {
    "smallbank": ("SmallBankConstants", (
        "Amalgamate", "Balance", "DepositChecking", "SendPayment",
        "TransactSavings", "WriteCheck")),
    "tatp": ("TATPConstants", (
        "DeleteCallForwarding", "GetAccessData", "GetNewDestination",
        "GetSubscriberData", "InsertCallForwarding", "UpdateLocation",
        "UpdateSubscriberData")),
    "tpcc": ("TPCCConstants", (
        "Delivery", "NewOrder", "OrderStatus", "Payment", "StockLevel", "TPCCProcedure")),
    "tpch": ("TPCHConstants", ("GenericQuery", *(f"Q{i}" for i in range(1, 23)))),
    "twitter": ("TwitterConstants", (
        "GetFollowers", "GetTweet", "GetTweetsFromFollowing", "GetUserTweets", "InsertTweet")),
    "ycsb": ("YCSBConstants", (
        "DeleteRecord", "InsertRecord", "ReadModifyWriteRecord", "ReadRecord",
        "ScanRecord", "UpdateRecord")),
}


class ExtractionError(ValueError):
    """An input is outside the deliberately small, non-executing extractor."""


def sha256(data: bytes) -> str:
    return hashlib.sha256(data).hexdigest()


def source_url(path: str, line: int | None = None) -> str:
    return f"{REPOSITORY}/blob/{REVISION}/{path}" + (f"#L{line}" if line else "")


def input_paths() -> dict[str, str]:
    paths = {"LICENSE": "license"}
    for filename in ("Procedure", "SQLStmt"):
        paths[f"src/main/java/com/oltpbenchmark/api/{filename}.java"] = "runtime_reference"
    for family, (constants, procedures) in FAMILIES.items():
        paths[f"{JAVA_ROOT}/{family}/{constants}.java"] = "static_defaults"
        for procedure in procedures:
            paths[f"{JAVA_ROOT}/{family}/procedures/{procedure}.java"] = "procedure"
    for family in ("tpch", "twitter"):
        paths[f"{RESOURCE_ROOT}/{family}/dialect-postgres.xml"] = "postgres_override"
    return dict(sorted(paths.items()))


@dataclass(frozen=True)
class Token:
    text: str
    start: int
    end: int
    kind: str = "symbol"


def java_tokens(text: str) -> list[Token]:
    """Lex enough Java to locate declarations, excluding comments and strings."""
    if re.search(r"\\u+[0-9a-fA-F]{4}", text):
        raise ExtractionError("Java Unicode preprocessing is not supported")
    result = []
    i = 0
    while i < len(text):
        start = i
        if text[i].isspace():
            i += 1
            continue
        if text.startswith("//", i):
            end = text.find("\n", i + 2)
            i = len(text) if end < 0 else end + 1
            continue
        if text.startswith("/*", i):
            end = text.find("*/", i + 2)
            if end < 0:
                raise ExtractionError("unterminated Java comment")
            i = end + 2
            continue
        if text[i] in "\"'":
            delimiter = '"""' if text.startswith('"""', i) else text[i]
            i += len(delimiter)
            while i < len(text) and not text.startswith(delimiter, i):
                i += 2 if text[i] == "\\" else 1
            if i >= len(text):
                raise ExtractionError("unterminated Java literal")
            i += len(delimiter)
            kind = "string" if delimiter != "'" else "char"
        elif text[i].isalpha() or text[i] in "_$":
            i += 1
            while i < len(text) and (text[i].isalnum() or text[i] in "_$"):
                i += 1
            kind = "identifier"
        elif text[i].isdigit():
            i += 1
            while i < len(text) and (text[i].isalnum() or text[i] in "._"):
                i += 1
            kind = "number"
        else:
            i += 1
            kind = "symbol"
        result.append(Token(text[start:i], start, i, kind))
    return result


def java_string(token: str) -> str:
    """Decode the supported Java literal subset, including text-block indentation."""
    block = token.startswith('"""')
    text = token[3:-3] if block else token[1:-1]
    if block:
        text = text.replace("\r\n", "\n").replace("\r", "\n")
        opening = re.match(r"[ \t]*\n", text)
        if not opening:
            raise ExtractionError("text block must begin with a newline")
        lines = text[opening.end():].split("\n")
        determining = [line for line in lines if line.strip()]
        if not lines[-1].strip():
            determining.append(lines[-1])
        indent = min((len(line) - len(line.lstrip(" \t")) for line in determining), default=0)
        text = "\n".join(line[indent:].rstrip(" \t") for line in lines)
    escapes = {"b": "\b", "t": "\t", "n": "\n", "f": "\f", "r": "\r",
               '"': '"', "'": "'", "\\": "\\", "s": " "}
    result = []
    i = 0
    while i < len(text):
        if text[i] != "\\":
            result.append(text[i])
            i += 1
            continue
        i += 1
        if i == len(text):
            raise ExtractionError("trailing Java escape")
        char = text[i]
        if char in escapes:
            result.append(escapes[char])
            i += 1
        elif char == "\n" and block:
            i += 1
        elif char in "01234567":
            length = 3 if char in "0123" else 2
            end = i + 1
            while end < min(i + length, len(text)) and text[end] in "01234567":
                end += 1
            result.append(chr(int(text[i:end], 8)))
            i = end
        else:
            raise ExtractionError(f"unsupported Java escape: {char!r}")
    return "".join(result)


class LiteralEvaluator:
    """A small expression interpreter; never eval(), compile(), or run Java."""

    def __init__(self, tokens: list[Token], constants: dict):
        self.tokens = tokens
        self.constants = constants
        self.index = 0
        self.used: set[str] = set()

    def peek(self, text: str) -> bool:
        return self.index < len(self.tokens) and self.tokens[self.index].text == text

    def take(self, text: str) -> None:
        if not self.peek(text):
            raise ExtractionError(f"expected {text!r} in literal expression")
        self.index += 1

    def expression(self) -> str | int:
        value = self.atom()
        while self.peek("+"):
            self.index += 1
            right = self.atom()
            value = str(value) + str(right) if isinstance(value, str) or isinstance(right, str) else value + right
        return value

    def atom(self) -> str | int:
        if self.index == len(self.tokens):
            raise ExtractionError("incomplete literal expression")
        token = self.tokens[self.index]
        self.index += 1
        if token.kind == "string":
            value = java_string(token.text)
        elif token.kind == "number" and re.fullmatch(r"[0-9]+[lL]?", token.text):
            value = int(token.text.rstrip("lL"))
        elif token.text == "(":
            value = self.expression()
            self.take(")")
        elif token.kind == "identifier":
            name = token.text
            while self.peek(".") and self.index + 1 < len(self.tokens) and self.tokens[self.index + 1].text != "formatted":
                self.index += 1
                name += "." + self.tokens[self.index].text
                self.index += 1
            if name not in self.constants:
                raise ExtractionError(f"unresolved static value {name}")
            self.used.add(name)
            value = self.constants[name]["value"]
        else:
            raise ExtractionError(f"unsupported literal expression near {token.text!r}")
        if self.peek("."):
            self.index += 1
            self.take("formatted")
            self.take("(")
            arguments = []
            if not self.peek(")"):
                arguments.append(self.expression())
                while self.peek(","):
                    self.index += 1
                    arguments.append(self.expression())
            self.take(")")
            if not isinstance(value, str):
                raise ExtractionError("formatted receiver is not a string")
            chunks = re.split(r"(%.)", value)
            consumed = 0
            for i, chunk in enumerate(chunks):
                if chunk == "%%":
                    chunks[i] = "%"
                elif chunk == "%s":
                    if consumed == len(arguments):
                        raise ExtractionError("too few formatted arguments")
                    chunks[i] = str(arguments[consumed])
                    consumed += 1
                elif chunk.startswith("%"):
                    raise ExtractionError("only %s and %% formatting are supported")
            if consumed != len(arguments):
                raise ExtractionError("unused formatted arguments")
            value = "".join(chunks)
        return value

    def evaluate(self) -> str | int:
        value = self.expression()
        if self.index != len(self.tokens):
            raise ExtractionError("dynamic or unsupported expression suffix")
        return value


def split_arguments(tokens: list[Token], start: int) -> tuple[list[list[Token]], int]:
    """Split the contents of an opening '('; return its matching closing index."""
    depth = 0
    begin = start + 1
    result = []
    for i in range(begin, len(tokens)):
        text = tokens[i].text
        if text in ("(", "[", "{"):
            depth += 1
        elif text in (")", "]", "}"):
            if depth == 0:
                if text != ")":
                    raise ExtractionError("mismatched constructor delimiter")
                if i > begin:
                    result.append(tokens[begin:i])
                return result, i
            depth -= 1
        elif text == "," and depth == 0:
            result.append(tokens[begin:i])
            begin = i + 1
    raise ExtractionError("unterminated SQLStmt constructor")


def read_constants(text: str, path: str) -> dict:
    tokens = java_tokens(text)
    result = {}
    owner = Path(path).stem
    for i in range(len(tokens) - 4):
        if tokens[i].text != "static":
            continue
        j = i + 1
        final = tokens[j].text == "final"
        j += int(final)
        if tokens[j].text not in ("String", "int", "long"):
            continue
        if tokens[j + 1].kind != "identifier" or tokens[j + 2].text != "=":
            continue
        end = next((k for k in range(j + 3, len(tokens)) if tokens[k].text == ";"), None)
        if end is None:
            raise ExtractionError("unterminated static declaration")
        try:
            value = LiteralEvaluator(tokens[j + 3:end], {}).evaluate()
        except ExtractionError:
            continue  # Only literal initializers are eligible; references fail closed.
        name = owner + "." + tokens[j + 1].text
        result[name] = {
            "name": name, "value": value, "final": final, "source_file": path,
            "source_line": text.count("\n", 0, tokens[i].start) + 1,
        }
    return result


def read_overrides(text: str, path: str) -> dict:
    """Use an XML parser for entity decoding and original statement line numbers."""
    parser = xml.parsers.expat.ParserCreate()
    result = {}
    dialect = None
    procedure = None
    current = None
    content: list[str] = []

    def start(name, attrs):
        nonlocal dialect, procedure, current, content
        if name == "dialect":
            dialect = attrs.get("type")
        elif name == "procedure":
            procedure = attrs["name"]
        elif name == "statement" and dialect == "POSTGRES":
            current = (procedure, attrs["name"])
            if current in result:
                raise ExtractionError(f"duplicate XML override {current}")
            result[current] = {"source_file": path, "source_line": parser.CurrentLineNumber}
            content = []

    def end(name):
        nonlocal current, dialect
        if name == "statement" and current:
            result[current]["sql"] = "".join(content)
            current = None
        elif name == "dialect":
            dialect = None

    def characters(data):
        if current:
            content.append(data)

    def reject_doctype(*_args):
        raise ExtractionError("XML DTDs and external entities are not supported")

    parser.StartElementHandler = start
    parser.EndElementHandler = end
    parser.CharacterDataHandler = characters
    parser.StartDoctypeDeclHandler = reject_doctype
    parser.Parse(text, True)
    return result


def number_parameters(sql: str) -> tuple[str, int]:
    """Translate JDBC bind markers outside SQL quotes/comments to $1, $2, ... .

    Assumes PostgreSQL standard_conforming_strings=on. E'...' strings retain
    their escape semantics. An unexpanded SQLStmt '??' is an error.
    """
    result = []
    i = count = 0
    while i < len(sql):
        start = i
        if sql.startswith("--", i):
            end = sql.find("\n", i + 2)
            i = len(sql) if end < 0 else end + 1
        elif sql.startswith("/*", i):
            i += 2
            depth = 1
            while i < len(sql) and depth:
                if sql.startswith("/*", i):
                    depth += 1
                    i += 2
                elif sql.startswith("*/", i):
                    depth -= 1
                    i += 2
                else:
                    i += 1
            if depth:
                raise ExtractionError("unterminated SQL block comment")
        elif sql[i] in "'\"":
            quote = sql[i]
            escaped = quote == "'" and i > 0 and sql[i - 1] in "eE" and (
                i == 1 or not (sql[i - 2].isalnum() or sql[i - 2] in "_$"))
            i += 1
            while i < len(sql):
                if escaped and sql[i] == "\\":
                    i += 2
                elif sql[i] == quote:
                    i += 1
                    if i < len(sql) and sql[i] == quote:
                        i += 1
                    else:
                        break
                else:
                    i += 1
            else:
                raise ExtractionError("unterminated SQL quoted value")
        elif sql[i] == "$":
            match = re.match(r"\$(?:[A-Za-z_][A-Za-z_0-9]*)?\$", sql[i:])
            if match:
                delimiter = match.group()
                end = sql.find(delimiter, i + len(delimiter))
                if end < 0:
                    raise ExtractionError("unterminated SQL dollar quote")
                i = end + len(delimiter)
            elif re.match(r"\$[0-9]", sql[i:]):
                raise ExtractionError("mixed numbered and JDBC parameters")
            else:
                i += 1
        elif sql[i] == "?":
            if sql.startswith("??", i):
                raise ExtractionError("unexpanded SQLStmt placeholder list")
            count += 1
            result.append(f"${count}")
            i += 1
            continue
        else:
            i += 1
        result.append(sql[start:i])
    return "".join(result), count


def normalize_sql(raw: str, substitutions: list[int]) -> tuple[str, int, list[str]]:
    sql = raw
    transformations = []
    for count in substitutions:
        if not 0 < count <= 1000 or "??" not in sql:
            raise ExtractionError("invalid or missing SQLStmt list substitution")
        # SQLStmt.setSQL uses Java replaceFirst("\\?\\?", ...), including on overrides.
        sql = sql.replace("??", ", ".join("?" for _ in range(count)), 1)
    if substitutions:
        transformations.append("sqlstmt_double_question_expansion")
    if sql != sql.strip():
        transformations.append("trim_outer_whitespace")
    sql = sql.strip()
    sql, count = number_parameters(sql)
    if count:
        transformations.append("jdbc_to_postgresql_parameters")
    return sql, count, transformations


def extract(source_root: Path) -> tuple[list[dict], dict]:
    paths = input_paths()
    inputs = []
    contents = {}
    for path, role in paths.items():
        data = (source_root / path).read_bytes()
        contents[path] = data.decode("utf-8")
        inputs.append({"path": path, "role": role, "sha256": sha256(data),
                       "bytes": len(data), "source_url": source_url(path)})
    all_constants = {}
    for path, role in paths.items():
        if role == "static_defaults":
            all_constants.update(read_constants(contents[path], path))
    records = []
    skipped = []
    counts = Counter()
    empty_procedures = []
    used_constants = {}
    applied_overrides = 0
    for family, (_owner, procedures) in FAMILIES.items():
        override_path = f"{RESOURCE_ROOT}/{family}/dialect-postgres.xml"
        overrides = read_overrides(contents[override_path], override_path) if override_path in contents else {}
        seen_overrides = set()
        for procedure in procedures:
            path = f"{JAVA_ROOT}/{family}/procedures/{procedure}.java"
            text = contents[path]
            tokens = java_tokens(text)
            constants = dict(all_constants)
            for match in re.finditer(r"import\s+static\s+[\w.]+\.([A-Za-z_]\w*)\.([A-Za-z_]\w*)\s*;", text):
                name = f"{match[1]}.{match[2]}"
                if name in constants:
                    constants[match[2]] = constants[name]
            constructors = 0
            for i in range(len(tokens) - 2):
                if [t.text for t in tokens[i:i + 3]] != ["new", "SQLStmt", "("]:
                    continue
                constructors += 1
                counts[family] += 1
                line = text.count("\n", 0, tokens[i].start) + 1
                statement = tokens[i - 2].text if i >= 3 and tokens[i - 1].text == "=" and tokens[i - 3].text == "SQLStmt" else f"anonymous_at_{line}"
                identity = f"benchbase:{family}:{procedure}:{statement}"
                base = {"id": identity, "source": f"benchbase:{family}",
                        "procedure": procedure, "statement": statement,
                        "source_file": path, "source_line": line,
                        "source_url": source_url(path, line)}
                try:
                    arguments, end = split_arguments(tokens, i + 2)
                    if not arguments:
                        raise ExtractionError("empty SQLStmt constructor")
                    evaluators = [LiteralEvaluator(arg, constants) for arg in arguments]
                    values = [evaluator.evaluate() for evaluator in evaluators]
                    default_sql, *substitutions = values
                    if not isinstance(default_sql, str) or any(type(n) is not int for n in substitutions):
                        raise ExtractionError("SQLStmt requires a string and integer substitution counts")
                    raw = default_sql
                    transformations = ["java_literal_expression_decoded"]
                    used = sorted({constants[name]["name"] for evaluator in evaluators for name in evaluator.used})
                    if used:
                        transformations.append("declared_static_defaults_substituted")
                        used_constants.update({name: all_constants[name] for name in used})
                    origin = dict(base)
                    override = overrides.get((procedure, statement))
                    if override:
                        seen_overrides.add((procedure, statement))
                        applied_overrides += 1
                        raw = override["sql"]
                        base.update({k: override[k] for k in ("source_file", "source_line")})
                        base["source_url"] = source_url(base["source_file"], base["source_line"])
                        transformations.append("postgres_dialect_override")
                    sql, parameter_count, sql_transformations = normalize_sql(raw, substitutions)
                    record = {
                        **base, "revision": REVISION, "sql": sql, "raw_sql": raw,
                        "transformations": transformations + sql_transformations,
                        "sqlstmt_substitutions": substitutions,
                        "parameter_count": parameter_count, "static_defaults": used,
                        "java_origin": {k: origin[k] for k in ("source_file", "source_line", "source_url")},
                        "java_expression": text[tokens[i + 3].start:tokens[end].start],
                    }
                    if override:
                        record["java_default_sql"] = default_sql
                    if family == "tpch" and procedure == "Q15":
                        record["caveats"] = [
                            "Q15 uses CREATE VIEW, a dependent SELECT, then DROP VIEW.",
                            "Its runtime substitutes date literals into CREATE VIEW; this corpus retains the source bind template.",
                        ]
                    records.append(record)
                except ExtractionError as exc:
                    skipped.append({**base, "reason": str(exc)})
            if not constructors:
                empty_procedures.append(path)
        unknown = set(overrides) - seen_overrides
        for procedure, statement in sorted(unknown):
            skipped.append({
                "id": f"benchbase:{family}:{procedure}:{statement}:unapplied_override",
                "source": f"benchbase:{family}", **overrides[(procedure, statement)],
                "reason": "PostgreSQL override had no successfully extracted SQLStmt",
            })
    records.sort(key=lambda record: record["id"])
    if len({record["id"] for record in records}) != len(records):
        raise ExtractionError("duplicate query identifiers")
    metadata = {
        "format_version": 1,
        "repository": REPOSITORY,
        "revision": REVISION,
        "revision_date": "2025-12-13T21:00:56Z",
        "license": {
            "spdx": "Apache-2.0",
            "upstream_license_url": source_url("LICENSE"),
            "upstream_license_copy": "licenses/benchbase-LICENSE",
            "license_text": "licenses/Apache-2.0.txt",
            "attribution": "licenses/benchbase-ATTRIBUTION",
            "upstream_notice_file": None,
            "copyright": ["Copyright 2021 by OLTPBenchmark Project",
                          "Copyright 2020 by OLTPBenchmark Project (Java source headers)"],
        },
        "selection": {
            "workloads": list(FAMILIES),
            "scope": "Every SQLStmt constructor in every procedures/*.java file of the six selected families, with the families' PostgreSQL XML overrides.",
            "not_in_scope": [
                "Other BenchBase workloads, loader-generated SQL and schema DDL.",
                "Runtime-generated SQL outside SQLStmt constructors and non-PostgreSQL overrides.",
                "All possible settings of mutable static fields; declared defaults are recorded.",
                "Native database execution, parameter values, data generation and transaction scheduling.",
            ],
            "no_constructor_files": sorted(empty_procedures),
        },
        "extraction": {
            "script": "scripts/extract_benchbase_corpus.py",
            "upstream_code_executed": False,
            "parameter_rule": "JDBC '?' outside quotes/comments becomes occurrence-numbered '$n'; SQLStmt '??' lists first expand with recorded constructor counts.",
            "constructor_count": sum(counts.values()),
            "constructors_by_workload": dict(sorted(counts.items())),
            "postgres_overrides_applied": applied_overrides,
            "static_defaults_used": [used_constants[name] for name in sorted(used_constants)],
            "skipped_inputs": skipped,
        },
        "record_count": len(records),
        "records_by_workload": dict(sorted(Counter(r["source"] for r in records).items())),
        "statement_kinds": dict(sorted(Counter(r["sql"].split()[0].upper() for r in records).items())),
        "inputs": inputs,
    }
    metadata["corpus_sha256"] = sha256(encode_records(records))
    return records, metadata


def encode_records(records: list[dict]) -> bytes:
    return "".join(json.dumps(record, ensure_ascii=False, sort_keys=True) + "\n" for record in records).encode()


def encode_metadata(metadata: dict) -> bytes:
    return (json.dumps(metadata, indent=2, ensure_ascii=False, sort_keys=True) + "\n").encode()


def verify_snapshot(output: Path) -> dict:
    data = (output / "benchbase.jsonl").read_bytes()
    metadata = json.loads((output / "benchbase_sources.json").read_bytes())
    records = [json.loads(line) for line in data.splitlines()]
    if metadata["revision"] != REVISION or metadata["repository"] != REPOSITORY:
        raise ExtractionError("unexpected upstream revision")
    if sha256(data) != metadata["corpus_sha256"] or len(records) != metadata["record_count"]:
        raise ExtractionError("corpus hash/count mismatch")
    if len({record["id"] for record in records}) != len(records):
        raise ExtractionError("duplicate identifiers")
    inventory = {entry["path"]: entry for entry in metadata["inputs"]}
    if set(inventory) != set(input_paths()):
        raise ExtractionError("input inventory differs from the fixed workload selection")
    counts = Counter(record["source"] for record in records)
    if dict(sorted(counts.items())) != metadata["records_by_workload"]:
        raise ExtractionError("workload counts differ")
    skipped_constructors = [entry for entry in metadata["extraction"]["skipped_inputs"]
                            if not entry["id"].endswith(":unapplied_override")]
    if len(records) + len(skipped_constructors) != metadata["extraction"]["constructor_count"]:
        raise ExtractionError("SQLStmt input denominator is inconsistent")
    for record in records:
        if record["revision"] != REVISION or record["source_file"] not in inventory:
            raise ExtractionError("record provenance mismatch")
        if record["source_url"] != source_url(record["source_file"], record["source_line"]):
            raise ExtractionError("record source URL mismatch")
        sql, count, transformations = normalize_sql(record["raw_sql"], record["sqlstmt_substitutions"])
        if (sql, count) != (record["sql"], record["parameter_count"]):
            raise ExtractionError("record normalization mismatch")
        if transformations and record["transformations"][-len(transformations):] != transformations:
            raise ExtractionError("record transformations mismatch")
    license_copy = (output / metadata["license"]["upstream_license_copy"]).read_bytes()
    if sha256(license_copy) != inventory["LICENSE"]["sha256"]:
        raise ExtractionError("upstream LICENSE copy mismatch")
    license_paths = {"licenses/benchbase-LICENSE", "licenses/Apache-2.0.txt",
                     "licenses/benchbase-ATTRIBUTION"}
    if set(metadata["license_file_sha256"]) != license_paths:
        raise ExtractionError("license/attribution inventory mismatch")
    for path, digest in metadata["license_file_sha256"].items():
        if sha256((output / path).read_bytes()) != digest:
            raise ExtractionError(f"license/attribution hash mismatch: {path}")
    return metadata


def verify_source_inputs(source_root: Path, reference: Path = OUTPUT) -> None:
    """Do not relabel a locally edited checkout as the pinned upstream revision."""
    metadata = verify_snapshot(reference)
    for entry in metadata["inputs"]:
        path = source_root / entry["path"]
        if sha256(path.read_bytes()) != entry["sha256"]:
            raise ExtractionError(f"input differs from pinned upstream bytes: {entry['path']}")


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    source = parser.add_mutually_exclusive_group()
    source.add_argument("--source-root", type=Path)
    source.add_argument("--download-to", type=Path, help="explicitly download fixed-revision source files here")
    parser.add_argument("--output-dir", type=Path, default=OUTPUT)
    parser.add_argument("--check", action="store_true")
    args = parser.parse_args()
    try:
        source_root = args.source_root or args.download_to
        if args.download_to:
            for path in input_paths():
                destination = source_root / path
                destination.parent.mkdir(parents=True, exist_ok=True)
                url = f"https://raw.githubusercontent.com/cmu-db/benchbase/{REVISION}/{path}"
                with urlopen(url, timeout=30) as response:
                    destination.write_bytes(response.read())
        if source_root:
            verify_source_inputs(source_root)
            records, metadata = extract(source_root)
            for name in ("benchbase-LICENSE", "Apache-2.0.txt", "benchbase-ATTRIBUTION"):
                relative = "licenses/" + name
                license_path = args.output_dir / relative
                if not args.check:
                    license_data = ((source_root / "LICENSE").read_bytes()
                                    if name == "benchbase-LICENSE"
                                    else (OUTPUT / relative).read_bytes())
                    license_path.parent.mkdir(parents=True, exist_ok=True)
                    license_path.write_bytes(license_data)
                metadata.setdefault("license_file_sha256", {})[relative] = sha256(license_path.read_bytes())
            if args.check:
                if (args.output_dir / "benchbase.jsonl").read_bytes() != encode_records(records):
                    raise ExtractionError("re-extracted corpus differs")
                if (args.output_dir / "benchbase_sources.json").read_bytes() != encode_metadata(metadata):
                    raise ExtractionError("re-extracted manifest or input hashes differ")
            else:
                args.output_dir.mkdir(parents=True, exist_ok=True)
                (args.output_dir / "benchbase.jsonl").write_bytes(encode_records(records))
                (args.output_dir / "benchbase_sources.json").write_bytes(encode_metadata(metadata))
        elif not args.check:
            parser.error("provide --source-root or --download-to to regenerate; --check works offline")
        metadata = verify_snapshot(args.output_dir)
        print(f"BenchBase: {metadata['record_count']} SQL templates; "
              f"{metadata['extraction']['constructor_count']} constructors; "
              f"{len(metadata['extraction']['skipped_inputs'])} skipped inputs; "
              f"{metadata['extraction']['postgres_overrides_applied']} PostgreSQL overrides")
        return 0
    except (OSError, ValueError, KeyError, xml.parsers.expat.ExpatError) as exc:
        print(f"BenchBase extraction failed: {exc}", file=sys.stderr)
        return 1


if __name__ == "__main__":
    raise SystemExit(main())
