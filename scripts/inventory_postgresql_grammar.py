#!/usr/bin/env python3
"""Inventory the pinned PostgreSQL 16 grammar using GNU Bison's XML report.

The upstream C actions are parsed by Bison, never compiled or executed. This
inventory is not a SQL parser, a coverage percentage, or a validity certificate.
Default operation and --check are offline. --download restores only pinned,
hash-checked input bytes.
"""
from __future__ import annotations

import argparse
from collections import Counter
import hashlib
import json
import os
from pathlib import Path
import re
import subprocess
import tempfile
from urllib.request import urlopen
import xml.etree.ElementTree as ET

ROOT = Path(__file__).resolve().parents[1]
FIXTURES = ROOT / "fixtures/postgresql_grammar"
COMMIT = "f0595c3d839debdb140903621c1b44a4f4d86256"
VERSION = "16.15"
BISON_VERSION = "3.8.2"
INPUTS = (
    "COPYRIGHT", "configure.ac", "src/backend/parser/gram.y",
    "src/backend/parser/scan.l", "src/backend/parser/parser.c",
    "src/include/parser/kwlist.h",
)
SOURCE_BASE = f"https://raw.githubusercontent.com/postgres/postgres/{COMMIT}/"

# This is a reviewed AST-interface inventory, not generated evidence of
# production coverage. No family is labeled completely supported.
PARTIAL_FAMILIES = {
    "SelectStmt": "Advanced.Query: expanded SELECT subset; independent validity covers the narrower basic profile.",
    "InsertStmt": "Advanced.Insert: VALUES/SELECT/DEFAULT VALUES, conflict and RETURNING subset.",
    "UpdateStmt": "Advanced.Update: single target with assignments, predicate and RETURNING; no complete UPDATE grammar.",
    "DeleteStmt": "Advanced.Delete: single target with predicate and RETURNING; no complete DELETE grammar.",
    "CreateStmt": "Advanced.CreateTable: restricted CREATE TABLE and metadata; no complete table-definition grammar.",
    "AlterTableStmt": "Advanced.AlterTable: selected column/constraint actions; no complete ALTER TABLE grammar.",
    "DropStmt": "Advanced.DropTable: table-only subset of the shared DROP production.",
    "RenameStmt": "Advanced.AlterTable: table/column renaming only.",
}

# Every entry point must be classified explicitly. New upstream alternatives
# fail inventory generation until this partition has been reviewed.
FAMILY_GROUPS = {
    "query": "SelectStmt",
    "mutation": "InsertStmt UpdateStmt DeleteStmt MergeStmt",
    "transaction-and-locking": "TransactionStmt TransactionStmtLegacy ConstraintsSetStmt LockStmt",
    "cursor": "DeclareCursorStmt ClosePortalStmt FetchStmt",
    "prepared-statement": "PrepareStmt ExecuteStmt DeallocateStmt",
    "maintenance": "AnalyzeStmt CheckPointStmt ClusterStmt ReindexStmt VacuumStmt",
    "session": "VariableResetStmt VariableSetStmt VariableShowStmt DiscardStmt",
    "copy": "CopyStmt",
    "notification": "ListenStmt NotifyStmt UnlistenStmt",
    "procedural-invocation": "CallStmt DoStmt LoadStmt",
    "explain": "ExplainStmt",
    "privilege-and-ownership": "GrantStmt GrantRoleStmt RevokeStmt RevokeRoleStmt DropOwnedStmt ReassignOwnedStmt",
    "schema-and-object-definition": """
        AlterEventTrigStmt AlterCollationStmt AlterDatabaseStmt AlterDatabaseSetStmt
        AlterDefaultPrivilegesStmt AlterDomainStmt AlterEnumStmt AlterExtensionStmt
        AlterExtensionContentsStmt AlterFdwStmt AlterForeignServerStmt AlterFunctionStmt
        AlterGroupStmt AlterObjectDependsStmt AlterObjectSchemaStmt AlterOwnerStmt
        AlterOperatorStmt AlterTypeStmt AlterPolicyStmt AlterSeqStmt AlterSystemStmt
        AlterTableStmt AlterTblSpcStmt AlterCompositeTypeStmt AlterPublicationStmt
        AlterRoleSetStmt AlterRoleStmt AlterSubscriptionStmt AlterStatsStmt
        AlterTSConfigurationStmt AlterTSDictionaryStmt AlterUserMappingStmt
        CommentStmt CreateAmStmt CreateAsStmt CreateAssertionStmt CreateCastStmt
        CreateConversionStmt CreateDomainStmt CreateExtensionStmt CreateFdwStmt
        CreateForeignServerStmt CreateForeignTableStmt CreateFunctionStmt CreateGroupStmt
        CreateMatViewStmt CreateOpClassStmt CreateOpFamilyStmt CreatePublicationStmt
        AlterOpFamilyStmt CreatePolicyStmt CreatePLangStmt CreateSchemaStmt CreateSeqStmt
        CreateStmt CreateSubscriptionStmt CreateStatsStmt CreateTableSpaceStmt
        CreateTransformStmt CreateTrigStmt CreateEventTrigStmt CreateRoleStmt CreateUserStmt
        CreateUserMappingStmt CreatedbStmt DefineStmt DropCastStmt DropOpClassStmt
        DropOpFamilyStmt DropStmt DropSubscriptionStmt DropTableSpaceStmt DropTransformStmt
        DropRoleStmt DropUserMappingStmt DropdbStmt ImportForeignSchemaStmt IndexStmt
        RefreshMatViewStmt RemoveAggrStmt RemoveFuncStmt RemoveOperStmt RenameStmt
        RuleStmt SecLabelStmt TruncateStmt ViewStmt
    """,
}

FEATURE_GAPS = [
    ("expression-and-function-grammar", ["a_expr", "b_expr", "func_application", "func_expr_common_subexpr"],
     "Partial scalar subset; general calls, special forms and full precedence remain incomplete."),
    ("conditional-expressions", ["case_expr"],
     "CASE and the complete PostgreSQL conditional-expression family require AST and independent rules."),
    ("arrays-and-row-values", ["array_expr", "row", "explicit_row", "implicit_row", "opt_array_bounds"],
     "Arrays, subscripts, row constructors and their typing are not complete."),
    ("window-and-ordered-aggregates", ["window_clause", "over_clause", "within_group_clause"],
     "Window frames and ordered-set aggregate syntax are not complete."),
    ("locking-and-pagination", ["for_locking_clause", "select_limit"],
     "Expression LIMIT/OFFSET is partial; locking, FETCH forms and complete clause order remain incomplete."),
    ("general-type-names", ["Typename", "GenericType"],
     "Built-in type increment is partial; qualified/custom types, arrays and all modifiers remain incomplete."),
    ("table-functions-and-xml", ["func_table", "xmltable"],
     "Table functions, XML constructs and complete FROM grammar require additional AST and contracts."),
    ("mutation-grammar", ["MergeStmt", "UpdateStmt", "DeleteStmt", "InsertStmt"],
     "MERGE, joined mutations, complete WITH/DML and assignment forms remain incomplete."),
    ("object-definition", ["CreateStmt", "AlterTableStmt", "DefineStmt", "ViewStmt"],
     "Restricted table DDL does not cover the complete object-definition grammar."),
    ("lexing-and-token-filter", [],
     "The existing lexer does not cover all scan.l states or parser.c lookahead/Unicode transformations."),
]


class InventoryError(ValueError):
    pass


def sha256(data: bytes) -> str:
    return hashlib.sha256(data).hexdigest()


def load_manifest(directory: Path) -> dict:
    manifest = json.loads((directory / "sources.json").read_text())
    if manifest.get("commit") != COMMIT or manifest.get("version") != VERSION:
        raise InventoryError("source manifest does not identify the pinned PostgreSQL revision/version")
    files = manifest.get("files", [])
    if len(files) != len(INPUTS) or {x.get("path") for x in files} != set(INPUTS):
        raise InventoryError("source manifest must list exactly the pinned six input files")
    for record in files:
        if record.get("source_url") != SOURCE_BASE + record["path"]:
            raise InventoryError("source URL does not match the pinned commit")
        if not re.fullmatch(r"[0-9a-f]{64}", record.get("sha256", "")):
            raise InventoryError("invalid input digest")
    return manifest


def verify_sources(directory: Path, manifest: dict) -> None:
    for record in manifest["files"]:
        path = directory / "source" / record["path"]
        if not path.is_file():
            raise InventoryError(f"missing upstream input: {record['path']}")
        data = path.read_bytes()
        if sha256(data) != record["sha256"] or len(data) != record["bytes"]:
            raise InventoryError(f"upstream input hash/size mismatch: {record['path']}")
    configure = (directory / "source/configure.ac").read_text()
    if f"AC_INIT([PostgreSQL], [{VERSION}]," not in configure:
        raise InventoryError("configure.ac does not identify the declared PostgreSQL version")


def download_sources(directory: Path, manifest: dict) -> None:
    # Validate every response before replacing any local file.
    downloaded = []
    for record in manifest["files"]:
        with urlopen(record["source_url"], timeout=60) as response:
            data = response.read()
        if sha256(data) != record["sha256"] or len(data) != record["bytes"]:
            raise InventoryError(f"downloaded input does not match pinned digest: {record['path']}")
        downloaded.append((record["path"], data))
    for name, data in downloaded:
        destination = directory / "source" / name
        destination.parent.mkdir(parents=True, exist_ok=True)
        destination.write_bytes(data)


def c_tokens(source: str) -> list[str]:
    """Lex enough C preprocessing tokens to read kwlist.h, ignoring comments.

    It is deliberately not used to split the Bison grammar. Escaped quotes and
    braces inside C strings/comments remain data, not macro invocations.
    """
    result, index, length = [], 0, len(source)
    while index < length:
        if source[index].isspace():
            index += 1
        elif source.startswith("/*", index):
            end = source.find("*/", index + 2)
            if end < 0:
                raise InventoryError("unterminated C block comment")
            index = end + 2
        elif source.startswith("//", index):
            end = source.find("\n", index + 2)
            index = length if end < 0 else end + 1
        elif source[index] in "\"'":
            start, quote = index, source[index]
            index += 1
            while index < length:
                if source[index] == "\\":
                    index += 2
                elif source[index] == quote:
                    index += 1
                    result.append(source[start:index])
                    break
                else:
                    index += 1
            else:
                raise InventoryError("unterminated C string/character literal")
        elif source[index].isalpha() or source[index] == "_":
            start = index
            index += 1
            while index < length and (source[index].isalnum() or source[index] == "_"):
                index += 1
            result.append(source[start:index])
        else:
            result.append(source[index])
            index += 1
    return result


def parse_keywords(source: str) -> list[dict]:
    tokens = c_tokens(source)
    records, index = [], 0
    categories = {"UNRESERVED_KEYWORD", "COL_NAME_KEYWORD", "TYPE_FUNC_NAME_KEYWORD", "RESERVED_KEYWORD"}
    while index < len(tokens):
        if tokens[index] != "PG_KEYWORD":
            index += 1
            continue
        row = tokens[index:index + 10]
        if len(row) != 10 or [row[i] for i in (1, 3, 5, 7, 9)] != ["(", ",", ",", ",", ")"]:
            raise InventoryError("malformed PG_KEYWORD macro")
        try:
            spelling = json.loads(row[2])
        except (ValueError, TypeError) as error:
            raise InventoryError("keyword spelling must be a quoted string") from error
        if not isinstance(spelling, str) or not re.fullmatch("[a-z_]+", spelling):
            raise InventoryError("unexpected keyword spelling")
        if row[6] not in categories or row[8] not in {"BARE_LABEL", "AS_LABEL"}:
            raise InventoryError("unknown keyword category/label classification")
        records.append({"spelling": spelling, "token": row[4], "category": row[6], "label": row[8]})
        index += 10
    if len({r["spelling"] for r in records}) != len(records) or len({r["token"] for r in records}) != len(records):
        raise InventoryError("duplicate keyword spelling/token")
    if [r["spelling"] for r in records] != sorted(r["spelling"] for r in records):
        raise InventoryError("keyword entries are not in canonical ASCII order")
    return records


def bison_report(grammar: Path, *, bison: str = "bison") -> ET.Element:
    with tempfile.TemporaryDirectory(prefix="sqlean-grammar-inventory-") as temporary:
        output = Path(temporary)
        command = [bison, "-Wno-deprecated", "-Wno-other",
                   "--xml=" + str(output / "grammar.xml"), "--report=all",
                   "--report-file=" + str(output / "grammar.output"),
                   "-o", str(output / "grammar.c"), str(grammar)]
        try:
            process = subprocess.run(command, capture_output=True, text=True,
                                     timeout=60, env={**os.environ, "LC_ALL": "C"})
        except (OSError, subprocess.TimeoutExpired) as error:
            raise InventoryError(f"cannot run the required Bison {BISON_VERSION}: {error}") from error
        if process.returncode:
            raise InventoryError(f"Bison rejected the grammar:\n{process.stderr}")
        root = ET.parse(output / "grammar.xml").getroot()
        if root.tag != "bison-xml-report" or root.get("version") != BISON_VERSION:
            raise InventoryError(f"inventory requires Bison {BISON_VERSION}, found {root.get('version')}")
        return root


def grammar_records(report: ET.Element) -> tuple[list[dict], list[dict], list[dict]]:
    grammar = report.find("grammar")
    if grammar is None:
        raise InventoryError("Bison report lacks a grammar")
    productions = []
    for rule in grammar.findall("rules/rule"):
        productions.append({
            "id": int(rule.attrib["number"]),
            "lhs": rule.findtext("lhs"),
            "rhs": [symbol.text for symbol in rule.findall("rhs/symbol")],
            "attributes": {k: v for k, v in rule.attrib.items() if k != "number"},
        })
    terminals = [dict(item.attrib) for item in grammar.findall("terminals/terminal")]
    nonterminals = [dict(item.attrib) for item in grammar.findall("nonterminals/nonterminal")]
    if not productions or [r["id"] for r in productions] != list(range(len(productions))):
        raise InventoryError("Bison production IDs must be consecutive and unique")
    terminal_names = {t["name"] for t in terminals}
    nonterminal_names = {n["name"] for n in nonterminals}
    if len(terminal_names) != len(terminals) or len(nonterminal_names) != len(nonterminals):
        raise InventoryError("duplicate grammar symbol")
    if terminal_names & nonterminal_names:
        raise InventoryError("terminal/nonterminal namespaces overlap")
    for rule in productions:
        if rule["lhs"] not in nonterminal_names or any(s not in terminal_names | nonterminal_names for s in rule["rhs"]):
            raise InventoryError("production references an undeclared grammar symbol")
    return productions, terminals, nonterminals


def statement_families(productions: list[dict]) -> list[dict]:
    groups = {}
    for category, names in FAMILY_GROUPS.items():
        for name in names.split():
            if name in groups:
                raise InventoryError(f"duplicate statement category for {name}")
            groups[name] = category
    entries = []
    for rule in productions:
        if rule["lhs"] not in {"stmt", "toplevel_stmt"} or not rule["rhs"] or rule["rhs"] == ["stmt"]:
            continue
        if len(rule["rhs"]) != 1:
            raise InventoryError("statement entry is not a single family nonterminal")
        name = rule["rhs"][0]
        entries.append({
            "name": name, "entry_production": rule["id"], "category": groups.get(name),
            "sqlean_ast_coverage": "partial" if name in PARTIAL_FAMILIES else "not-implemented",
            "scope": PARTIAL_FAMILIES.get(name, "No corresponding production AST interface is implemented."),
            "production_coverage": "not-measured",
            "full_independent_validity": False,
            "full_renderer_contract": False,
            "upstream_action_note": (
                "The C action reports feature-not-supported; CFG derivability does not imply PostgreSQL acceptance."
                if name == "CreateAssertionStmt" else None),
        })
    names = {entry["name"] for entry in entries}
    if len(names) != len(entries) or names != set(groups):
        raise InventoryError(f"statement category partition changed: new={sorted(names-set(groups))}, stale={sorted(set(groups)-names)}")
    if not set(PARTIAL_FAMILIES) <= names:
        raise InventoryError("partial-coverage annotation names an absent statement family")
    return entries


def build_inventory(directory: Path = FIXTURES, *, bison: str = "bison") -> dict:
    manifest = load_manifest(directory)
    verify_sources(directory, manifest)
    report = bison_report(directory / "source/src/backend/parser/gram.y", bison=bison)
    productions, terminals, nonterminals = grammar_records(report)
    keywords = parse_keywords((directory / "source/src/include/parser/kwlist.h").read_text())
    terminal_names = {t["name"] for t in terminals}
    if any(keyword["token"] not in terminal_names for keyword in keywords):
        raise InventoryError("keyword table refers to an unknown grammar token")
    families = statement_families(productions)
    nonterminal_names = {n["name"] for n in nonterminals}
    if any(name not in nonterminal_names for _, roots, _ in FEATURE_GAPS for name in roots):
        raise InventoryError("feature-gap annotation refers to an absent grammar production")
    states = report.findall("automaton/state")
    return {
        "format_version": 1,
        "upstream": {k: manifest[k] for k in ("repository", "commit", "version", "license")},
        "inputs": manifest["files"],
        "generator": {
            "script": "scripts/inventory_postgresql_grammar.py",
            "bison_version": report.attrib["version"],
            "method": "Bison XML rules/symbols/automaton; C action bodies are never compiled or executed.",
        },
        "counts": {
            "source_productions": sum(r["lhs"] != "$accept" for r in productions),
            "generated_accept_productions": sum(r["lhs"] == "$accept" for r in productions),
            "source_nonterminals": sum(n["name"] != "$accept" for n in nonterminals),
            "generated_accept_nonterminals": sum(n["name"] == "$accept" for n in nonterminals),
            "reported_terminals": len(terminals),
            "keyword_entries": len(keywords),
            "lalr_states": len(states),
            "precedence_resolutions": sum(len(s.findall("solved-conflicts/resolution")) for s in states),
            "statement_families": len(families),
            "statement_categories": dict(sorted(Counter(f["category"] for f in families).items())),
            "sqlean_ast_family_annotations": dict(sorted(Counter(f["sqlean_ast_coverage"] for f in families).items())),
        },
        "boundary": {
            "evidence": "pinned-grammar-inventory-only",
            "implements_parser": False,
            "proves_lexer_equivalence": False,
            "executes_postgresql_actions": False,
            "proves_typed_sql_validity": False,
            "proves_renderer_semantics": False,
            "warning": "CFG rules omit action-level rejection and depend on scan.l plus parser.c token transformations.",
        },
        "entry_modes": [r for r in productions if r["lhs"] == "parse_toplevel"],
        "statement_families": families,
        "feature_gaps": [{"id": name, "grammar_roots": roots, "scope": scope} for name, roots, scope in FEATURE_GAPS],
        "keywords": keywords,
        "terminals": terminals,
        "nonterminals": nonterminals,
        "productions": productions,
    }


def encoded(inventory: dict) -> str:
    return json.dumps(inventory, indent=2, ensure_ascii=False) + "\n"


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--check", action="store_true", help="rebuild offline and compare with the committed inventory")
    parser.add_argument("--download", action="store_true", help="restore source bytes from pinned URLs and verify all hashes")
    parser.add_argument("--bison", default="bison")
    parser.add_argument("--directory", type=Path, default=FIXTURES)
    args = parser.parse_args()
    try:
        if args.download:
            download_sources(args.directory, load_manifest(args.directory))
        inventory = build_inventory(args.directory, bison=args.bison)
        path = args.directory / "inventory.json"
        content = encoded(inventory)
        if args.check:
            if not path.is_file() or path.read_text() != content:
                raise InventoryError("stale PostgreSQL grammar inventory; regenerate and review the change")
        else:
            path.write_text(content)
        print("PASS: PostgreSQL", VERSION, "grammar inventory", json.dumps(inventory["counts"], sort_keys=True))
    except (InventoryError, OSError, ValueError, ET.ParseError) as error:
        raise SystemExit(str(error)) from error


if __name__ == "__main__":
    main()
