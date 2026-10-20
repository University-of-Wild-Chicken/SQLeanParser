#!/usr/bin/env python3
"""Replay every legacy SELECT through the checked rendering CLI.

The inventory is fixed at 1,237 SELECTs. Identity and PostgreSQL profiles must
render every entry and recheck their canonical SQL. The 400 portable SELECTs
also run through the SQLite profile and native SQLite on empty/seeded fixtures.
These are finite serialization/execution observations, not universal semantics
or an assertion that the two database dialects have interchangeable behavior.
"""
from __future__ import annotations

from collections import Counter
from contextlib import ExitStack, closing
from dataclasses import dataclass
import hashlib
import json
from pathlib import Path
import sqlite3
import subprocess

from check_industrial_cli import industrial_database
from check_relational_cli import create_database

ROOT = Path(__file__).resolve().parents[1]
EXE = ROOT / ".lake/build/bin/sqlean"
EXPECTED_FAMILIES = {"basic": 100, "crud": 50, "relational": 200,
                     "industrial": 150, "postgresql": 250, "advanced": 487}
PROFILES = {"identity": "sqlean-select-render-v0.1",
            "postgres": "postgresql-16-select-render-v0.1",
            "sqlite": "sqlite-3.39-select-render-v0.1"}
THEOREMS = {
    "SQLean.RenderContract.check_roundTrip", "SQLean.RenderContract.check_admissible",
    "SQLean.RenderContract.check_canonical", "SQLean.RenderContract.render_expected_stable",
    "SQLean.RenderContract.Certificate.parameter_slots_injective",
    "SQLean.RenderContract.Certificate.parameter_map_complete",
    "SQLean.RenderContract.Certificate.transport_preserves",
}
FOUNDATIONS = {"Lean kernel", "propext", "Classical.choice", "Quot.sound",
               "Lean compiler/runtime for executable reports"}
ASSUMPTIONS = {
    "identity": ["server_encoding=UTF8", "client_encoding=UTF8", "standard_conforming_strings=on",
                 "max_identifier_length=63", "same catalog, search_path, and namespace interpretation"],
    "sqlite": ["SQLite>=3.39.0", "UTF8 input", "SQLITE_LIMIT_VARIABLE_NUMBER>=32766",
               "profile identifier limit=63 UTF8 bytes", "same database, namespace, and collation settings",
               "SQLite native types, NULL behavior and identifier rules; no PostgreSQL semantic equivalence"],
}
ASSUMPTIONS["postgres"] = ASSUMPTIONS["identity"]
ADVANCED_SELECTIONS = {
    **{name: tuple(range(1, 51)) for name in (
        "in_subqueries", "exists", "lateral", "using_joins", "natural_joins",
        "intersect", "except", "floating")},
    "nulls": (*range(1, 44), 49, 50),
    "placeholders": (*range(1, 22), *range(26, 47)),
    **{name: () for name in ("upsert", "insert_select", "create_table", "alter_table", "drop_table")},
}


@dataclass(frozen=True)
class CorpusFile:
    family: str
    path: str
    count: int
    selected: tuple[int, ...]


@dataclass(frozen=True)
class Case:
    family: str
    path: str
    index: int
    sql: str

    @property
    def key(self):
        return f"{self.path}:{self.index}"


def inventory():
    files = [CorpusFile("basic", "fixtures/queries.sql", 100, tuple(range(1, 101)))]
    categories = {
        "crud": ("select",),
        "relational": ("joins", "grouping", "subqueries", "ctes"),
        "industrial": ("recursive_ctes", "unions", "source_free"),
        "postgresql": ("distinct_on", "aggregate_filter", "casts", "predicates", "null_ordering"),
    }
    files.extend(CorpusFile(family, f"fixtures/{family}/{category}.sql", 50, tuple(range(1, 51)))
                 for family, names in categories.items() for category in names)
    files.extend(CorpusFile("advanced", f"fixtures/advanced/{name}.sql", 50, selected)
                 for name, selected in ADVANCED_SELECTIONS.items())
    return files


def load_file(root, entry):
    lines = (root / entry.path).read_text(encoding="utf-8").splitlines()
    assert len(lines) == entry.count, (entry.path, "changed fixture count", len(lines), entry.count)
    assert all(line.strip() for line in lines), (entry.path, "blank fixture")
    assert len(set(lines)) == len(lines), (entry.path, "duplicate fixture")
    assert len(set(entry.selected)) == len(entry.selected)
    assert all(1 <= index <= entry.count for index in entry.selected)
    return lines


def sql_tokens(sql, mode):
    """Small independent lexical observer, not a SQL parser.

    Observe parameters and outer ORDER BY, ignoring strings, quoted names and
    comments. PostgreSQL block comments nest; SQLite comments do not.
    """
    i, depth, ordinal = 0, 0, 0
    tokens = []
    while i < len(sql):
        if sql.startswith("--", i):
            end = sql.find("\n", i + 2)
            i = len(sql) if end < 0 else end + 1
        elif sql.startswith("/*", i):
            nesting = 1
            i += 2
            while i < len(sql) and nesting:
                if sql.startswith("*/", i):
                    nesting -= 1
                    i += 2
                elif mode != "sqlite" and sql.startswith("/*", i):
                    nesting += 1
                    i += 2
                else:
                    i += 1
            assert nesting == 0, "unterminated observed comment"
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
            else:
                raise AssertionError("unterminated observed quoted text")
        elif sql[i] in "?$":
            marker = sql[i]
            i += 1
            start = i
            while i < len(sql) and sql[i].isdigit():
                i += 1
            digits = sql[start:i]
            if digits:
                assert marker == "$" or mode == "sqlite", "unexpected numbered question marker"
                parameter = ("numbered", int(digits))
            else:
                assert marker == "?", "bare dollar marker"
                ordinal += 1
                parameter = ("anonymous", ordinal)
            assert parameter[1] > 0
            tokens.append(("parameter", parameter, depth))
        elif sql[i] == "(":
            depth += 1
            i += 1
        elif sql[i] == ")":
            depth -= 1
            assert depth >= 0
            i += 1
        elif sql[i].isalpha() or sql[i] == "_":
            start = i
            i += 1
            while i < len(sql) and (sql[i].isalnum() or sql[i] in "_$"):
                i += 1
            tokens.append(("word", sql[start:i].upper(), depth))
        else:
            i += 1
    assert depth == 0, "unbalanced observed parentheses"
    return tokens


def parameters(sql, mode):
    return [value for kind, value, _ in sql_tokens(sql, mode) if kind == "parameter"]


def ordered(sql):
    words = [value for kind, value, depth in sql_tokens(sql, "sqlite") if kind == "word" and depth == 0]
    return any(words[i:i + 2] == ["ORDER", "BY"] for i in range(len(words) - 1))


def load_inventory(root=ROOT):
    metadata = json.loads((root / "fixtures/advanced/cases.json").read_text())
    assert set(metadata) == set(ADVANCED_SELECTIONS), "advanced metadata categories changed"
    cases = []
    for entry in inventory():
        lines = load_file(root, entry)
        if entry.family == "advanced":
            category = Path(entry.path).stem
            assert [case["sql"] for case in metadata[category]] == lines, entry.path
            # Exclusions are fixed statement identities, never parser failures.
            for index, sql in enumerate(lines, 1):
                first = next(value for kind, value, _ in sql_tokens(sql, "identity") if kind == "word")
                assert (first in ("SELECT", "WITH")) == (index in entry.selected), (entry.path, index)
        cases.extend(Case(entry.family, entry.path, index, lines[index - 1]) for index in entry.selected)
    assert Counter(case.family for case in cases) == EXPECTED_FAMILIES
    assert len(cases) == len({case.key for case in cases}) == 1237
    assert len({case.sql for case in cases}) == 1237, "duplicate SQL across corpus files"
    return cases


def unique_json(pairs):
    result = {}
    for key, value in pairs:
        assert key not in result, ("duplicate JSON key", key)
        result[key] = value
    return result


def validate_report(result, mode, source):
    report = json.loads(result.stdout, object_pairs_hook=unique_json)
    assert isinstance(report, dict), report
    status = report.get("status")
    if status != "rendered":
        assert not ({"sql", "parameterMap", "theorems"} & report.keys()), report
        assert report.get("evidence") == "none", report
        raise AssertionError(("unexpected renderer failure; no corpus entry may be skipped", status,
                              report.get("diagnostic"), result.returncode))
    assert result.returncode == 0, (result.returncode, report, result.stderr)
    expected = {"profile": PROFILES[mode], "mode": mode, "assurance": "checked-roundtrip",
                "evidence": "checked-instance", "rendererVersion": "0.2",
                "scope": "SELECT AST serialization; independent target semantics not established"}
    for key, value in expected.items():
        assert report.get(key) == value, (key, report)
    assert report.get("semanticPreservation") is False and "diagnostic" not in report, report
    assert set(report.get("theorems", [])) == THEOREMS, report
    assert set(report.get("trustedFoundations", [])) == FOUNDATIONS, report
    assert report.get("assumptions") == ASSUMPTIONS[mode], report
    sql = report.get("sql")
    assert isinstance(sql, str) and sql.endswith(";") and sql.strip(), report
    logical = parameters(source, mode)
    assert len({style for style, _ in logical}) <= 1, "mixed fixture parameter styles"
    expected_map = [{"source": {"style": style, "index": slot}, "target": slot}
                    for style, slot in dict.fromkeys(logical)]
    assert report.get("parameterMap") == expected_map, ("incorrect binding map", report, expected_map)
    for entry in report["parameterMap"]:
        assert type(entry["source"]["index"]) is int and type(entry["target"]) is int, report
    emitted = logical if mode == "identity" else [("numbered", slot) for _, slot in logical]
    assert parameters(sql, mode) == emitted, ("changed parameter occurrences", source, report)
    return report


def invoke(mode, sql):
    result = subprocess.run([str(EXE), "--render-assurance", mode, sql], cwd=ROOT,
                            capture_output=True, text=True, timeout=30, check=False)
    return validate_report(result, mode, sql)


def replay(mode, sql, invoke_fn=invoke):
    report = invoke_fn(mode, sql)
    canonical = invoke_fn(mode, report["sql"])
    assert canonical["sql"] == report["sql"], ("canonical bytes changed", report, canonical)
    # The canonical query's anonymous markers become numbered under translation.
    expected_map = [{"source": {"style": entry["source"]["style"] if mode == "identity" else "numbered",
                                "index": entry["target"]}, "target": entry["target"]}
                    for entry in report["parameterMap"]]
    assert canonical["parameterMap"] == expected_map, ("canonical binding map changed", report, canonical)
    return report


def typed_rows(rows):
    return [tuple((type(value).__name__, value) for value in row) for row in rows]


def compare_rows(source, original, canonical):
    arity, rows = original
    other_arity, other_rows = canonical
    assert arity == other_arity, ("changed result arity", source, original, canonical)
    left, right = typed_rows(rows), typed_rows(other_rows)
    if ordered(source):
        assert left == right, ("changed ordered finite observation", source, left, right)
    else:
        assert Counter(left) == Counter(right), ("changed result bag", source, left, right)


def observe(db, sql):
    """Bound each prepare/fetch to 500,000 SQLite VM instructions."""
    callbacks = 0

    def progress():
        nonlocal callbacks
        callbacks += 1
        return callbacks >= 500

    db.set_progress_handler(progress, 1000)
    try:
        cursor = db.execute(sql)
        labels = [column[0] for column in cursor.description]
        return (len(labels), cursor.fetchall()), labels
    finally:
        db.set_progress_handler(None, 0)


def load_label_expectations(cases, root=ROOT):
    expected = json.loads((root / "fixtures/renderer_label_expectations.json").read_text(),
                          object_pairs_hook=unique_json)
    assert len(expected) == 54, "reviewed generated-label exception count changed"
    portable = {case.key: case for case in cases if case.family in ("crud", "relational", "industrial")}
    assert expected.keys() <= portable.keys(), "label expectation refers to a missing SELECT"
    for key, entry in expected.items():
        assert set(entry) == {"sourceSha256", "sourceLabels", "renderedLabels"}, (key, entry)
        assert hashlib.sha256(portable[key].sql.encode()).hexdigest() == entry["sourceSha256"], key
        assert entry["sourceLabels"] != entry["renderedLabels"], key
        assert len(entry["sourceLabels"]) == len(entry["renderedLabels"]), key
    return expected


def compare_labels(key, source_labels, rendered_labels, expectations):
    if key in expectations:
        expected = expectations[key]
        assert source_labels == expected["sourceLabels"], (key, source_labels, expected)
        assert rendered_labels == expected["renderedLabels"], (key, rendered_labels, expected)
        return True
    assert source_labels == rendered_labels, ("unreviewed output-label difference", key,
                                              source_labels, rendered_labels)
    return False


def database(root, family, populated):
    schema = json.loads((root / f"fixtures/{family}/schema.json").read_text())
    if family == "industrial":
        return industrial_database(schema, populated)
    if family == "relational":
        return create_database(schema, populated)
    db = create_database(schema, False)
    if populated:
        db.executemany("INSERT INTO users VALUES (?, ?, ?, ?)", [
            (1, 24, "Alice", "Paris"), (2, 17, "Bob", "Paris"), (3, 38, "Carol", "Rome"),
            (4, 71, "Dora", "Rome"), (5, 33, "O'Brien", ""), (6, 40, "Fran", "Paris")])
        db.executemany("INSERT INTO inventory VALUES (?, ?, ?, ?)", [
            (1, 120, 4, "Hammer"), (2, 50, 0, "Nail"), (3, 50, 7, "O'Brien"),
            (4, 0, 2, ""), (5, 220, 1, "Drill")])
        db.executemany("INSERT INTO flags VALUES (?, ?, ?)", [
            (1, True, "Enabled"), (2, False, "Disabled"), (3, True, "Preview")])
    return db


def main():
    if not EXE.is_file():
        raise SystemExit("Build the CLI first: lake build")
    if sqlite3.sqlite_version_info < (3, 39, 0):
        raise SystemExit("SQLite 3.39 or newer is required")
    cases = load_inventory()
    label_expectations = load_label_expectations(cases)
    digest = hashlib.sha256(json.dumps([(c.key, c.sql) for c in cases],
                                      separators=(",", ":")).encode()).hexdigest()
    count = comparisons = 0
    observed_label_differences = set()
    with ExitStack() as stack:
        databases = {(family, populated): stack.enter_context(closing(database(ROOT, family, populated)))
                     for family in ("crud", "relational", "industrial") for populated in (False, True)}
        for case in cases:
            try:
                for mode in ("identity", "postgres"):
                    replay(mode, case.sql)
                    count += 1
                if case.family in ("crud", "relational", "industrial"):
                    rendered = replay("sqlite", case.sql)
                    assert rendered["parameterMap"] == [], case.key
                    for populated in (False, True):
                        db = databases[case.family, populated]
                        original, source_labels = observe(db, case.sql)
                        canonical, rendered_labels = observe(db, rendered["sql"])
                        compare_rows(case.sql, original, canonical)
                        if compare_labels(case.key, source_labels, rendered_labels, label_expectations):
                            observed_label_differences.add(case.key)
                        comparisons += 1
            except Exception as error:
                raise AssertionError(f"renderer corpus failure at {case.key}: {case.sql}") from error
    assert count == 2474 and comparisons == 800
    assert observed_label_differences == label_expectations.keys()
    print(f"PASS: 1237 inventoried SELECTs; {count} identity/PostgreSQL renders with canonical rechecks")
    print(f"PASS: SQLite {sqlite3.sqlite_version}; 400 renders with canonical rechecks; "
          f"{comparisons} bounded empty/seeded comparisons")
    print("PASS: 346 cases preserve labels; 54 reviewed generated-label differences match exact expected pairs")
    print(f"SELECT inventory SHA256: {digest}")
    print("Scope: finite AST-serialization, binding-map, arity and typed-row observations; "
          "no universal semantics or general output-label equivalence claim.")


if __name__ == "__main__":
    main()
