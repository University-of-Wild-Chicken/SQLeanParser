"""Offline regressions for inventory, evidence, binding and native result checks."""
from copy import deepcopy
import json
from pathlib import Path
import sqlite3
import subprocess
import tempfile
import unittest
from unittest.mock import patch

from check_renderer_corpus import (
    ADVANCED_SELECTIONS, ASSUMPTIONS, CorpusFile, EXPECTED_FAMILIES, FOUNDATIONS,
    PROFILES, ROOT, THEOREMS, compare_labels, compare_rows, load_file, load_inventory,
    load_label_expectations, observe, ordered, parameters, replay, validate_report,
)


def report(mode, source, sql):
    logical = parameters(source, mode)
    return {
        "profile": PROFILES[mode], "mode": mode, "status": "rendered",
        "assurance": "checked-roundtrip", "evidence": "checked-instance",
        "rendererVersion": "0.2", "semanticPreservation": False,
        "scope": "SELECT AST serialization; independent target semantics not established",
        "theorems": sorted(THEOREMS), "trustedFoundations": sorted(FOUNDATIONS),
        "assumptions": ASSUMPTIONS[mode], "sql": sql,
        "parameterMap": [{"source": {"style": style, "index": slot}, "target": slot}
                         for style, slot in dict.fromkeys(logical)],
    }


def completed(value, code=0):
    return subprocess.CompletedProcess([], code, json.dumps(value), "")


class RendererCorpusTests(unittest.TestCase):
    def test_complete_inventory_and_advanced_statement_identities(self):
        cases = load_inventory()
        self.assertEqual(len(cases), 1237)
        self.assertEqual({family: sum(c.family == family for c in cases) for family in EXPECTED_FAMILIES},
                         EXPECTED_FAMILIES)
        self.assertEqual(ADVANCED_SELECTIONS["nulls"], (*range(1, 44), 49, 50))
        self.assertEqual(ADVANCED_SELECTIONS["placeholders"], (*range(1, 22), *range(26, 47)))
        self.assertEqual(sum(not indices for indices in ADVANCED_SELECTIONS.values()), 5)
        # A valid basic query begins with a comment: prefix filtering loses it.
        leading = next(c for c in cases if c.path == "fixtures/queries.sql" and c.index == 93)
        self.assertTrue(leading.sql.startswith("/*"))
        self.assertEqual(len(load_label_expectations(cases)), 54)

    def test_fixture_count_missing_duplicate_and_blank_fail_closed(self):
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            entry = CorpusFile("basic", "queries.sql", 2, (1, 2))
            with self.assertRaises(FileNotFoundError):
                load_file(root, entry)
            for text in ("SELECT 1;\n", "SELECT 1;\nSELECT 2;\nSELECT 3;\n",
                         "SELECT 1;\nSELECT 1;\n", "SELECT 1;\n\n"):
                (root / entry.path).write_text(text)
                with self.subTest(text=text), self.assertRaises(AssertionError):
                    load_file(root, entry)

    def test_cross_file_duplicate_sql_is_rejected(self):
        duplicate = (ROOT / "fixtures/crud/select.sql").read_text().splitlines()[0]

        def modified(root, entry):
            lines = load_file(root, entry)
            if entry.family == "basic":
                lines[0] = duplicate
            return lines

        with patch("check_renderer_corpus.load_file", side_effect=modified):
            with self.assertRaisesRegex(AssertionError, "duplicate SQL across"):
                load_inventory()

    def test_stale_or_unknown_label_expectations_are_rejected(self):
        cases = load_inventory()
        original = load_label_expectations(cases)
        key = next(iter(original))
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            (root / "fixtures").mkdir()
            for mutate in ("hash", "unknown", "missing"):
                expected = deepcopy(original)
                if mutate == "hash":
                    expected[key]["sourceSha256"] = "0" * 64
                elif mutate == "unknown":
                    expected["unknown:1"] = expected.pop(key)
                else:
                    del expected[key]
                (root / "fixtures/renderer_label_expectations.json").write_text(json.dumps(expected))
                with self.subTest(mutate=mutate), self.assertRaises(AssertionError):
                    load_label_expectations(cases, root)

    def test_lexical_parameter_identity_ignores_quotes_and_comments(self):
        source = """SELECT $2, '$9''?', "$8""?", $1, $2
                    -- $7 ?
                    /* $6 /* $5 */ $4 */"""
        self.assertEqual(parameters(source, "postgres"),
                         [("numbered", 2), ("numbered", 1), ("numbered", 2)])
        self.assertEqual(parameters("WITH c AS (SELECT ?) SELECT ?, '?' FROM c", "identity"),
                         [("anonymous", 1), ("anonymous", 2)])
        self.assertEqual(parameters("SELECT price$1, $2, column$3 FROM table$4", "postgres"),
                         [("numbered", 2)])

    def test_comment_dialects_have_different_parameter_visibility(self):
        self.assertEqual(parameters("SELECT ?1 /* /* */ + ?2 -- */", "sqlite"),
                         [("numbered", 1), ("numbered", 2)])
        self.assertEqual(parameters("SELECT $1 /* /* */ + $2 -- */", "postgres"),
                         [("numbered", 1)])

    def test_top_level_order_ignores_subqueries_strings_and_comments(self):
        for sql in ("WITH c AS (SELECT 1 ORDER BY 1) SELECT * FROM c",
                    "SELECT * FROM (SELECT 1 ORDER BY 1) q",
                    "SELECT 'ORDER BY', \"ORDER BY\" /* ORDER BY */"):
            self.assertFalse(ordered(sql), sql)
        self.assertTrue(ordered("WITH c AS (SELECT 1) SELECT * FROM c ORDER /*comment*/ BY 1"))

    def test_success_evidence_and_anonymous_translation(self):
        for mode, rendered in (("identity", "SELECT ?, ?;"),
                               ("postgres", "SELECT $1, $2;"),
                               ("sqlite", "SELECT ?1, ?2;")):
            value = report(mode, "SELECT ?, ?", rendered)
            self.assertEqual(validate_report(completed(value), mode, "SELECT ?, ?"), value)

    def test_reordered_repeated_numbered_slots_are_exact(self):
        source = "SELECT $2, $1, $2"
        value = report("postgres", source, source + ";")
        validate_report(completed(value), "postgres", source)
        for bad_map in (value["parameterMap"][::-1], value["parameterMap"][:1],
                        value["parameterMap"] + value["parameterMap"][:1]):
            bad = {**value, "parameterMap": bad_map}
            with self.assertRaises(AssertionError):
                validate_report(completed(bad), "postgres", source)

    def test_semantic_evidence_and_foundation_mutations_are_rejected(self):
        value = report("identity", "SELECT 1", "SELECT 1;")
        for field, bad_value in (
            ("evidence", "none"), ("semanticPreservation", True), ("semanticPreservation", 0),
            ("assurance", "syntax-only"), ("profile", PROFILES["sqlite"]), ("mode", "sqlite"),
            ("rendererVersion", "unknown"), ("scope", "universal semantics"),
            ("theorems", []), ("trustedFoundations", ["custom axiom"]), ("assumptions", []),
        ):
            with self.subTest(field=field), self.assertRaises(AssertionError):
                validate_report(completed({**value, field: bad_value}), "identity", "SELECT 1")
        with self.assertRaises(AssertionError):
            validate_report(completed(value, code=3), "identity", "SELECT 1")

    def test_parameter_styles_slots_occurrences_and_boolean_indexes_are_rejected(self):
        source = "SELECT ?, ?"
        value = report("postgres", source, "SELECT $1, $2;")
        for field, bad_value in (
            ("style", "numbered"), ("index", 2), ("index", True), ("target", 2), ("target", True),
        ):
            bad = deepcopy(value)
            if field == "target":
                bad["parameterMap"][0][field] = bad_value
            else:
                bad["parameterMap"][0]["source"][field] = bad_value
            with self.subTest(field=field, value=bad_value), self.assertRaises(AssertionError):
                validate_report(completed(bad), "postgres", source)
        for sql in ("SELECT $2, $1;", "SELECT $1;", "SELECT $1, $1;", "SELECT ?, ?;"):
            with self.subTest(sql=sql), self.assertRaises(AssertionError):
                validate_report(completed({**value, "sql": sql}), "postgres", source)

    def test_nonparameter_queries_cannot_claim_bindings(self):
        value = report("identity", "SELECT '$1', '?'", "SELECT '$1', '?';")
        value["parameterMap"] = [{"source": {"style": "numbered", "index": 1}, "target": 1}]
        with self.assertRaises(AssertionError):
            validate_report(completed(value), "identity", "SELECT '$1', '?'")

    def test_every_renderer_failure_is_fatal_and_must_not_publish_sql(self):
        for status in ("invalid", "unsupported", "inconclusive", "mismatch", "unknown"):
            value = {"status": status, "evidence": "none",
                     "diagnostic": {"code": "test", "message": "test"}}
            with self.subTest(status=status), self.assertRaisesRegex(AssertionError, "may be skipped"):
                validate_report(completed(value, 1), "identity", "SELECT 1")
            with self.assertRaises(AssertionError):
                validate_report(completed({**value, "sql": "SELECT 1;"}), "identity", "SELECT 1")

    def test_duplicate_json_fields_are_rejected(self):
        result = subprocess.CompletedProcess([], 0, '{"status":"rendered","status":"unsupported"}', "")
        with self.assertRaisesRegex(AssertionError, "duplicate JSON key"):
            validate_report(result, "identity", "SELECT 1")

    def test_canonical_recheck_accounts_for_parameter_style_translation(self):
        first = report("postgres", "SELECT ?, ?", "SELECT $1, $2;")
        canonical = report("postgres", first["sql"], first["sql"])
        outputs = iter((first, canonical))
        self.assertEqual(replay("postgres", "SELECT ?, ?", lambda *_: next(outputs)), first)
        for bad in ({**canonical, "sql": "SELECT $1;"}, first,
                    {**canonical, "parameterMap": canonical["parameterMap"][::-1]}):
            outputs = iter((first, bad))
            with self.assertRaises(AssertionError):
                replay("postgres", "SELECT ?, ?", lambda *_: next(outputs))

    def test_bag_comparison_preserves_duplicates_nulls_and_runtime_types(self):
        compare_rows("SELECT x FROM t", (1, [(1,), (None,), (1,)]), (1, [(1,), (1,), (None,)]))
        for wrong in ((1, [(1,), (None,)]), (1, [(1,), ("NULL",), (1,)]),
                      (1, [(1.0,), (None,), (1,)]), (2, [(1, None), (None, 1), (1, None)])):
            with self.subTest(wrong=wrong), self.assertRaises(AssertionError):
                compare_rows("SELECT x FROM t", (1, [(1,), (None,), (1,)]), wrong)

    def test_ordered_observation_rejects_row_reordering(self):
        with self.assertRaises(AssertionError):
            compare_rows("SELECT x FROM t ORDER BY x", (1, [(1,), (2,)]), (1, [(2,), (1,)]))
        compare_rows("SELECT x FROM (SELECT x FROM t ORDER BY x) q",
                     (1, [(1,), (2,)]), (1, [(2,), (1,)]))

    def test_exact_reviewed_labels_reject_unrelated_or_changed_differences(self):
        expected = {"case": {"sourceLabels": ["x + 1", "stable"],
                             "renderedLabels": ['("x" + 1)', "stable"]}}
        self.assertTrue(compare_labels("case", ["x + 1", "stable"],
                                       ['("x" + 1)', "stable"], expected))
        self.assertFalse(compare_labels("other", ["stable"], ["stable"], expected))
        for key, original, canonical in (
            ("other", ["x"], ["y"]), ("case", ["x + 1", "stable"], ['("x" + 1)', "lost"]),
            ("case", ["changed", "stable"], ['("x" + 1)', "stable"]),
        ):
            with self.subTest(key=key), self.assertRaises(AssertionError):
                compare_labels(key, original, canonical, expected)

    def test_native_execution_is_bounded_and_handler_is_removed(self):
        with sqlite3.connect(":memory:") as db:
            with self.assertRaisesRegex(sqlite3.OperationalError, "interrupted"):
                observe(db, "WITH RECURSIVE r(n) AS (SELECT 1 UNION ALL SELECT n+1 FROM r) SELECT n FROM r")
            # Do not call observe here: that would replace a leaked exhausted
            # handler and conceal a missing finally cleanup.
            result = db.execute("WITH RECURSIVE r(n) AS "
                                "(SELECT 1 UNION ALL SELECT n+1 FROM r WHERE n<1000) "
                                "SELECT SUM(n) FROM r").fetchall()
            self.assertEqual(result, [(500500,)])
            self.assertEqual(observe(db, "SELECT 1 AS n"), ((1, [(1,)]), ["n"]))


if __name__ == "__main__":
    unittest.main()
