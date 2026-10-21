#!/usr/bin/env python3
"""Offline mutation tests for grammar CLI evidence and generated coverage."""
from __future__ import annotations

import json
from collections import Counter
from pathlib import Path
import tempfile
from types import SimpleNamespace
import unittest
from unittest.mock import patch

import check_postgresql_grammar_cli as cli
import generate_postgresql_grammar_examples as examples


class ReportTests(unittest.TestCase):
    SQL = "/* α */ SELECT 'λ'; -- end\n"
    DOMAIN = {"terminals": {"SELECT", "SCONST", "';'"},
              "families": {"SelectStmt"}, "production_count": 3285}

    def report(self):
        raw = self.SQL.encode()
        tokens = []
        for kind, value in [("SELECT", "SELECT"), ("SCONST", "'λ'"), ("';'", ";")]:
            start = raw.index(value.encode())
            tokens.append({"kind": kind, "lexeme": value, "start": start,
                           "end": start + len(value.encode())})
        return {**cli.COMMON, "status": "grammar-accepted",
                "evidence": "context-free-derivation", "sourcePreservation": "exact",
                "sql": self.SQL, "tokens": tokens, "productionIds": [1, 7, 125],
                "statementFamilies": ["SelectStmt"]}

    def check(self, report):
        return cli.validate_report(report, self.SQL, family="SelectStmt", domain=self.DOMAIN)

    def test_exact_utf8_spans_with_comments(self):
        self.check(self.report())

    def test_source_change_fails(self):
        report = self.report()
        report["sql"] += " "
        with self.assertRaisesRegex(AssertionError, "source bytes"):
            self.check(report)

    def test_false_assurance_or_wrong_revision_fails(self):
        for key, value in [("staticValidity", "valid"), ("grammarSemanticActions", "checked"),
                           ("profile", "postgresql"), ("postgresqlCommit", "0" * 40),
                           ("evidence", "kernel-proof-of-SQL-validity")]:
            with self.subTest(key=key):
                report = self.report()
                report[key] = value
                with self.assertRaises(AssertionError):
                    self.check(report)

    def test_missing_or_extra_field_fails(self):
        for field in self.report():
            with self.subTest(field=field):
                report = self.report()
                del report[field]
                with self.assertRaises(AssertionError):
                    self.check(report)
        report = self.report()
        report["typedProof"] = True
        with self.assertRaisesRegex(AssertionError, "fields"):
            self.check(report)

    def test_invalid_production_ids_fail(self):
        for ids in [[], [1, 1], [-1], [3285], [True], ["1"], None]:
            with self.subTest(ids=ids):
                report = self.report()
                report["productionIds"] = ids
                with self.assertRaises(AssertionError):
                    self.check(report)

    def test_wrong_or_nested_statement_family_fails(self):
        for families in [["unknown"], ["SelectStmt", "SelectStmt"], [], "SelectStmt", [None]]:
            with self.subTest(families=families):
                report = self.report()
                report["statementFamilies"] = families
                with self.assertRaises(AssertionError):
                    self.check(report)

    def test_byte_not_character_offsets_are_required(self):
        report = self.report()
        for token in report["tokens"]:
            token["start"] -= 1
            token["end"] -= 1
        with self.assertRaises(AssertionError):
            self.check(report)

    def test_token_overlap_and_noninteger_offsets_fail(self):
        for start, end in [(0, 0), (0, 999), (-1, 3), (True, 3), (3, 2)]:
            with self.subTest(span=(start, end)):
                report = self.report()
                report["tokens"][1].update(start=start, end=end)
                with self.assertRaises(AssertionError):
                    self.check(report)

    def test_missing_token_cannot_hide_as_trivia(self):
        for index in [0, 1, 2]:
            report = self.report()
            del report["tokens"][index]
            with self.assertRaisesRegex(AssertionError, "nontrivia"):
                self.check(report)

    def test_wrong_token_kind_or_spelling_fails(self):
        for mutation in [{"kind": "UNKNOWN"}, {"kind": 1}, {"lexeme": ""},
                         {"lexeme": "'x'"}, {"extra": True}]:
            with self.subTest(mutation=mutation):
                report = self.report()
                report["tokens"][1].update(mutation)
                with self.assertRaises(AssertionError):
                    self.check(report)

    def test_expected_contextual_tokens_are_checked(self):
        with self.assertRaisesRegex(AssertionError, "contextual"):
            cli.validate_report(self.report(), self.SQL, kinds=["SELECT"], domain=self.DOMAIN)

    def test_rejected_and_inconclusive_have_no_success_evidence(self):
        for status in ["grammar-rejected", "inconclusive"]:
            report = {**cli.COMMON, "status": status, "evidence": "none", "diagnostic": "reason"}
            cli.validate_report(report, self.SQL, status, domain=self.DOMAIN)
            for key, value in [("sql", self.SQL), ("productionIds", [1]),
                               ("evidence", "context-free-derivation")]:
                with self.subTest(status=status, key=key), self.assertRaises(AssertionError):
                    cli.validate_report({**report, key: value}, self.SQL, status, domain=self.DOMAIN)

    def test_duplicate_json_keys_and_nonfinite_values_fail(self):
        for raw in ['{"status":"x","status":"y"}', '{"tokens":[{"kind":"x","kind":"y"}]}',
                    '{"n":NaN}', '{"n":Infinity}', '{"n":-Infinity}']:
            with self.subTest(raw=raw), self.assertRaises(ValueError):
                cli.strict_json(raw)

    def test_trivia_lexer_handles_nesting_and_rejects_code(self):
        for raw in [b"", b" \t\n\r\f", b"-- x\n", b"/* /* */ */", "-- λ".encode()]:
            self.assertTrue(cli.trivia_only(raw), raw)
        for raw in [b"1", b";", b"/*", b"/* /* */", b"\v", b"'x'", b"--x\nSELECT"]:
            self.assertFalse(cli.trivia_only(raw), raw)

    def test_fixture_duplicate_ids_or_missing_sql_fail(self):
        with tempfile.TemporaryDirectory() as temporary, patch.object(cli, "ROOT", Path(temporary)):
            path = Path(temporary) / "cases.jsonl"
            for rows in [[{"id": "a", "sql": "SELECT 1"}] * 2,
                         [{"id": "a"}], [{"id": "", "sql": "SELECT 1"}]]:
                path.write_text("\n".join(json.dumps(row) for row in rows) + "\n")
                with self.assertRaises(AssertionError):
                    cli.read_cases(path)


class AuthoredSubqueryInputTests(unittest.TestCase):
    def test_quantified_query_populations_keep_only_authored_adapters(self):
        authored = [row for name in ("synthetic.json", "row_synthetic.json", "operator_direction.json")
                    for row in cli.read_cases(cli.ROOT / "fixtures/quantified_subqueries" / name)]
        originals = cli.read_cases(cli.ROOT / "fixtures/quantified_subqueries/concrete.jsonl")
        self.assertEqual((len(authored), len(originals)), (118, 84))
        self.assertEqual(sum("grammar_input_transformations" in row for row in authored), 2)
        self.assertEqual(Counter(row["query_class"] for row in originals), {"scalar":50,"row":34})
        self.assertTrue(all(row["sql"] == row["raw_sql"] and row["transformations"] == []
                            and "grammar_input_transformations" not in row for row in originals))

    def test_row_in_population_keeps_authored_adapters_separate_from_sources(self):
        authored = cli.read_cases(cli.ROOT / "fixtures/row_in_subqueries/synthetic.json")
        source = cli.read_cases(cli.ROOT / "fixtures/row_in_subqueries/concrete.jsonl")
        self.assertEqual((len(authored), len(source)), (50, 50))
        adapted = [row for row in authored if "grammar_input_transformations" in row]
        self.assertEqual(len(adapted), 2)
        self.assertTrue(all(row["grammar_input_origin"] == "authored-sqlean-parameter-fixture"
                            for row in adapted))
        self.assertTrue(all(row["sql"] == row["raw_sql"] and row["transformations"] == []
                            and "grammar_input_transformations" not in row for row in source))

    def test_anonymous_markers_preserve_lexical_order_and_source_evidence(self):
        sql = "WITH c AS(SELECT ? x) SELECT ?,(SELECT ?)"
        row = {"id": "a", "source_kind": "synthetic", "sql": sql}
        actual = cli.authored_subquery_input(row)
        self.assertEqual(actual["sql"], "WITH c AS(SELECT $1 x) SELECT $2,(SELECT $3)")
        self.assertEqual(actual["grammar_original_sql"], sql)
        self.assertEqual(row["sql"], sql)
        self.assertEqual(len(actual["grammar_input_transformations"]), 1)

    def test_literals_and_json_operators_are_not_rewritten_as_bind_slots(self):
        sql = "SELECT '?' AS t, '{}'::jsonb ? 'x', (SELECT ?)"
        actual = cli.authored_subquery_input({"source_kind": "synthetic", "sql": sql})
        self.assertEqual(actual["sql"], "SELECT '?' AS t, '{}'::jsonb ? 'x', (SELECT $1)")
        unchanged = {"source_kind": "synthetic", "sql": "SELECT (SELECT $2),$1"}
        self.assertIs(cli.authored_subquery_input(unchanged), unchanged)
        with self.assertRaisesRegex(AssertionError, "only authored"):
            cli.authored_subquery_input({"source_kind": "engine-regression", "sql": sql})

    def test_exact_new_population_has_twelve_adaptations_and_untouched_originals(self):
        authored = cli.read_cases(cli.ROOT / "fixtures/subqueries/synthetic.json")
        changed = [r for r in authored if "grammar_input_transformations" in r]
        self.assertEqual(len(authored), 150)
        self.assertEqual(len(changed), 12)
        for factor in ("scalar", "exists", "in"):
            original = cli.read_cases(cli.ROOT / "fixtures/subqueries" / (factor + "_concrete.jsonl"))
            self.assertEqual(len(original), 50)
            self.assertTrue(all(r["sql"] == r["raw_sql"] and r["transformations"] == [] for r in original))
            self.assertFalse(any("grammar_input_transformations" in r for r in original))


class SyntheticCoverageTests(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        cls.cases, cls.coverage = examples.build()

    def test_exactly_all_pinned_families_are_represented(self):
        expected = cli.inventory()["families"]
        self.assertEqual({case["grammar_family"] for case in self.cases}, expected)
        self.assertEqual(len(expected), 125)

    def test_unique_examples_are_not_comment_or_case_padding(self):
        self.assertEqual(len(self.cases), len({case["id"] for case in self.cases}))
        self.assertEqual(len(self.cases), len({case["sql"] for case in self.cases}))
        for case in self.cases:
            self.assertNotIn("/*", case["sql"])
            self.assertNotIn("--", case["sql"])
            self.assertNotIn("\n", case["sql"])

    def test_finite_spelling_shortfalls_are_explicit(self):
        rows = {row["grammar_family"]: row for row in self.coverage["families"]}
        self.assertEqual(rows["CheckPointStmt"]["examples"], 1)
        self.assertEqual(rows["CheckPointStmt"]["shortfall"], 49)
        self.assertEqual(rows["DiscardStmt"]["examples"], 5)
        self.assertEqual(self.coverage["families_meeting_target"], 123)
        self.assertEqual(sum(row["examples"] for row in rows.values()), len(self.cases))
        self.assertTrue(all(row["examples"] + row["shortfall"] == 50 for row in rows.values()))

    def test_structural_diversity_is_separate_from_example_count(self):
        for family in self.coverage["families"]:
            cases = [case for case in self.cases if case["grammar_family"] == family["grammar_family"]]
            self.assertEqual(len({case["grammar_template"] for case in cases}), family["structural_templates"])
            self.assertLessEqual(family["structural_templates"], family["examples"])
        self.assertLess(self.coverage["structural_templates"], self.coverage["examples"])

    def test_no_static_or_action_validity_claim(self):
        self.assertTrue(all(case["static_validity"] == "not-claimed" and
                            case["upstream_action_status"] == "not-checked" for case in self.cases))
        self.assertTrue(any(case["grammar_family"] == "CreateAssertionStmt" for case in self.cases))

    def test_generator_is_offline_and_byte_reproducible(self):
        for name, value in [("synthetic.json", self.cases), ("synthetic_inventory.json", self.coverage)]:
            self.assertEqual((examples.FIXTURES / name).read_text(),
                             json.dumps(value, indent=2, ensure_ascii=False) + "\n")


class BatchProtocolTests(unittest.TestCase):
    def invoke(self, *, stdout=None, stderr="", returncode=0, extra_case=None):
        case = {"id": "case-1", "sql": ReportTests.SQL, **(extra_case or {})}
        envelope = {"id": case["id"], "result": ReportTests().report()}
        if stdout is None:
            stdout = json.dumps(envelope) + "\n"
        process = SimpleNamespace(stdout=stdout, stderr=stderr, returncode=returncode)
        with patch.object(cli.subprocess, "run", return_value=process):
            return cli.run_batch([case])

    def test_valid_single_jsonl_envelope(self):
        self.assertEqual(len(self.invoke()), 1)

    def test_wrong_exit_code_or_stderr_fails(self):
        for kwargs in [{"returncode": 1}, {"stderr": "unstructured warning"}]:
            with self.subTest(kwargs=kwargs), self.assertRaises(AssertionError):
                self.invoke(**kwargs)

    def test_missing_extra_or_nonjson_output_fails(self):
        for stdout in ["", "{}\n{}\n", "debug output\n", '{"id":"case-1"}\n']:
            with self.subTest(stdout=stdout), self.assertRaises((AssertionError, ValueError)):
                self.invoke(stdout=stdout)

    def test_wrong_id_or_extra_envelope_field_fails(self):
        for envelope in [{"id": "other", "result": ReportTests().report()},
                         {"id": "case-1", "result": ReportTests().report(), "extra": True}]:
            with self.assertRaises(AssertionError):
                self.invoke(stdout=json.dumps(envelope) + "\n")

    def test_outer_family_entry_production_is_checked(self):
        with self.assertRaisesRegex(AssertionError, "entry production"):
            self.invoke(extra_case={"entry_production": 99})

    def test_negative_diagnostic_is_checked(self):
        report = {**cli.COMMON, "status": "grammar-rejected", "evidence": "none", "diagnostic": "wrong"}
        with self.assertRaisesRegex(AssertionError, "diagnostic"):
            self.invoke(stdout=json.dumps({"id": "case-1", "result": report}) + "\n",
                        returncode=1, extra_case={"expected": "grammar-rejected",
                                                 "diagnostic_contains": "RETURNING"})


if __name__ == "__main__":
    unittest.main()
