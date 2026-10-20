"""Offline provenance and pattern-source observations, without SQL execution."""
from collections import Counter
from copy import deepcopy
import json
import unittest

from extract_factor_corpus import (
    ROOT, extract, observe_pattern_matches, render, validate_pattern_matches,
    validate_population,
)
from extract_pagination_corpus import comparison_key


def constant(value="a"):
    return {"A_Const": {"sval": {"sval": value}}}


def expression(operator, left=None, right=None, kind="AEXPR_OP"):
    return {"A_Expr": {"kind": kind, "name": [{"String": {"sval": operator}}],
                       "lexpr": constant() if left is None else left,
                       "rexpr": constant() if right is None else right}}


def query(*expressions):
    return {"SelectStmt": {"targetList": list(expressions)}}


class PatternExtractionTests(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        cls.manifests, cls.records = {}, {}
        for factor in ("ilike", "regex"):
            directory = ROOT / "fixtures" / factor
            cls.manifests[factor] = json.loads((directory / "concrete_sources.json").read_text())
            cls.records[factor] = extract(cls.manifests[factor], factor)

    def test_both_fifty_statement_populations_reproduce_exactly(self):
        for factor in self.records:
            with self.subTest(factor=factor):
                self.assertEqual(render(self.records[factor]),
                                 (ROOT / "fixtures" / factor / "concrete.jsonl").read_text())
                self.assertEqual(len(self.records[factor]), 50)
        self.assertEqual(Counter(row["source"] for row in self.records["ilike"]),
                         {"duckdb": 40, "postgres": 7, "river": 2, "hatchet": 1})
        self.assertEqual(Counter(row["source"] for row in self.records["regex"]), {"postgres": 50})
        self.assertEqual(Counter(row["source_kind"] for row in self.records["ilike"]),
                         {"engine-regression": 47, "application-constant": 3})
        self.assertEqual({factor: sum(len(source["files"]) for source in manifest["sources"].values())
                          for factor, manifest in self.manifests.items()}, {"ilike": 8, "regex": 5})

    def test_exact_operator_counts_include_all_regex_spellings_and_not_ilike(self):
        expected = {"ilike": {"ILIKE": 43, "NOT ILIKE": 7},
                    "regex": {"~": 42, "~*": 6, "!~": 1, "!~*": 1}}
        for factor, records in self.records.items():
            matches = [match for row in records for match in row["observed_syntax"]["pattern_matches"]]
            self.assertEqual(len(matches), 50)
            self.assertEqual(Counter(match["operator"] for match in matches), expected[factor])

    def test_source_types_bindings_and_runtime_results_are_not_invented(self):
        for records in self.records.values():
            for row in records:
                self.assertEqual(row["raw_sql"], row["sql"])
                self.assertEqual(row["transformations"], [])
                self.assertIsNone(row["parameter_types"])
                self.assertEqual(row["application_schema_validity"], "not-claimed")
                for field in ("parameter_values", "expected_value", "expected_result", "collation"):
                    self.assertNotIn(field, row)
                for match in row["observed_syntax"]["pattern_matches"]:
                    self.assertEqual(set(match), {"operator", "left_form", "right_form"})
        self.assertEqual(sum(bool(row["observed_parameter_slots"]) for row in self.records["ilike"]), 3)
        self.assertFalse(any(row["observed_parameter_slots"] for row in self.records["regex"]))

    def test_river_constants_preserve_template_comments_and_original_parameter_slots(self):
        original = {row["symbol"]: row for row in (
            json.loads(line) for line in (ROOT / "fixtures/external_postgresql/river.jsonl").read_text().splitlines()
        )}
        river = [row for row in self.records["ilike"] if row["source"] == "river"]
        self.assertEqual({row["symbol"] for row in river}, {"jobKindList", "queueNameList"})
        for row in river:
            self.assertEqual(row["sql"], original[row["symbol"]]["raw_sql"])
            self.assertEqual(row["observed_parameter_slots"], [1, 2, 3, 4])
            self.assertIn("/* TEMPLATE: schema */", row["sql"])
            self.assertIn("ALL($3)", row["sql"])

    def test_duckdb_selection_is_whole_literal_sql_without_imported_results(self):
        duck = [row for row in self.records["ilike"] if row["source"] == "duckdb"]
        self.assertEqual(Counter(row["source_file"] for row in duck), {
            "test/sql/function/string/test_ilike.test": 24,
            "test/sql/function/string/test_ilike_constant_pattern.test": 16,
        })
        for row in duck:
            self.assertEqual(row["source_dialect"], "duckdb")
            self.assertEqual(row["extraction"], "sqllogic_query")
            self.assertTrue(row["sql"].endswith("\n"))
            self.assertNotIn("----", row["sql"])
            self.assertNotIn("expected_result", row)
            self.assertNotIn(" ESCAPE ", row["sql"].upper())
            self.assertNotIn("chr(0)", row["sql"])

    def test_positive_regex_population_excludes_ltree_and_documented_error_section(self):
        records = self.records["regex"]
        self.assertFalse(any("ltree" in row["source_file"] for row in records))
        literals = [row for row in records if row["source_file"].endswith("/regex.sql")]
        self.assertEqual(len(literals), 27)
        self.assertLess(max(row["line"] for row in literals), 100)
        name = [row for row in records if row["source_file"].endswith("/name.sql")]
        self.assertEqual(len(name), 3)
        self.assertTrue(any(match["operator"] == "!~*" for row in records
                            for match in row["observed_syntax"]["pattern_matches"]))

    def test_no_duplicates_against_whole_grammar_or_within_new_population(self):
        old = {comparison_key(json.loads(line)["sql"]) for line in
               (ROOT / "fixtures/statement_families/concrete.jsonl").read_text().splitlines()}
        new = [comparison_key(row["sql"]) for records in self.records.values() for row in records]
        self.assertEqual(len(set(new)), 100)
        self.assertFalse(old.intersection(new))

    def test_each_regex_spelling_is_observed_as_an_operator_not_a_literal(self):
        for operator in ("~", "~*", "!~", "!~*"):
            with self.subTest(operator=operator):
                self.assertEqual(observe_pattern_matches(query(expression(operator)), "regex"), [
                    {"operator": operator, "left_form": "A_Const", "right_form": "A_Const"},
                ])
        with self.assertRaisesRegex(ValueError, "absent"):
            observe_pattern_matches(query(constant("a !~* b")), "regex")

    def test_ilike_and_not_ilike_are_kept_separate_from_symbolic_operator_aliases(self):
        for raw, observed in (("~~*", "ILIKE"), ("!~~*", "NOT ILIKE")):
            with self.subTest(raw=raw):
                self.assertEqual(observe_pattern_matches(query(expression(raw, kind="AEXPR_ILIKE")), "ilike"), [
                    {"operator": observed, "left_form": "A_Const", "right_form": "A_Const"},
                ])
                with self.assertRaisesRegex(ValueError, "extended operator"):
                    observe_pattern_matches(query(expression(raw)), "ilike")
        with self.assertRaisesRegex(ValueError, "spelling"):
            observe_pattern_matches(query(expression("~~", kind="AEXPR_ILIKE")), "ilike")

    def test_nested_observation_preserves_operand_sides_and_order(self):
        column = {"ColumnRef": {"fields": [{"String": {"sval": "pattern"}}]}}
        inner = expression("~", right=column)
        tree = query(expression("!~*", left=inner), expression("~*", left=column))
        self.assertEqual(observe_pattern_matches(tree, "regex"), [
            {"operator": "!~*", "left_form": "A_Expr", "right_form": "A_Const"},
            {"operator": "~", "left_form": "A_Const", "right_form": "ColumnRef"},
            {"operator": "~*", "left_form": "ColumnRef", "right_form": "A_Const"},
        ])

    def test_unary_complement_missing_operands_and_other_extended_operators_are_rejected(self):
        unary = expression("~")
        unary["A_Expr"].pop("lexpr")
        with self.assertRaisesRegex(ValueError, "two expression operands"):
            observe_pattern_matches(query(unary), "regex")
        for operator in ("@", "->>", "^"):
            with self.subTest(operator=operator), self.assertRaisesRegex(ValueError, "extended operator"):
                observe_pattern_matches(query(expression("~"), expression(operator)), "regex")
        qualified = expression("~")
        qualified["A_Expr"]["name"].insert(0, {"String": {"sval": "pg_catalog"}})
        with self.assertRaisesRegex(ValueError, "extended operator"):
            observe_pattern_matches(query(qualified), "regex")

    def test_escape_and_later_expression_dependencies_cannot_hide_inside_calls(self):
        good = expression("~~*", kind="AEXPR_ILIKE")
        later = [
            {"FuncCall": {"funcname": [{"String": {"sval": name}} for name in ("pg_catalog", "like_escape")]}},
            {"RowExpr": {"args": [constant()]}},
            {"A_ArrayExpr": {"elements": [constant()]}},
            {"A_Indirection": {"arg": constant(), "indirection": []}},
            {"SubLink": {"subLinkType": "ARRAY_SUBLINK"}},
            {"SubLink": {"subLinkType": "ANY_SUBLINK"}},
        ]
        for value in later:
            with self.subTest(value=value), self.assertRaisesRegex(ValueError, "outside"):
                observe_pattern_matches(query(good, {"FuncCall": {"args": [value]}}), "ilike")

    def test_metadata_rejects_invented_types_unknown_spellings_and_nonstring_forms(self):
        valid = {"operator": "~", "left_form": "A_Const", "right_form": "ColumnRef"}
        bad = [[], [{**valid, "left_type": "text"}], [{**valid, "operator": "~="}],
               [{**valid, "operator": ["~"]}], [{**valid, "left_form": True}],
               [{**valid, "right_form": "UnknownNode"}]]
        for value in bad:
            with self.subTest(value=value), self.assertRaises(ValueError):
                validate_pattern_matches(value, "regex")
        with self.assertRaisesRegex(ValueError, "unknown"):
            validate_pattern_matches([valid], "like")

    def test_closed_operator_and_operand_counts_cannot_silently_change(self):
        for factor in ("ilike", "regex"):
            rows = deepcopy(self.records[factor])
            entry = rows[0]["observed_syntax"]["pattern_matches"][0]
            entry["operator"] = "NOT ILIKE" if factor == "ilike" else "!~*"
            with self.subTest(factor=factor), self.assertRaisesRegex(ValueError, "50 nodes"):
                validate_population(rows, factor)
            rows = deepcopy(self.records[factor])
            rows[0]["observed_syntax"]["pattern_matches"][0]["left_form"] = "FuncCall"
            with self.subTest(factor=factor), self.assertRaisesRegex(ValueError, "50 nodes"):
                validate_population(rows, factor)

    def test_pinned_source_hashes_and_complete_slt_boundaries_are_enforced(self):
        manifest = deepcopy(self.manifests["ilike"])
        selection = next(row for row in manifest["selections"] if row["selector"]["kind"] == "sqllogic_query")
        selection["selector"]["end"] -= 1
        with self.assertRaisesRegex(ValueError, "complete"):
            extract(manifest, "ilike")
        manifest = deepcopy(self.manifests["regex"])
        manifest["selections"][0]["sql_sha256"] = "0" * 64
        with self.assertRaisesRegex(ValueError, "SQL hash"):
            extract(manifest, "regex")
        manifest = deepcopy(self.manifests["ilike"])
        manifest["sources"]["duckdb"]["files"][0]["sha256"] = "0" * 64
        with self.assertRaisesRegex(ValueError, "hash"):
            extract(manifest, "ilike")


if __name__ == "__main__":
    unittest.main()
