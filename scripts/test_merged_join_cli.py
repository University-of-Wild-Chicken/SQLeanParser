"""Mutation and native-oracle boundaries for USING/NATURAL JOINs."""
from collections import Counter
import copy
import json
import unittest
from unittest.mock import patch

import check_merged_join_cli as checker
from generate_merged_join_examples import all_cases, schema


class MergedJoinTests(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        cls.using = all_cases("using_contract")
        cls.natural = all_cases("natural_contract")
        cls.cases = cls.using + cls.natural

    def test_both_generated_populations_and_schema_reproduce(self):
        for factor, cases in (("using_contract", self.using), ("natural_contract", self.natural)):
            path = checker.ROOT / "fixtures" / factor / "synthetic.json"
            self.assertEqual(json.loads(path.read_text()), cases)
            self.assertEqual(len({case["sql"] for case in cases}), 50)
        self.assertEqual(json.loads(checker.CATALOG.read_text()), schema())

    def test_four_populations_retain_outer_rows_and_null_key_nonmatches(self):
        full = next(case for case in self.natural if case["shape"] == "star" and case["join_kind"] == "full")
        self.assertEqual([len(full["expected_rows_by_state"][state]) for state in checker.STATES], [0, 4, 4, 7])
        rows = full["expected_rows_by_state"]["both"]
        # NULL id/tag 'n' exists on each side, and must yield two unmatched rows.
        self.assertEqual(sum(row[0] is None and row[1] == "n" for row in rows), 2)

    def test_empty_key_natural_full_has_a_cartesian_and_outer_boundary(self):
        case = self.natural[-1]
        self.assertEqual(case["shape"], "no-common-columns")
        self.assertEqual([len(case["expected_rows_by_state"][s]) for s in checker.STATES], [0, 4, 2, 8])

    def test_merged_and_qualified_keys_keep_different_exact_types(self):
        case = self.using[2]
        self.assertEqual([c["type"] for c in case["output_columns"]], ["int64", "int32", "int64"])
        with patch.object(checker, "assert_report") as report:
            checker.validity(case)
        self.assertEqual([c[1] for c in report.call_args.args[3]], ["bigint", "int32", "bigint"])

    def test_sqlite_star_order_is_not_replaced_with_postgres_order(self):
        case = self.using[0]
        self.assertEqual([c["name"] for c in case["output_columns"]],
                         ["id", "left_value", "tag", "right_value", "tag"])
        self.assertEqual(case["sqlite_output_names"],
                         ["left_value", "id", "tag", "right_value", "tag"])

    def test_sqlite_qualified_star_merged_values_are_separately_authored(self):
        case = next(c for c in self.natural if c["shape"] == "qualified-stars" and c["join_kind"] == "right")
        postgres = case["expected_rows_by_state"]["right_only"]
        sqlite = case["sqlite_expected_rows_by_state"]["right_only"]
        self.assertIn([None, None, None, 1, 101, "x"], postgres)
        self.assertIn([None, 1, "x", 1, 101, "x"], sqlite)
        self.assertNotEqual(checker.bag(postgres), checker.bag(sqlite))

    def test_full_join_merged_nonnull_key_does_not_inherit_qualified_null_extension(self):
        case = self.using[-1]
        self.assertEqual([c["nullable"] for c in case["output_columns"]], [False, True, True])
        self.assertTrue(all(row[0] is not None for rows in case["expected_rows_by_state"].values() for row in rows))

    def test_duplicate_projected_labels_are_kept_positionally(self):
        case = self.using[1]
        labels = [c["name"] for c in case["output_columns"]]
        self.assertEqual(Counter(labels)["id"], 2)
        sql = checker.prepare_capture(case, case["sql"])
        self.assertIn("c0 INTEGER, c1 INTEGER, c2 TEXT, c3 BIGINT, c4 INTEGER, c5 TEXT", sql[1])
        self.assertIn("RETURN QUERY EXECUTE", sql[1])

    def test_values_stay_out_of_prepared_sql_and_keep_separate_types(self):
        case = self.using[5]
        capture = checker.prepare_capture(case, case["sql"])
        self.assertIn("PREPARE merged_parameters (INTEGER, INTEGER)", capture[0])
        self.assertIn("$1 AS marker", capture[0])
        self.assertIn("id >= $2", capture[0])
        self.assertIn("EXECUTE merged_parameters (7, 1)", capture[1])

    def test_native_captures_all_four_populations_without_function_type_leakage(self):
        script, expected = checker.postgres_script(self.cases, [c["sql"] for c in self.cases])
        self.assertEqual(len(expected), 800)
        self.assertEqual(script.count("SAVEPOINT merged_case;"), 2400)
        self.assertEqual(script.count("PREPARE merged_parameters"), 800)
        self.assertEqual(script.count("DEALLOCATE merged_parameters"), 800)
        self.assertTrue(script.rstrip().endswith("ROLLBACK;"))

    def test_missing_canonical_input_fails_before_database(self):
        with self.assertRaises(AssertionError):
            checker.postgres_script(self.cases, [])
        with self.assertRaises(AssertionError):
            checker.sqlite_observations(self.cases, [])

    def test_sqlite_executes_all_800_independent_row_and_label_expectations(self):
        canonical = [c["sqlite_sql"].replace("SELECT tag,", 'SELECT "tag",')
                     for c in self.cases]
        self.assertEqual(checker.sqlite_observations(self.cases, canonical), 800)

    def test_unaliased_sqlite_merged_expression_label_retains_quoting(self):
        case = self.using[-1]
        self.assertEqual(case["sqlite_output_names"], ["tag", "left_id", "right_id"])
        self.assertEqual(case["sqlite_canonical_output_names"], ['"tag"', "left_id", "right_id"])
        with self.assertRaises(AssertionError):
            checker.sqlite_observations([case], [case["sqlite_sql"]])

    def test_wrong_dialect_oracles_cannot_silently_pass(self):
        case = copy.deepcopy(self.using[0])
        case["sqlite_output_names"] = [c["name"] for c in case["output_columns"]]
        with self.assertRaises(AssertionError):
            checker.sqlite_observations([case], [case["sqlite_sql"]])
        case = copy.deepcopy(self.natural[25])
        case["sqlite_expected_rows_by_state"] = case["expected_rows_by_state"]
        with self.assertRaises(AssertionError):
            checker.sqlite_observations([case], [case["sqlite_sql"]])

    def test_native_typmod_probes_keep_original_qualified_type_checks(self):
        script, expected = checker.type_script()
        self.assertEqual(len(expected), 24)
        self.assertEqual(script.count("original_left"), 8)
        self.assertEqual(script.count("original_right"), 8)
        self.assertIn("character varying(4)", expected)
        self.assertIn("character varying", expected)


if __name__ == "__main__":
    unittest.main()
