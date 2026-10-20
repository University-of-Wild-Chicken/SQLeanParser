"""Independent row-model and harness regressions for derived SELECT sources."""
import copy
import json
import unittest

import check_derived_contract_cli as checker
from generate_derived_contract_examples import all_cases, schema


class DerivedContractTests(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        cls.cases = all_cases()
        cls.portable = [case for case in cls.cases if case["sqlite_supported"]]

    def test_generated_population_and_catalog_reproduce(self):
        self.assertEqual(json.loads((checker.FIXTURES / "synthetic.json").read_text()), self.cases)
        self.assertEqual(json.loads((checker.FIXTURES / "schema.json").read_text()), schema())
        self.assertEqual(len({case["sql"] for case in self.cases}), 50)

    def test_alias_lists_are_explicitly_postgres_only(self):
        rejected = [case for case in self.cases if not case["sqlite_supported"]]
        self.assertEqual(len(rejected), 10)
        self.assertEqual({case["shape"] for case in rejected}, {"prefix-alias", "full-alias"})

    def test_prefix_renaming_keeps_remaining_names_and_types(self):
        case = self.cases[2]
        self.assertEqual([c["name"] for c in case["output_columns"]], ["key_id", "score", "name"])
        self.assertEqual([c["nullable"] for c in case["output_columns"]], [False, True, False])
        self.assertEqual(case["expected_rows"], self.cases[0]["expected_rows"])

    def test_nested_projection_uses_inner_coalescing(self):
        self.assertIn([2, 1], self.cases[1]["expected_rows"])
        self.assertEqual([c["nullable"] for c in self.cases[1]["output_columns"]], [False, False])

    def test_inner_predicate_reaches_single_row_boundary(self):
        self.assertEqual(len(self.cases[0]["expected_rows"]), 4)
        self.assertEqual(self.cases[40]["expected_rows"], [[4, 40, "Di"]])

    def test_full_join_retains_both_unmatched_sides_and_duplicates(self):
        case = self.cases[6]
        self.assertEqual(case["expected_rows_by_state"]["items_only"],
                         [[1, 1, None], [2, 2, None], [3, 3, None], [4, 4, None]])
        self.assertEqual(case["expected_rows_by_state"]["labels_only"],
                         [[1, None, "A"], [1, None, "B"], [3, None, "C"], [5, None, "E"]])
        self.assertEqual(len(case["expected_rows_by_state"]["both"]), 6)
        self.assertEqual([c["nullable"] for c in case["output_columns"]], [False, True, True])

    def test_nullable_metadata_survives_outer_filter(self):
        case = self.cases[8]
        self.assertTrue(case["output_columns"][0]["nullable"])
        self.assertEqual(case["expected_rows"], [[10], [40]])
        self.assertNotIn([None], case["expected_rows"])

    def test_anonymous_values_remain_separate_and_globally_ordered(self):
        case = self.cases[4]
        capture = checker.prepare_capture(case, case["sql"])
        self.assertIn("SELECT $1 AS marker", capture[0])
        self.assertIn("AND id >= $2", capture[0])
        self.assertIn(">= $3", capture[0])
        self.assertIn("LIMIT $4 OFFSET $5", capture[0])
        self.assertIn("EXECUTE merged_parameters (7, 1, 0, 2, 0)", capture[1])

    def test_native_capture_count_and_query_local_return_types(self):
        script, expected = checker.postgres_script(self.cases, [case["sql"] for case in self.cases])
        self.assertEqual(len(expected), 400)
        self.assertEqual(script.count("SAVEPOINT derived_case;"), 1200)
        self.assertEqual(script.count("DEALLOCATE merged_parameters;"), 400)
        self.assertTrue(script.rstrip().endswith("ROLLBACK;"))

    def test_missing_canonical_input_is_rejected(self):
        with self.assertRaises(AssertionError):
            checker.postgres_script(self.cases, [])
        with self.assertRaises(AssertionError):
            checker.sqlite_observations(self.portable, [])

    def test_sqlite_disallows_alias_cases_before_execution(self):
        with self.assertRaises(AssertionError):
            checker.sqlite_observations([self.cases[2]], [self.cases[2]["sql"]])

    def test_sqlite_runs_320_independent_source_observations(self):
        self.assertEqual(checker.sqlite_observations(
            self.portable, [case["sqlite_sql"] for case in self.portable]), 320)

    def test_wrong_inner_null_model_is_detected(self):
        case = copy.deepcopy(self.cases[1])
        case["expected_rows_by_state"]["both"] = [[1, 11], [2, None], [3, 11], [4, 41]]
        with self.assertRaises(AssertionError):
            checker.sqlite_observations([case], [case["sqlite_sql"]])

    def test_missing_duplicate_native_row_is_detected(self):
        expected = {"capture": (1, [["1"], ["1"]])}
        with self.assertRaises(AssertionError):
            checker.validate_native({"capture": (1, [["1"]])}, expected)


if __name__ == "__main__":
    unittest.main()
