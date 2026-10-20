"""Regression checks for JOIN fixture and native-observation boundaries."""
from collections import Counter
import copy
import json
import unittest
from unittest.mock import patch

import check_join_contract_cli as checker
from generate_join_contract_examples import cases, schema


class JoinContractTests(unittest.TestCase):
    def setUp(self):
        self.cases = cases()

    def test_checked_in_schema_and_synthetic_population_reproduce(self):
        self.assertEqual(json.loads((checker.FIXTURES / "synthetic.json").read_text()), self.cases)
        self.assertEqual(json.loads((checker.FIXTURES / "schema.json").read_text()), schema())
        self.assertEqual(Counter(c["join_kind"] for c in self.cases),
                         {kind: 10 for kind in ("cross", "inner", "left", "right", "full")})
        self.assertEqual(len({c["sql"] for c in self.cases}), 50)

    def test_sources_keep_duplicate_matches_and_both_unmatched_sides(self):
        expected_counts = {"cross": 9, "inner": 2, "left": 4, "right": 3, "full": 5}
        for case in self.cases:
            if case["shape"] == "identity":
                self.assertEqual(len(case["expected_rows"]), expected_counts[case["join_kind"]])
        full = next(c for c in self.cases if c["id"] == "join-full-identity")
        self.assertEqual(checker.bag(full["expected_rows"]),
                         checker.bag([[1, 11], [1, 12], [2, None], [3, None], [None, 13]]))

    def test_null_extension_is_not_refined_away_by_where(self):
        for case in self.cases:
            if case["shape"] == "post-join-filter":
                right_nullable = case["join_kind"] in ("left", "full")
                self.assertEqual(case["output_columns"][1]["nullable"], right_nullable)
                self.assertTrue(all(row[1] is not None for row in case["expected_rows"]))

    def test_projection_on_where_parameters_remain_distinct(self):
        for case in self.cases:
            if case["shape"] == "anonymous-source-order":
                self.assertEqual(checker.parameters(case["sql"], "postgres"),
                                 [("anonymous", 1), ("anonymous", 2), ("anonymous", 3)])
                self.assertEqual(case["parameter_values"], [10, 7, 18])
                self.assertIn("? + COALESCE", case["sql"])
                self.assertIn("COALESCE(u.age, 0) >= ?", case["sql"])

    def test_metadata_is_used_for_contract_checks(self):
        case = self.cases[20]
        with patch.object(checker, "assert_report") as report:
            checker.validity(case)
        args = report.call_args.args
        self.assertEqual(args[1:3], ("valid", "contract"))
        self.assertIn(str(checker.FIXTURES / "schema.json"), args[0])
        self.assertEqual(args[3], (("user_id", "int32", False), ("order_id", "int32", True)))

    def test_all_native_cases_are_real_execute_in_two_states(self):
        script, expected = checker.postgres_script(self.cases, [c["sql"] for c in self.cases])
        self.assertEqual(len(expected), 200)
        self.assertEqual(script.count("PREPARE locking_parameters"), 200)
        self.assertEqual(script.count("DEALLOCATE locking_parameters"), 200)
        self.assertEqual(script.count("ROLLBACK TO SAVEPOINT join_case"), 200)
        self.assertIn("RETURN QUERY EXECUTE", script)
        self.assertTrue(script.rstrip().endswith("ROLLBACK;"))

    def test_sqlite_keeps_numbered_identity_without_tuple_binding(self):
        self.assertEqual(checker.sqlite_bindings("SELECT ?2, ?1, ?2", [7, 9]), {"1": 7, "2": 9})
        self.assertEqual(checker.sqlite_bindings("SELECT ?, ?", [7, 9]), [7, 9])

    def test_missing_canonical_cases_fail_before_database(self):
        with self.assertRaises(AssertionError):
            checker.postgres_script(self.cases, [])
        with self.assertRaises(AssertionError):
            checker.sqlite_observations(self.cases, [])

    def test_native_bag_check_keeps_duplicate_and_null_information(self):
        expected = {"one": (2, [["1", None], ["1", None], [None, "2"]])}
        self.assertEqual(checker.validate_native(copy.deepcopy(expected), expected), 1)
        for actual in ({}, {"one": (2, [["1", None], [None, "2"]])},
                       {"one": (1, [["1", None], ["1", None], [None, "2"]])},
                       {"one": (2, [["1", ""], ["1", None], [None, "2"]])}):
            with self.assertRaises(AssertionError):
                checker.validate_native(actual, expected)

    def test_sqlite_independently_checks_all_200_authored_rows(self):
        observed = checker.sqlite_observations(self.cases, [c["sqlite_sql"] for c in self.cases])
        self.assertEqual(observed, 200)

    def test_sqlite_rejects_wrong_row_or_output_label(self):
        case = copy.deepcopy(self.cases[40])
        case["expected_rows"] = case["expected_rows"][:-1]
        with self.assertRaises(AssertionError):
            checker.sqlite_observations([case], [case["sqlite_sql"]])
        case = copy.deepcopy(self.cases[40])
        case["output_columns"][0]["name"] = "incorrect_label"
        with self.assertRaises(AssertionError):
            checker.sqlite_observations([case], [case["sqlite_sql"]])


if __name__ == "__main__":
    unittest.main()
