"""Tests for array binding and exact-result-descriptor native evidence."""
import json
import unittest

import check_array_types_cli as checker
from generate_array_type_examples import cases


class ArrayTypeTests(unittest.TestCase):
    def test_fifty_type_bearing_queries_reproduce(self):
        expected = cases()
        self.assertEqual(json.loads((checker.FIXTURES / "synthetic.json").read_text()), expected)
        self.assertEqual(len({case["sql"] for case in expected}), 50)
        self.assertEqual(len({case["declared_element"] for case in expected}), 10)

    def test_array_null_elements_do_not_make_array_object_nullable(self):
        for case in cases():
            self.assertFalse(case["output_columns"][0]["nullable"])
        self.assertEqual(checker.operator_cases()[-1]["expected_value"], "{NULL,1}")
        self.assertIn("'{NULL,", checker.operator_cases()[-1]["sql"])

    def test_json_null_conversion_is_a_runtime_error_not_sql_null(self):
        case = checker.runtime_error_case()
        self.assertIn("""'{"null","1"}'""", case["sql"])
        script, expected = checker.runtime_error_script(case, case["sql"])
        self.assertEqual(len(expected), 2)
        self.assertTrue(all(result == (1, [["22023"]]) for result in expected.values()))
        self.assertIn("RETURN SQLSTATE", script)

    def test_declared_rank_is_not_a_distinct_result_type(self):
        case = cases()[2]
        self.assertIn("integer[][]", case["sql"])
        self.assertEqual(case["output_columns"][0]["type"], "integer[]")
        self.assertEqual(case["postgres_display_type"], "integer[]")

    def test_cast_values_and_modifiers_are_separate_from_unmodified_bindings(self):
        numeric = cases()[10:15]
        self.assertEqual(numeric[0]["expected_value"], "{1.23,NULL,5.68}")
        self.assertEqual(numeric[1]["expected_value"], "{1.234,NULL,5.678}")
        self.assertEqual(numeric[0]["postgres_display_type"], "numeric(6,2)[]")
        self.assertEqual(numeric[1]["postgres_display_type"], "numeric[]")

    def test_parameter_modifier_regressions_include_scalar_and_array(self):
        rows = checker.parameter_modifier_cases()
        self.assertEqual(len(rows), 10)
        for original, casted in zip(rows[::2], rows[1::2]):
            self.assertEqual(original["parameter_types"], casted["parameter_types"])
            self.assertNotEqual(original["output_columns"][0]["type"], casted["output_columns"][0]["type"])
            self.assertNotEqual(original["expected_value"], casted["expected_value"])
            self.assertNotEqual(original["postgres_display_type"], casted["postgres_display_type"])

    def test_descriptor_uses_prepared_select_not_return_table_wrapper(self):
        case = checker.parameter_modifier_cases()[0]
        script, expected = checker.describe_script([case], [case["sql"]])
        self.assertIn("PREPARE array_description (numeric(6,2)) AS SELECT $1 AS v;", script)
        self.assertIn("EXECUTE array_description('1.234')", script)
        self.assertNotIn("RETURNS TABLE", script)
        self.assertEqual(script.count("\\gdesc"), 2)
        self.assertEqual(expected, ["v|numeric", "v|numeric"])

    def test_descriptor_keeps_anonymous_parameter_source_order(self):
        case = cases()[2]
        script, _ = checker.describe_script([case], [case["sql"]])
        self.assertIn("CAST($1 AS integer[][])", script)
        self.assertIn("EXECUTE array_description('{1,NULL,3}')", script)

    def test_descriptor_counts_names_and_exact_modifiers(self):
        rows = cases() + checker.parameter_modifier_cases() + checker.operator_cases()
        script, expected = checker.describe_script(rows, [case["sql"] for case in rows])
        self.assertEqual(len(expected), 126)
        self.assertEqual(script.count("\\gdesc"), 126)
        self.assertIn("v|character varying(8)[]", expected)
        self.assertIn("v|timestamp(2) without time zone", expected)

    def test_missing_canonical_description_is_an_error(self):
        with self.assertRaises(AssertionError):
            checker.describe_script(cases(), [])

    def test_missing_value_or_oid_is_an_error(self):
        expected = {"capture": (2, [["{1,NULL}", "integer[]"]])}
        for actual in ({}, {"capture": (1, [["{1,NULL}"]])},
                       {"capture": (2, [["{1,NULL}", "bigint[]"]])}):
            with self.assertRaises(AssertionError):
                checker.validate_results(actual, expected)

    def test_json_and_bytea_lexemes_keep_escaped_data(self):
        json_case, bytea_case = cases()[40], cases()[45]
        self.assertEqual(json_case["expected_value"], r'{"{\"a\": 1}",NULL,"null"}')
        self.assertEqual(bytea_case["expected_value"], r'{"\\x00",NULL,"\\x6162"}')

    def test_value_capture_preserves_typed_parameters_separately(self):
        case = cases()[11]
        script, expected = checker.database_script([case], [case["sql"]])
        self.assertIn("PREPARE exact_type_parameters (numeric[])", script)
        self.assertIn("SELECT $1 AS v", script)
        self.assertIn("EXECUTE exact_type_parameters", script)
        self.assertEqual(len(expected), 2)
        self.assertTrue(all(row == (2, [["{1.234,NULL,5.678}", "numeric[]"]]) for row in expected.values()))


if __name__ == "__main__":
    unittest.main()
