import unittest
from unittest.mock import patch

import check_scalar_forms_cli as runner
from check_extended_types_cli import database_script
from generate_scalar_form_examples import examples


class ScalarFormRunnerTests(unittest.TestCase):
    def test_independent_factors_have_exact_closed_counts(self):
        for factor in runner.FACTORS:
            synthetic, concrete = runner.load_cases(factor)
            self.assertEqual(synthetic, examples(factor))
            self.assertTrue(all(case["source_kind"] == "synthetic" for case in synthetic))
            self.assertEqual(len(concrete), 50)
            self.assertTrue(all(case["source_url"].startswith("https://") for case in concrete))

    def test_native_oracles_cover_both_forms_and_all_metadata(self):
        cases = examples("functions") + examples("conditional")
        script, expected = database_script(cases, [c["sql"] for c in cases])
        self.assertEqual(len(expected), 200)
        self.assertEqual(script.count("PREPARE exact_type_parameters"), 200)
        self.assertIn("SET LOCAL timezone = 'UTC'", script)
        self.assertIn("EXECUTE exact_type_parameters (", script)
        self.assertTrue(any(c["expected_value"] is None for c in cases))
        self.assertTrue(any(len(c["parameter_values"]) > 1 for c in cases))

    def test_catalog_checks_exact_types_and_strictness(self):
        sql, expected = runner.catalog_script()
        self.assertEqual(len(expected), 92)
        self.assertEqual(sql.count("SELECT unnest(proargtypes::oid[])"), 92)
        self.assertEqual(sql.count("AND (proisstrict OR pronargs=0)"), 92)
        self.assertIn("pronamespace='pg_catalog'::regnamespace", sql)
        self.assertNotIn("CREATE", sql)
        self.assertNotIn("DROP", sql)

    def test_boundary_statuses_do_not_promote_unknown_functions(self):
        with patch.object(runner, "assert_report") as report:
            self.assertEqual(runner.boundaries(), 10)
        statuses = [call.args[1] for call in report.call_args_list]
        self.assertEqual(statuses.count("unsupported"), 2)
        self.assertEqual(statuses.count("invalid"), 8)

    def test_synthetic_cases_do_not_execute_external_queries(self):
        source, _ = runner.load_cases("functions")
        script, _ = database_script(source, [c["sql"] for c in source])
        self.assertNotIn("pg_advisory", script)
        self.assertNotIn("CREATE TABLE", script)
        self.assertEqual(script.count("ROLLBACK;"), 1)


if __name__ == "__main__":
    unittest.main()
