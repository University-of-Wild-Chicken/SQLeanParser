"""Offline regressions for type-oracle bindings and observation inventory."""
from copy import deepcopy
import json
from pathlib import Path
import tempfile
import unittest
from unittest.mock import patch

import check_extended_types_cli as cli
from extract_extended_type_corpus import extract
from generate_extended_type_examples import cases


class ExtendedTypeCliTests(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        cls.synthetic, cls.concrete = cli.load_cases()

    def test_inputs_match_generator_and_pinned_original_statements(self):
        self.assertEqual(self.synthetic, cases())
        manifest = json.loads((cli.FIXTURES / "concrete_sources.json").read_text())
        self.assertEqual(self.concrete, extract(manifest))

    def test_missing_or_duplicate_fixture_identity_fails(self):
        for kind in ("missing", "duplicate-id", "duplicate-sql"):
            with self.subTest(kind=kind), tempfile.TemporaryDirectory() as directory:
                root = Path(directory)
                values = deepcopy(self.synthetic)
                if kind == "missing":
                    values.pop()
                else:
                    field = "id" if kind == "duplicate-id" else "sql"
                    values[1][field] = values[0][field]
                (root / "synthetic.json").write_text(json.dumps(values))
                (root / "concrete.jsonl").write_text(
                    "".join(json.dumps(row) + "\n" for row in self.concrete))
                with patch.object(cli, "FIXTURES", root), self.assertRaises(AssertionError):
                    cli.load_cases()

    def test_capture_keeps_markers_and_binds_values_separately(self):
        source = "SELECT CAST($2 AS JSONB) AS v WHERE $1 = $1;"
        result = cli.capture(source, "integer,jsonb?", [7, '{"v":"O\'Brien"}'])
        self.assertEqual(
            result[0],
            "PREPARE exact_type_parameters (integer,jsonb) AS "
            "SELECT v::text, pg_typeof(v)::text FROM "
            "(SELECT CAST($2 AS JSONB) AS v WHERE $1 = $1) AS observed;")
        self.assertNotIn("O'Brien", result[0])
        self.assertIn("EXECUTE exact_type_parameters (7,", result[1])
        self.assertIn("O''''''''Brien", result[1])
        self.assertIn("RETURNS TABLE (value TEXT, type TEXT)", result[1])

    def test_anonymous_conversion_ignores_quoted_question_marks(self):
        result = cli.capture("SELECT CAST(? AS TEXT) AS v WHERE '?' = '?';",
                             "text?", [None])
        self.assertIn("CAST($1 AS TEXT)", result[0])
        self.assertIn("WHERE '?' = '?'", result[0])
        self.assertIn("EXECUTE exact_type_parameters (NULL)", result[1])
        plain = cli.capture("SELECT UUID '00000000-0000-0000-0000-000000000000' AS v;", "", [])
        self.assertTrue(plain[0].startswith("PREPARE exact_type_parameters AS "))
        self.assertNotIn("EXECUTE exact_type_parameters ()", plain[1])

    def test_native_inventory_has_source_and_rendered_value_and_type(self):
        rendered = [case["sql"] for case in self.synthetic]
        script, expected = cli.database_script(self.synthetic, rendered)
        self.assertEqual(len(expected), 100)
        self.assertEqual(script.count("PREPARE exact_type_parameters"), 100)
        self.assertEqual(script.count("DEALLOCATE exact_type_parameters;"), 100)
        self.assertIn("SET LOCAL statement_timeout = '5s';", script)
        self.assertIn("SET LOCAL timezone = 'UTC';", script)
        self.assertIn("SET LOCAL intervalstyle = 'postgres';", script)
        self.assertIn("SET LOCAL standard_conforming_strings = on;", script)
        self.assertTrue(script.endswith("ROLLBACK;"))
        for index, case in enumerate(self.synthetic, 1):
            for form in ("source", "postgres"):
                key = cli.marker("exact_types", index, True, form)
                self.assertEqual(expected[key],
                                 (2, [[case["expected_value"], case["postgres_type"]]]))

    def test_zip_cannot_hide_missing_rendered_observations(self):
        with self.assertRaisesRegex(AssertionError, "missing rendered type case"):
            cli.database_script(self.synthetic, [case["sql"] for case in self.synthetic][:-1])

    def test_contract_assertion_keeps_exact_type_and_nullability(self):
        case = next(case for case in self.synthetic if case["parameter_types"] and case["nullable"])
        with patch.object(cli, "assert_report") as assertion:
            cli.assurance(case)
        assertion.assert_called_once_with(
            ["--assurance", "contract", "--param-types", case["parameter_types"], case["sql"]],
            "valid", "contract", (("v", case["contract_type"], case["nullable"]),))

    def test_json_comparison_boundary_inventory_remains_closed(self):
        with patch.object(cli, "assert_report") as assertion:
            self.assertEqual(cli.boundaries(), 21)
        calls = assertion.call_args_list
        self.assertEqual(len(calls), 21)
        self.assertEqual(sum(call.args[1] == "invalid" for call in calls), 6)
        self.assertEqual(sum(call.args[1] == "rejected" for call in calls), 12)
        self.assertEqual(sum(call.args[1] == "checked" for call in calls), 3)
        self.assertTrue(any("USING(v)" in call.args[0][-1] for call in calls))


if __name__ == "__main__":
    unittest.main()
