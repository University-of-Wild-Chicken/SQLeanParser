"""Offline checks for pagination fixture identity and native-binding helpers."""
from copy import deepcopy
import json
from pathlib import Path
import sqlite3
import tempfile
import unittest
from unittest.mock import patch

import check_pagination_cli as cli
from extract_pagination_corpus import extract
from generate_pagination_examples import cases as generated_cases


class PaginationCliTests(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        cls.synthetic, cls.concrete = cli.load_cases()

    def test_loaded_sources_match_generators_and_pinned_extraction(self):
        self.assertEqual(self.synthetic, generated_cases())
        manifest = json.loads((cli.FIXTURES / "concrete_sources.json").read_text())
        self.assertEqual(self.concrete, extract(manifest))
        river = next(case for case in self.concrete if case["source"] == "river")
        self.assertTrue(river["sql"].startswith("-- name: QueueList :many\n"))
        self.assertEqual(river["sql"], river["raw_sql"])

    def test_load_cases_rejects_dropped_or_duplicate_statement_identity(self):
        for kind in ("missing", "duplicate-id", "duplicate-sql"):
            with self.subTest(kind=kind), tempfile.TemporaryDirectory() as directory:
                root = Path(directory)
                synthetic = deepcopy(self.synthetic)
                if kind == "missing":
                    synthetic.pop()
                elif kind == "duplicate-id":
                    synthetic[1]["id"] = synthetic[0]["id"]
                else:
                    synthetic[1]["sql"] = synthetic[0]["sql"]
                (root / "synthetic.json").write_text(json.dumps(synthetic))
                (root / "concrete.jsonl").write_text(
                    "".join(json.dumps(case) + "\n" for case in self.concrete))
                with patch.object(cli, "FIXTURES", root), self.assertRaises(AssertionError):
                    cli.load_cases()

    def test_prepare_keeps_query_and_separate_bindings(self):
        source = """SELECT '?' AS "?", id FROM page_rows LIMIT ? OFFSET ?;"""
        capture = cli.prepare_capture(source, "int,int", [2, 1])
        self.assertEqual(capture[0],
                         'PREPARE pagination_parameters (INTEGER, INTEGER) AS '
                         """SELECT '?' AS "?", id FROM page_rows LIMIT $1 OFFSET $2;""")
        self.assertIn("EXECUTE pagination_parameters (2, 1)", capture[1])
        self.assertNotIn("LIMIT 2", capture[0])
        self.assertNotIn("OFFSET 1", capture[0])

    def test_prepare_values_are_quoted_inside_execute_not_select(self):
        value = "x'; DROP TABLE page_rows; --"
        source = "SELECT id FROM page_rows LIMIT CAST($1 AS INTEGER);"
        capture = cli.prepare_capture(source, "text", [value])
        self.assertEqual(capture[0],
                         "PREPARE pagination_parameters (TEXT) AS " + source)
        self.assertNotIn(value, capture[0])
        # The argument, dynamic EXECUTE statement, and CREATE FUNCTION body
        # each quote this apostrophe: three levels require eight quote bytes.
        self.assertIn("x''''''''; DROP TABLE page_rows; --", capture[1])
        self.assertIn("RETURN QUERY EXECUTE", capture[1])

    def test_source_comment_is_sent_through_stdin_without_becoming_an_option(self):
        source = next(case["sql"] for case in self.concrete if case["source"] == "river")
        completed, report = object(), object()
        with patch.object(cli.subprocess, "run", return_value=completed) as run:
            with patch.object(cli, "validate_report", return_value=report) as validate:
                self.assertIs(cli.invoke("postgres", source), report)
        self.assertEqual(run.call_args.args[0], [str(cli.EXE), "--render-assurance", "postgres"])
        self.assertEqual(run.call_args.kwargs["input"], source)
        self.assertEqual(run.call_args.kwargs["timeout"], 30)
        validate.assert_called_once_with(completed, "postgres", source)

    def test_prepare_nullable_types_boolean_and_null_values(self):
        capture = cli.prepare_capture(
            "SELECT id FROM page_rows LIMIT CAST($2 AS INTEGER);",
            "int?,text?,bool?", [None, "2", True])
        self.assertTrue(capture[0].startswith(
            "PREPARE pagination_parameters (INTEGER, TEXT, BOOLEAN) AS "))
        self.assertIn("EXECUTE pagination_parameters (NULL, ", capture[1])
        self.assertIn("TRUE)", capture[1])
        self.assertNotIn("None", capture[1])
        plain = cli.prepare_capture("SELECT id FROM page_rows LIMIT 2;", "", [])
        self.assertTrue(plain[0].startswith("PREPARE pagination_parameters AS "))
        self.assertNotIn("EXECUTE pagination_parameters ()", plain[1])

    def test_runtime_capture_returns_sqlstate_and_detects_unexpected_success(self):
        capture = cli.prepare_capture(
            "SELECT id FROM page_rows LIMIT $1;", "int", [-1], error=True)
        self.assertIn("EXECUTE pagination_parameters (-1)", capture[1])
        self.assertIn("unexpected-success", capture[1])
        self.assertIn("EXCEPTION WHEN OTHERS THEN RETURN SQLSTATE", capture[1])
        self.assertNotIn("RETURN QUERY", capture[1])

    def test_postgres_observation_inventory_includes_both_forms_and_states(self):
        rendered = [{"postgres": case["sql"]} for case in self.synthetic]
        errors = [sql for sql, _, _, _ in cli.RUNTIME_CASES]
        script, expected = cli.postgres_script(self.synthetic, rendered, errors)
        self.assertEqual(len(expected), 212)
        self.assertEqual(script.count("PREPARE pagination_parameters"), 212)
        self.assertEqual(script.count("DEALLOCATE pagination_parameters;"), 212)
        self.assertEqual(script.count("INSERT INTO page_rows VALUES"), 1)
        self.assertIn("SET LOCAL statement_timeout = '5s';", script)
        self.assertTrue(script.endswith("ROLLBACK;"))
        for index, case in enumerate(self.synthetic, 1):
            for form in ("source", "postgres"):
                self.assertEqual(expected[cli.marker("pagination", index, False, form)], (1, []))
                self.assertEqual(expected[cli.marker("pagination", index, True, form)],
                                 (1, [[str(cell) for cell in row]
                                      for row in case["expected_rows"]]))
        for index, (_, _, _, state) in enumerate(cli.RUNTIME_CASES, 1):
            for form in ("source", "postgres"):
                self.assertEqual(expected[cli.marker("pagination_error", index, True, form)],
                                 (1, [[state]]))

    def test_missing_rendered_observations_cannot_be_truncated_by_zip(self):
        rendered = [{"postgres": case["sql"]} for case in self.synthetic]
        errors = [sql for sql, _, _, _ in cli.RUNTIME_CASES]
        with self.assertRaisesRegex(AssertionError, "missing rendered pagination case"):
            cli.postgres_script(self.synthetic, rendered[:-1], errors)
        with self.assertRaisesRegex(AssertionError, "missing rendered runtime boundary"):
            cli.postgres_script(self.synthetic, rendered, errors[:-1])
        with self.assertRaisesRegex(AssertionError, "missing rendered SQLite case"):
            cli.sqlite_check(self.synthetic, rendered[:-1])

    def test_sqlite_fixture_adaptation_preserves_all_parameter_occurrences(self):
        for case in self.synthetic:
            with self.subTest(case=case["id"]):
                original = cli.parameters(case["sql"], "postgres")
                sqlite = cli.parameters(case["sqlite_sql"], "sqlite")
                self.assertEqual(sqlite, original)
                self.assertEqual({slot for _, slot in sqlite},
                                 set(range(1, len(case["parameter_values"]) + 1)))
                self.assertNotIn("::", case["sqlite_sql"])
                self.assertNotIn("$", case["sqlite_sql"])

    def test_sqlite_numbered_bindings_follow_slot_not_occurrence_order(self):
        with sqlite3.connect(":memory:") as db:
            for sql in ("SELECT ?2, ?1, ?2", "SELECT $2, $1, $2"):
                bindings = cli.sqlite_bindings(sql, [7, 11])
                self.assertEqual(db.execute(sql, bindings).fetchall(), [(11, 7, 11)])
            sql = 'SELECT \'?9\' AS "?literal", ?2, ?1, ?2'
            bindings = cli.sqlite_bindings(sql, ["O'Brien", None])
            self.assertEqual(db.execute(sql, bindings).fetchall(),
                             [("?9", None, "O'Brien", None)])

    def test_sqlite_anonymous_bindings_ignore_quoted_markers(self):
        sql = "SELECT '?', ?, '?' || ?, ?"
        bindings = cli.sqlite_bindings(sql, [3, "value", None])
        with sqlite3.connect(":memory:") as db:
            self.assertEqual(db.execute(sql, bindings).fetchall(),
                             [("?", 3, "?value", None)])
        self.assertEqual(cli.sqlite_bindings("SELECT '$1', '?' /* ?2 */", []), ())

    def test_sqlite_binding_arity_and_mixed_styles_fail_closed(self):
        for sql, values in (
            ("SELECT 1", [1]),
            ("SELECT ?, ?", [1]),
            ("SELECT ?2, ?1", [1]),
            ("SELECT ?1", [1, 2]),
            ("SELECT ?2", [1, 2]),
            ("SELECT ?, ?1", [1]),
        ):
            with self.subTest(sql=sql), self.assertRaises(AssertionError):
                cli.sqlite_bindings(sql, values)


if __name__ == "__main__":
    unittest.main()
