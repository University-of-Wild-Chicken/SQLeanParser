"""Offline regressions for locking corpus identity and bounded native checks."""
from copy import deepcopy
import io
import json
from pathlib import Path
import subprocess
import tempfile
import unittest
from unittest.mock import MagicMock, patch

import check_locking_cli as cli
from extract_factor_corpus import extract
from generate_locking_examples import POLICIES, STRENGTHS, cases as generated_cases


class LockingCliTests(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        cls.synthetic, cls.concrete = cli.load_cases()

    def fixtures(self, synthetic, concrete=None):
        directory = tempfile.TemporaryDirectory()
        self.addCleanup(directory.cleanup)
        root = Path(directory.name)
        (root / "synthetic.json").write_text(json.dumps(synthetic))
        (root / "concrete.jsonl").write_text("".join(
            json.dumps(row) + "\n" for row in
            (self.concrete if concrete is None else concrete)))
        return root

    def test_generated_and_whole_source_fixtures_reproduce(self):
        self.assertEqual(self.synthetic, generated_cases())
        manifest = json.loads((cli.FIXTURES / "concrete_sources.json").read_text())
        self.assertEqual(self.concrete, extract(manifest, "locking"))
        self.assertTrue(all(row["sql"] == row["raw_sql"] for row in self.concrete))
        self.assertTrue(all(row["parameter_types"] is None for row in self.concrete))
        self.assertTrue(all("parameter_values" not in row for row in self.concrete))

    def test_every_strength_and_wait_policy_has_four_distinct_shapes(self):
        expected_shapes = {
            "filtered-base-table", "alias-and-text-parameter",
            "numbered-offset-first", "anonymous-leading-lock-offset-first",
        }
        for index, (strength, policy) in enumerate(
                (strength, policy) for strength in STRENGTHS for policy in POLICIES):
            batch = self.synthetic[index * 4:index * 4 + 4]
            self.assertEqual({case["shape"] for case in batch}, expected_shapes)
            for case in batch:
                self.assertIn("FOR " + strength, case["sql"])
                if policy:
                    self.assertIn(policy, case["sql"])
                else:
                    self.assertNotIn("NOWAIT", case["sql"])
                    self.assertNotIn("SKIP LOCKED", case["sql"])
        self.assertEqual(self.synthetic[48]["sql"].count(" FOR "), 2)
        self.assertEqual(self.synthetic[49]["sql"].count(" FOR "), 2)

    def test_missing_or_duplicate_case_identity_fails_closed(self):
        for population in ("synthetic", "concrete"):
            for mutation in ("missing", "duplicate-id", "duplicate-sql"):
                synthetic, concrete = deepcopy(self.synthetic), deepcopy(self.concrete)
                rows = synthetic if population == "synthetic" else concrete
                if mutation == "missing":
                    rows.pop()
                elif mutation == "duplicate-id":
                    rows[1]["id"] = rows[0]["id"]
                else:
                    rows[1]["sql"] = rows[0]["sql"]
                root = self.fixtures(synthetic, concrete)
                with self.subTest(population=population, mutation=mutation):
                    with patch.object(cli, "FIXTURES", root), self.assertRaises(AssertionError):
                        cli.load_cases()

    def test_catalog_bindings_parameter_order_and_row_arity_are_checked(self):
        changes = (
            (0, "catalogFile", "fixtures/other.json"),
            (2, "sqlite_sql", "SELECT ?1, ?2, ?3;"),
            (2, "parameter_values", [2, 1]),
            (2, "parameter_types", "int,int"),
            (0, "parameter_types", "int"),
            (0, "expected_rows", [[1, 2]]),
        )
        for index, field, value in changes:
            rows = deepcopy(self.synthetic)
            rows[index][field] = value
            with self.subTest(field=field), patch.object(cli, "FIXTURES", self.fixtures(rows)):
                with self.assertRaises(AssertionError):
                    cli.load_cases()

    def test_reordered_numbered_and_anonymous_slots_keep_occurrence_identity(self):
        for case in self.synthetic:
            original = cli.parameters(case["sql"], "postgres")
            self.assertEqual(original, cli.parameters(case["sqlite_sql"], "sqlite"))
            if case["shape"] == "numbered-offset-first":
                self.assertEqual(original, [("numbered", 3), ("numbered", 2), ("numbered", 1)])
                self.assertEqual(case["parameter_values"], [2, 1, 18])
            if case["shape"] == "anonymous-leading-lock-offset-first":
                self.assertEqual(original, [("anonymous", n) for n in range(1, 5)])
                self.assertEqual(case["parameter_values"], [5, 2, 1, 2])
                self.assertLess(case["sql"].index("OFFSET ?"), case["sql"].index("LIMIT ?"))

    def test_validity_uses_authored_catalog_declared_types_and_exact_output(self):
        case = self.synthetic[1]
        sentinel = object()
        with patch.object(cli, "assert_report", return_value=sentinel) as report:
            self.assertIs(cli.validity(case), sentinel)
        report.assert_called_once_with(
            ["--assurance", "contract", "--schema", str(cli.ROOT / "fixtures/schema.json"),
             "--param-types", "text", case["sql"]],
            "valid", "contract", (("user_id", "int32", False), ("user_name", "text", False)))
        with patch.object(cli, "assert_report") as report:
            cli.validity(self.synthetic[0])
        self.assertNotIn("--param-types", report.call_args.args[0])

    def test_sqlite_rejection_has_two_explicit_parse_boundaries(self):
        reasons = []
        for case in self.synthetic:
            message = ("SQLite OFFSET requires LIMIT first"
                       if case["shape"] == "numbered-offset-first"
                       else "SQLite does not support row-locking clauses")
            report = {"diagnostic": {"code": "input.parse", "message": message}, "evidence": "none"}
            with patch.object(cli, "dialect_render", return_value=report) as render:
                self.assertIs(cli.sqlite_rejection(case), report)
                render.assert_called_once_with("sqlite", case["sqlite_sql"], "invalid")
            reasons.append(message)
        self.assertEqual(reasons.count("SQLite OFFSET requires LIMIT first"), 12)
        self.assertEqual(reasons.count("SQLite does not support row-locking clauses"), 38)

    def test_sqlite_wrong_diagnostic_or_success_payload_cannot_pass(self):
        base = {"diagnostic": {"code": "input.parse",
                               "message": "SQLite does not support row-locking clauses"},
                "evidence": "none"}
        bad_reports = []
        for key, value in (("sql", "SELECT 1"), ("parameterMap", []), ("theorems", []),
                           ("evidence", "checked-roundtrip")):
            bad_reports.append({**base, key: value})
        bad_reports.extend([
            {**base, "diagnostic": {"code": "other", "message": base["diagnostic"]["message"]}},
            {**base, "diagnostic": {"code": "input.parse", "message": "unexpected token"}},
        ])
        for report in bad_reports:
            with self.subTest(report=report), patch.object(cli, "dialect_render", return_value=report):
                with self.assertRaises(AssertionError):
                    cli.sqlite_rejection(self.synthetic[0])

    def test_prepare_keeps_parameter_values_separate_and_ignores_quoted_markers(self):
        source = """SELECT '?' AS "?", id FROM users OFFSET ? LIMIT ? FOR UPDATE;"""
        capture = cli.prepare_capture(
            source, "int,int", [2, 1], [{"name": "id", "type": "int32"}])
        self.assertEqual(capture[0], 'PREPARE locking_parameters (INTEGER, INTEGER) AS '
                         """SELECT '?' AS "?", id FROM users OFFSET $1 LIMIT $2 FOR UPDATE;""")
        self.assertIn("EXECUTE locking_parameters (2, 1)", capture[1])
        self.assertNotIn("OFFSET 2", capture[0])
        self.assertNotIn("LIMIT 1", capture[0])

    def test_prepare_quotes_nested_values_and_preserves_native_output_types(self):
        value = "x'; DROP TABLE users; --"
        capture = cli.prepare_capture(
            "SELECT id, name, age >= 18 AS adult FROM users WHERE name = $1 FOR SHARE;",
            "text", [value], [{"name": "id", "type": "int32"},
                             {"name": "na\"me", "type": "text"},
                             {"name": "adult", "type": "bool"}])
        self.assertNotIn(value, capture[0])
        self.assertIn("x''''''''; DROP TABLE users; --", capture[1])
        self.assertIn('RETURNS TABLE ("id" INTEGER, "na""me" TEXT, "adult" BOOLEAN)', capture[1])
        self.assertIn("RETURN QUERY EXECUTE", capture[1])
        self.assertIn("VOLATILE", capture[1])
        nullable = cli.prepare_capture("SELECT id FROM users FOR UPDATE;",
                                       "int?,text?,bool?", [None, "2", True],
                                       [{"name": "id", "type": "int32"}])
        self.assertIn("(INTEGER, TEXT, BOOLEAN)", nullable[0])
        self.assertIn("EXECUTE locking_parameters (NULL,", nullable[1])
        self.assertIn("TRUE)", nullable[1])

    def test_native_inventory_is_two_forms_by_two_states_without_lock_leakage(self):
        script, expected = cli.postgres_script(self.synthetic, [row["sql"] for row in self.synthetic])
        self.assertEqual(len(expected), 200)
        for command in ("PREPARE locking_parameters", "DEALLOCATE locking_parameters;",
                        "SAVEPOINT locking_case;", "ROLLBACK TO SAVEPOINT locking_case;",
                        "RELEASE SAVEPOINT locking_case;"):
            # SAVEPOINT occurs within ROLLBACK/RELEASE too; line equality isolates it.
            count = sum(line == command for line in script.splitlines()) if command.startswith(
                ("SAVEPOINT", "ROLLBACK", "RELEASE", "DEALLOCATE")) else script.count(command)
            self.assertEqual(count, 200)
        self.assertEqual(script.count("INSERT INTO users VALUES"), 1)
        self.assertIn("SET LOCAL statement_timeout = '5s';", script)
        self.assertTrue(script.endswith("ROLLBACK;"))
        for index, case in enumerate(self.synthetic, 1):
            for form in ("source", "postgres"):
                arity = len(case["output_columns"])
                self.assertEqual(expected[cli.marker("locking", index, False, form)], (arity, []))
                self.assertEqual(expected[cli.marker("locking", index, True, form)],
                                 (arity, [[cli.copy_cell(cell) for cell in row]
                                          for row in case["expected_rows"]]))
        self.assertEqual(expected[cli.marker("locking", 49, True, "source")],
                         (2, [["1", "t"], ["2", "f"], ["3", "t"]]))

    def test_missing_canonical_case_or_contention_mode_cannot_be_silently_skipped(self):
        with self.assertRaisesRegex(AssertionError, "missing rendered locking case"):
            cli.postgres_script(self.synthetic, [row["sql"] for row in self.synthetic[:-1]])
        with self.assertRaisesRegex(AssertionError, "missing rendered contention query"):
            cli.contention_observations(["psql"], {"nowait": cli.CONTENTION_QUERIES["nowait"]})

    def test_contention_uses_real_execute_sqlstate_and_distinct_timeout_error(self):
        script, key = cli.contention_script("private_schema", cli.CONTENTION_QUERIES["nowait"],
                                            error=True)
        self.assertIn("SET LOCAL statement_timeout = '2s';", script)
        self.assertIn("SET LOCAL lock_timeout = 0;", script)
        self.assertIn('SET LOCAL search_path = "private_schema", pg_catalog;', script)
        self.assertIn("PREPARE locking_parameters AS " + cli.CONTENTION_QUERIES["nowait"], script)
        self.assertIn("EXECUTE locking_parameters", script)
        self.assertIn("EXCEPTION WHEN OTHERS THEN RETURN SQLSTATE", script)
        self.assertIn("unexpected-success", script)
        self.assertIn("\\echo " + key, script)
        self.assertTrue(script.endswith("ROLLBACK;"))

    def test_unestablished_owner_lock_stops_observations_and_cleans_up(self):
        owner = MagicMock()
        owner.command.return_value = []
        with patch.object(cli, "PersistentPsql", return_value=owner):
            with patch.object(cli, "run") as run:
                with self.assertRaisesRegex(AssertionError, "owner did not establish"):
                    cli.contention_observations(["psql"], cli.CONTENTION_QUERIES)
        self.assertEqual(run.call_count, 2)  # Only schema setup and cleanup, no contender.
        self.assertIn("DROP SCHEMA", run.call_args.kwargs["input"])
        owner.close.assert_called_once_with()
        self.assertIn("WHERE id = 1 FOR UPDATE", owner.command.call_args.args[0])


class PersistentPsqlTests(unittest.TestCase):
    def owner(self):
        owner = cli.PersistentPsql.__new__(cli.PersistentPsql)
        owner.process = MagicMock()
        owner.process.stdin = io.BytesIO()
        owner.process.stdout.fileno.return_value = 42
        owner.buffer, owner.sequence = b"", 0
        selector = MagicMock()
        selector.__enter__.return_value = selector
        selector.select.return_value = [object()]
        return owner, selector

    def test_fragmented_markers_and_retained_buffer_do_not_lose_rows(self):
        owner, selector = self.owner()
        chunks = [b"\n1\r\n__SQLEAN_", b"LOCK_SYNC_1__\n",
                  b"two\n__SQLEAN_LOCK_SYNC_2__\nleftover"]
        with patch.object(cli.selectors, "DefaultSelector", return_value=selector):
            with patch.object(cli.os, "read", side_effect=chunks) as read:
                self.assertEqual(owner.command("SELECT 1;"), ["1"])
                self.assertEqual(owner.command("SELECT 'two';"), ["two"])
                self.assertEqual(read.call_count, 3)
        self.assertEqual(owner.buffer, b"leftover")
        self.assertEqual(owner.process.stdin.getvalue(),
                         b"SELECT 1;\n\\echo __SQLEAN_LOCK_SYNC_1__\n"
                         b"SELECT 'two';\n\\echo __SQLEAN_LOCK_SYNC_2__\n")

    def test_buffered_complete_response_needs_no_second_read(self):
        owner, selector = self.owner()
        with patch.object(cli.selectors, "DefaultSelector", return_value=selector):
            with patch.object(cli.os, "read", return_value=(
                    b"1\n__SQLEAN_LOCK_SYNC_1__\n2\n__SQLEAN_LOCK_SYNC_2__\n")) as read:
                self.assertEqual(owner.command("first"), ["1"])
                self.assertEqual(owner.command("second"), ["2"])
        self.assertEqual(read.call_count, 1)
        self.assertEqual(owner.buffer, b"")

    def test_timeout_and_eof_fail_closed_without_claiming_lock_established(self):
        owner, selector = self.owner()
        selector.select.return_value = []
        with patch.object(cli.selectors, "DefaultSelector", return_value=selector):
            with self.assertRaisesRegex(AssertionError, "handshake timed out"):
                owner.command("SELECT 1;")
        owner, selector = self.owner()
        owner.process.poll.return_value = 7
        with patch.object(cli.selectors, "DefaultSelector", return_value=selector):
            with patch.object(cli.os, "read", return_value=b""):
                with self.assertRaisesRegex(AssertionError, "exited before handshake"):
                    owner.command("SELECT 1;")

    def test_close_rolls_back_then_bounds_termination_escalation(self):
        owner, _ = self.owner()
        owner.process.stdin = MagicMock()
        owner.process.stdin.closed = False
        owner.process.wait.side_effect = [
            subprocess.TimeoutExpired("psql", 5), subprocess.TimeoutExpired("psql", 5), 0]
        owner.close()
        owner.process.stdin.write.assert_called_once_with(b"ROLLBACK;\n\\quit\n")
        owner.process.stdin.close.assert_called_once_with()
        owner.process.terminate.assert_called_once_with()
        owner.process.kill.assert_called_once_with()
        self.assertEqual(owner.process.wait.call_count, 3)
        owner.process.stdout.close.assert_called_once_with()


if __name__ == "__main__":
    unittest.main()
