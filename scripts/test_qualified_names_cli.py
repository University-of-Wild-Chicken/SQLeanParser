"""Qualified relation identity, positional results, and bounded native evidence."""
from contextlib import nullcontext, redirect_stdout
from copy import deepcopy
import io
import json
from pathlib import Path
import subprocess
import tempfile
import unittest
from unittest.mock import MagicMock, patch

import check_assurance_cli as assurance
import check_qualified_names_cli as checker
from check_postgresql_cli import NULL, marker
from generate_qualified_name_examples import cases, schema


def transcript(case, *, populated_rows=None):
    """Produce COPY observations without consulting the native script's oracle."""
    def field(value):
        value = checker.copy_cell(value)
        return NULL if value is None else '"' + value.replace('"', '""') + '"'
    lines = []
    for populated in (False, True):
        for form in ("source", "postgres"):
            lines += [marker("qualified_names", 1, populated, form),
                      ",".join('"c' + str(i) + '"' for i in range(len(case["output_columns"])))]
            rows = (case["expected_rows"] if populated_rows is None else populated_rows) if populated else []
            lines += [",".join(map(field, row)) for row in rows]
    return "\n".join(lines) + "\n"


class QualifiedNamesCliTests(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        cls.synthetic, cls.sources = checker.load_cases()

    @classmethod
    def case(cls, shape="duplicate-labels"):
        return deepcopy(next(row for row in cls.synthetic if row["shape"] == shape))

    def fixtures(self, rows, sources=None, catalog=None):
        temporary = tempfile.TemporaryDirectory()
        self.addCleanup(temporary.cleanup)
        directory = Path(temporary.name)
        (directory / "synthetic.json").write_text(json.dumps(rows))
        (directory / "concrete.jsonl").write_text("".join(
            json.dumps(row) + "\n" for row in (self.sources if sources is None else sources)))
        (directory / "schema.json").write_text(json.dumps(schema() if catalog is None else catalog))
        return directory

    def test_frozen_populations_and_authored_catalog_reproduce(self):
        self.assertEqual(self.synthetic, cases())
        self.assertEqual(json.loads((checker.FIXTURES / "schema.json").read_text()), schema())
        self.assertEqual((len(self.synthetic), len(self.sources)), (50, 50))
        for row in self.sources:
            self.assertEqual(row["sql"], row["raw_sql"])
            self.assertEqual(row["transformations"], [])
            self.assertIs(row["observed_syntax"]["source_free"], False)
            self.assertIsNone(row["parameter_types"])
            self.assertNotIn("parameter_values", row)
        visible = {(row["schema"], row["name"]) for row in schema()["tables"]
                   if row["exposeUnqualified"]}
        self.assertEqual(visible, {("qa", "users"), ("qa", "orders"),
                                   ("qa", "users.dot"), ("qa", "select")})
        self.assertEqual(len(schema()["tables"]), 7)

    def test_loader_rejects_missing_duplicate_or_malformed_fixture_evidence(self):
        for mutation in ("missing", "source_missing", "duplicate_id", "duplicate_sql",
                         "source_duplicate_id", "source_duplicate_sql", "catalog",
                         "extra_value", "missing_value", "sparse_slot", "extra_type",
                         "missing_type", "sqlite_slot_order", "sqlite_slot_reuse",
                         "row_arity", "nullable_int", "nullable_null"):
            rows, sources = deepcopy(self.synthetic), deepcopy(self.sources)
            row = next(row for row in rows if row["shape"] == "reordered-parameter")
            if mutation == "missing":
                rows.pop()
            elif mutation == "source_missing":
                sources.pop()
            elif "duplicate" in mutation:
                population = sources if mutation.startswith("source_") else rows
                field = mutation.rsplit("_", 1)[1]
                population[1][field] = population[0][field]
            elif mutation == "catalog":
                row["catalogFile"] = "fixtures/other/schema.json"
            elif mutation == "extra_value":
                row["parameter_values"].append(99)
            elif mutation == "missing_value":
                row["parameter_values"].pop()
            elif mutation == "sparse_slot":
                row["sql"] = row["sql"].replace("$2", "$3")
                row["sqlite_sql"] = row["sqlite_sql"].replace("?2", "?3")
            elif mutation == "extra_type":
                row["parameter_types"] += ",int"
            elif mutation == "missing_type":
                row["parameter_types"] = "int"
            elif mutation == "sqlite_slot_order":
                row["sqlite_sql"] = row["sqlite_sql"].replace("?2", "?0").replace("?1", "?2").replace("?0", "?1")
            elif mutation == "sqlite_slot_reuse":
                row["sqlite_sql"] = row["sqlite_sql"].replace("?2", "?1")
            elif mutation == "row_arity":
                row["expected_rows"][0].append("unexpected")
            else:
                row["output_columns"][0]["nullable"] = 0 if mutation == "nullable_int" else None
            with self.subTest(mutation=mutation), patch.object(checker, "FIXTURES",
                    self.fixtures(rows, sources)), self.assertRaises(AssertionError):
                checker.load_cases()

    def test_parameter_occurrences_retain_reuse_reordering_and_anonymous_identity(self):
        expectations = {
            "reordered-parameter": ([("numbered", 2), ("numbered", 1)], [2, 10]),
            "repeated-parameter": ([("numbered", 1), ("numbered", 1)], [1]),
            "anonymous-order": ([("anonymous", 1), ("anonymous", 2), ("anonymous", 3)], [10, 7, 1]),
            "pagination": ([("numbered", 2), ("numbered", 1)], [1, 1]),
            "nullable-parameter": ([("numbered", 1)], [None]),
        }
        for shape, (uses, values) in expectations.items():
            row = self.case(shape)
            with self.subTest(shape=shape):
                self.assertEqual(checker.parameters(row["sql"], "postgres"), uses)
                self.assertEqual(checker.parameters(row["sqlite_sql"], "sqlite"), uses)
                self.assertEqual(row["parameter_values"], values)
        for row in self.synthetic:
            self.assertEqual(checker.parameters(row["sql"], "postgres"),
                             checker.parameters(row["sqlite_sql"], "sqlite"))
        capture = checker.prepare_capture(self.case("anonymous-order"), self.case("anonymous-order")["sql"])
        self.assertIn("SELECT $1 + qa.users.id", capture[0])
        self.assertIn("qa.orders.amount >= $2", capture[0])
        self.assertIn("qa.users.id >= $3", capture[0])
        self.assertIn("EXECUTE merged_parameters (10, 7, 1)", capture[1])

    def test_validity_uses_exact_catalog_bindings_and_duplicate_ordered_labels(self):
        row = self.case()
        sentinel = object()
        with patch.object(checker, "assert_report", return_value=sentinel) as report:
            self.assertIs(checker.validity(row), sentinel)
        report.assert_called_once_with(
            ["--assurance", "contract", "--schema", str(checker.FIXTURES / "schema.json"), row["sql"]],
            "valid", "contract", (("x", "int32", False), ("x", "text", False)))
        row = self.case("nullable-parameter")
        with patch.object(checker, "assert_report") as report:
            checker.validity(row)
        self.assertEqual(report.call_args.args[0][-3:], ["--param-types", "text?", row["sql"]])
        self.assertEqual(report.call_args.args[3], (("label", "text", True),))

    def test_validity_rejects_wrong_evidence_or_positional_metadata(self):
        row = self.case()
        good = {"status": "valid", "assurance": "declarative", "profile": assurance.PROFILES["contract"],
                "evidence": "declarative-derivation", "catalogUnchanged": True, "typePrecision": "exact",
                "outputColumns": row["output_columns"]}
        with patch.object(assurance, "invoke", return_value=subprocess.CompletedProcess(
                [], 0, json.dumps(good), "")):
            self.assertEqual(checker.validity(row), good)
        for mutation in ("status", "evidence", "profile", "catalog", "precision", "missing_columns",
                         "reordered_columns", "renamed_column", "wrong_type", "nullable_integer",
                         "nullable_true", "exit"):
            report, exit_code = deepcopy(good), 0
            if mutation == "status":
                report["status"] = "checked"
            elif mutation in {"evidence", "profile"}:
                report[mutation] = "wrong"
            elif mutation == "catalog":
                report["catalogUnchanged"] = False
            elif mutation == "precision":
                report["typePrecision"] = "family"
            elif mutation == "missing_columns":
                report["outputColumns"].pop()
            elif mutation == "reordered_columns":
                report["outputColumns"].reverse()
            elif mutation == "renamed_column":
                report["outputColumns"][0]["name"] = "id"
            elif mutation == "wrong_type":
                report["outputColumns"][0]["type"] = "bigint"
            elif mutation.startswith("nullable_"):
                report["outputColumns"][0]["nullable"] = 0 if mutation.endswith("integer") else True
            else:
                exit_code = 3
            with self.subTest(mutation=mutation), patch.object(assurance, "invoke",
                    return_value=subprocess.CompletedProcess([], exit_code, json.dumps(report), "")), \
                    self.assertRaises(AssertionError):
                checker.validity(row)

    def test_schema_and_column_components_are_quoted_individually(self):
        self.assertEqual(checker.qualified_name(("schema.dot", "table.dot")), '"schema.dot"."table.dot"')
        self.assertEqual(checker.qualified_name(('s"x', "select")), '"s""x"."select"')
        setup = "\n".join(checker.setup())
        self.assertIn('CREATE TABLE "schema.dot"."table.dot" ("id" INTEGER NOT NULL, '
                      '"column.dot" TEXT NOT NULL);', setup)
        self.assertIn('CREATE TABLE "qa"."select" ("id" INTEGER NOT NULL, "from" TEXT NOT NULL);', setup)
        self.assertEqual(setup.count("CREATE TABLE "), 7)
        self.assertEqual(setup.count("CREATE SCHEMA "), 4)
        self.assertIn("SET LOCAL search_path = qa, qb, public;", setup)
        self.assertIn("SET LOCAL statement_timeout = '5s';", setup)
        self.assertIn("SET LOCAL standard_conforming_strings = on;", setup)

    def test_capture_keeps_duplicate_labels_positional_and_parameter_values_separate(self):
        row = self.case()
        capture = checker.prepare_capture(row, row["sql"])
        self.assertIn("RETURNS TABLE (c0 INTEGER, c1 TEXT)", capture[1])
        self.assertNotIn('RETURNS TABLE ("x"', capture[1])
        self.assertIn("AS x, qa.users.name AS x", capture[0])
        row = self.case("nullable-parameter")
        row["parameter_values"] = ["x'; SELECT 'never interpolate'; --"]
        capture = checker.prepare_capture(row, row["sql"])
        self.assertIn("PREPARE merged_parameters (TEXT)", capture[0])
        self.assertIn("COALESCE(qb.users.title, $1)", capture[0])
        self.assertNotIn(row["parameter_values"][0], capture[0])
        self.assertIn("x''''''''; SELECT ''''''''never interpolate''''''''; --", capture[1])
        nullable = self.case("nullable-parameter")
        self.assertIn("EXECUTE merged_parameters (NULL)",
                      checker.prepare_capture(nullable, nullable["sql"])[1])

    def test_native_population_is_two_states_by_two_forms_with_per_case_lock_rollback(self):
        script, wanted = checker.postgres_script(self.synthetic, [row["sql"] for row in self.synthetic])
        self.assertEqual(len(wanted), 200)
        lines = script.splitlines()
        for command in ("SAVEPOINT qualified_case;", "DEALLOCATE merged_parameters;",
                        "ROLLBACK TO SAVEPOINT qualified_case;", "RELEASE SAVEPOINT qualified_case;"):
            self.assertEqual(lines.count(command), 200)
        self.assertEqual(script.count("PREPARE merged_parameters"), 200)
        self.assertEqual(script.count("INSERT INTO "), 7)
        self.assertTrue(script.endswith("ROLLBACK;"))
        for index, row in enumerate(self.synthetic, 1):
            arity = len(row["output_columns"])
            for form in ("source", "postgres"):
                self.assertEqual(wanted[marker("qualified_names", index, False, form)], (arity, []))
                self.assertEqual(wanted[marker("qualified_names", index, True, form)],
                                 (arity, [[checker.copy_cell(cell) for cell in values]
                                          for values in row["expected_rows"]]))
        for helper in (checker.postgres_script, checker.describe_script):
            with self.subTest(helper=helper.__name__), self.assertRaises(AssertionError):
                helper(self.synthetic, [row["sql"] for row in self.synthetic[:-1]])

    def test_descriptors_preserve_duplicate_label_positions_types_and_literal_dots(self):
        script, wanted = checker.describe_script(self.synthetic, [row["sql"] for row in self.synthetic])
        self.assertEqual(len(wanted), 166)
        self.assertEqual(script.count("\\gdesc"), 100)
        self.assertEqual(script.count("DEALLOCATE qualified_description;"), 100)
        _, duplicate = checker.describe_script([self.case()], [self.case()["sql"]])
        self.assertEqual(duplicate, ["x|integer", "x|text"] * 2)
        self.assertIn("column.dot|text", wanted)
        self.assertIn("Case ID|integer", wanted)
        self.assertIn("PREPARE qualified_description (text)", script)
        self.assertIn("EXECUTE qualified_description(NULL)", script)
        self.assertIn("EXECUTE qualified_description(2, 10)", script)
        self.assertTrue(script.endswith("ROLLBACK;"))

    def test_boundaries_distinguish_namespace_ambiguity_planning_and_whole_row_fallback(self):
        with patch.object(checker, "assert_report") as report:
            self.assertEqual(checker.boundaries(), 25)
        self.assertEqual([sum(call.args[1] == status for call in report.call_args_list)
                          for status in ("invalid", "unsupported")], [12, 13])
        script, states = checker.boundary_script()
        self.assertEqual(states, ["42P09", "42P09", "42P01", "42P01", "42P01", "42712",
                                  "42712", "42712", "0A000", "42P01", "42P01", "42703",
                                  *(["00000"] * 9), "42702", "00000", "42703", "42702"])
        self.assertIn("EXECUTE ''EXPLAIN EXECUTE qualified_boundary''", script)
        self.assertIn("IF EXISTS (SELECT 1 FROM pg_prepared_statements", script)
        self.assertIn("DEALLOCATE qualified_boundary; END IF; RETURN SQLSTATE;", script)
        self.assertEqual(script.count("SELECT pg_temp.qualified_analysis("), 25)
        for expression in ("users", "ctid", "xmin", "xmax", "cmin", "cmax", "tableoid"):
            self.assertIn((f"SELECT {expression} FROM qa.users", "unsupported", "00000"),
                          checker.BOUNDARIES)
        self.assertIn(("SELECT ctid FROM qa.users, (SELECT 1 AS ctid) d", "unsupported", "42702"),
                      checker.BOUNDARIES)
        self.assertIn(("SELECT ctid FROM qa.users CROSS JOIN (SELECT 1 AS ctid) d", "unsupported", "00000"),
                      checker.BOUNDARIES)
        self.assertTrue(script.endswith("ROLLBACK;"))

    def test_visibility_is_observed_for_every_exact_relation_identity(self):
        script, wanted = checker.visibility_script()
        self.assertEqual(wanted, ["t", "f", "t", "t", "f", "t", "f"])
        self.assertEqual(script.count("SELECT pg_table_is_visible("), 7)
        self.assertIn("""SELECT pg_table_is_visible('"qa"."users.dot"'::regclass);""", script)
        self.assertIn("""SELECT pg_table_is_visible('"schema.dot"."table.dot"'::regclass);""", script)
        self.assertIn("SET LOCAL search_path = qa, qb, public;", script)
        self.assertTrue(script.endswith("ROLLBACK;"))

    def test_sqlite_requires_exact_exit_status_code_and_absence_of_success_evidence(self):
        parse_reasons = {
            "column-aliases": "reserved identifier key",
            "partial-aliases": "reserved identifier key",
            "substring": "1:32: expected )",
            "locking": "SQLite does not support row-locking clauses",
            "locking-first-inner": "SQLite does not support row-locking clauses",
            "locking-first-left": "SQLite does not support row-locking clauses",
            "locking-first-reversed": "SQLite does not support row-locking clauses",
        }
        self.assertEqual(len(parse_reasons), 7)
        self.assertEqual(sum(row["shape"] not in parse_reasons for row in self.synthetic), 43)
        for row in self.synthetic:
            shape, sql = row["shape"], row["sqlite_sql"]
            reason = parse_reasons.get(shape)
            exit_code, status, code = ((1, "invalid", "input.parse") if reason else
                                      (3, "unsupported", "coverage.sqlite.schema-qualification"))
            good = {"status": status, "diagnostic": {"code": code,
                    "message": (reason if shape == "substring" else "1:23: " + reason) if reason else
                               "schema-qualified relations are unsupported"},
                    "evidence": "none"}
            with patch.object(checker.subprocess, "run", return_value=subprocess.CompletedProcess(
                    [], exit_code, json.dumps(good), "")) as run:
                checker.sqlite_rejection(sql)
            self.assertEqual(run.call_args.kwargs["input"], sql)
            self.assertEqual(run.call_args.kwargs["timeout"], 30)
            mutations = ["exit", "status", "code", "evidence", "sql", "parameterMap", "theorems"]
            if reason:
                mutations += ["message", "missing_message", "wrong_parse_boundary"]
            if shape == "substring":
                mutations += ["wrong_parse_position"]
            for mutation in mutations:
                report, result_code = deepcopy(good), exit_code
                if mutation == "exit":
                    result_code = 0
                elif mutation == "status":
                    report["status"] = "inconclusive"
                elif mutation == "code":
                    report["diagnostic"]["code"] = "coverage.other"
                elif mutation == "evidence":
                    report["evidence"] = "checked-roundtrip"
                elif mutation == "message":
                    report["diagnostic"]["message"] = "unexpected input"
                elif mutation == "missing_message":
                    del report["diagnostic"]["message"]
                elif mutation == "wrong_parse_position":
                    report["diagnostic"]["message"] = "1:31: expected )"
                elif mutation == "wrong_parse_boundary":
                    report["diagnostic"]["message"] = (
                        "reserved identifier key" if reason != "reserved identifier key" else
                        "SQLite does not support row-locking clauses")
                else:
                    report[mutation] = [] if mutation != "sql" else sql
                with self.subTest(shape=shape, mutation=mutation), patch.object(checker.subprocess, "run",
                        return_value=subprocess.CompletedProcess([], result_code, json.dumps(report), "")), \
                        self.assertRaises((AssertionError, KeyError)):
                    checker.sqlite_rejection(sql)

    def exercise_main(self, *, row=None, values=None, descriptors=None, states=None, visibility=None):
        row = self.case() if row is None else row
        source = [{"sql": "SELECT external_field FROM never_execute_source.private_table;"}]
        values = transcript(row) if values is None else values
        if descriptors is None:
            display = {"int32": "integer", "text": "text", "bool": "boolean"}
            descriptors = "".join(c["name"] + "|" + display[c["type"]] + "\n"
                                  for c in row["output_columns"]) * 2
        states = "\n".join(checker.boundary_script()[1]) + "\n" if states is None else states
        visibility = "t\nf\nt\nt\nf\nt\nf\n" if visibility is None else visibility
        results = [subprocess.CompletedProcess([], 0, text, "") for text in
                   (values, descriptors, states, visibility, "16.15\n")]
        with patch.object(checker, "load_cases", return_value=([row], source)), \
                patch.object(checker, "validity") as validity, \
                patch.object(checker, "replay", side_effect=lambda mode, sql: {
                    "sql": sql + (" /* canonical */" if mode == "postgres" else "")}) as replay, \
                patch.object(checker, "sqlite_rejection") as sqlite, \
                patch.object(checker, "boundaries", return_value=25), \
                patch.object(checker, "first_lock_observations", return_value=8) as locks, \
                patch.object(checker, "connection", return_value=nullcontext(["psql"])), \
                patch.object(checker, "run", side_effect=results) as run, \
                patch("sys.argv", ["check_qualified_names_cli.py", "--dsn", "unused"]), \
                redirect_stdout(io.StringIO()):
            checker.main()
            sqlite.assert_called_once_with(row["sqlite_sql"])
            return run.call_args_list, validity.call_args_list, replay.call_args_list, locks.call_args_list

    def test_main_never_executes_or_invents_catalog_certificates_for_downloaded_sql(self):
        calls, validity, replays, locks = self.exercise_main()
        self.assertEqual((len(calls), len(validity), len(replays), len(locks)), (5, 1, 4, 1))
        self.assertEqual(sum("never_execute_source" in call.args[1] for call in replays), 2)
        self.assertNotIn("never_execute_source", validity[0].args[0]["sql"])
        for call in calls[:4]:
            self.assertIn("ON_ERROR_STOP=1", call.args[0])
            self.assertNotIn("never_execute_source", call.kwargs["input"])
        for call in calls[:2]:
            self.assertEqual(call.kwargs["timeout"], 120)
            self.assertIn("/* canonical */", call.kwargs["input"])

    def test_main_checks_sqlite_numbered_input_without_rewriting_postgresql_execution(self):
        row = self.case("reordered-parameter")
        self.assertNotEqual(row["sql"], row["sqlite_sql"])
        calls, validity, replays, _ = self.exercise_main(row=row)
        self.assertEqual(validity[0].args[0]["sql"], row["sql"])
        self.assertEqual([call.args for call in replays[:2]],
                         [("identity", row["sql"]), ("postgres", row["sql"])])
        self.assertIn("qa.users.id + $2", calls[0].kwargs["input"])
        self.assertNotIn("qa.users.id + ?2", calls[0].kwargs["input"])
        self.assertIn("EXECUTE merged_parameters (2, 10)", calls[0].kwargs["input"])

    def test_main_rejects_missing_duplicate_and_corrupted_row_observations(self):
        row = self.case()
        good = transcript(row)
        bad_rows = ([[1, "Ada"]], [[1, "Ada"], [1, "Ada"], [2, "Bea"]],
                    [[1, "Ada"], [2, None]], [[1, "Ada"], [2, "NULL"]], [[1, "Ada"], [3, "Bea"]])
        for values in ["", good + good, *[transcript(row, populated_rows=rows) for rows in bad_rows]]:
            with self.subTest(values=values), self.assertRaises((AssertionError, ValueError)):
                self.exercise_main(values=values)
        # A missing empty observation also fails even though it contains no rows.
        without_first = good[good.index(marker("qualified_names", 1, False, "postgres")):]
        with self.assertRaises(AssertionError):
            self.exercise_main(values=without_first)

    def test_main_rejects_wrong_order_labels_types_or_missing_visibility(self):
        for descriptors in ("", "x|integer\nx|text\n", "x|integer\nx|text\n" * 3,
                            "x|text\nx|integer\n" * 2, "id|integer\nx|text\n" * 2,
                            "x|bigint\nx|text\n" * 2):
            with self.subTest(descriptors=descriptors), self.assertRaises(AssertionError):
                self.exercise_main(descriptors=descriptors)
        for visibility in ("", "t\nf\nt\nt\nf\nt\n", "t\n" * 7, "f\n" * 7,
                           "true\nfalse\ntrue\ntrue\nfalse\ntrue\nfalse\n"):
            with self.subTest(visibility=visibility), self.assertRaises(AssertionError):
                self.exercise_main(visibility=visibility)

    def test_main_demands_exact_analysis_states_including_planning_error_and_success(self):
        good = checker.boundary_script()[1]
        bad = [[], good[:-1], good + ["00000"], list(reversed(good))]
        for index, wrong in ((0, "42702"), (8, "00000"), (8, "57014"), (12, "42703"),
                             (15, "42703"), (21, "00000"), (22, "42702"), (24, "00000")):
            changed = good.copy()
            changed[index] = wrong
            bad.append(changed)
        for states in bad:
            with self.subTest(states=states), self.assertRaises(AssertionError):
                self.exercise_main(states="\n".join(states) + "\n")

    def exercise_locks(self, *, observed=None, handshake=None, rollback=None):
        owner = MagicMock()
        owner.command.side_effect = lambda sql: (
            ([] if rollback is None else rollback) if sql == "ROLLBACK;" else
            (["1"] if handshake is None else handshake))
        outputs = iter(["55P03", "00000"] * 4 if observed is None else observed)

        def native_run(command, **kwargs):
            sql = kwargs["input"]
            if "CREATE FUNCTION pg_temp.probe" in sql:
                self.assertTrue(owner.command.call_args.args[0].startswith("BEGIN; "))
                return subprocess.CompletedProcess([], 0, next(outputs) + "\n", "")
            return subprocess.CompletedProcess([], 0, "", "")

        with patch.object(checker, "PersistentPsql", return_value=owner), \
                patch.object(checker.uuid, "uuid4", return_value=type("UUID", (), {"hex": "fixed"})()), \
                patch.object(checker, "replay", side_effect=lambda mode, sql: {
                    "sql": sql + " /* rendered */"}) as replay, \
                patch.object(checker, "run", side_effect=native_run) as run:
            count = checker.first_lock_observations(["psql"])
            return count, owner, run.call_args_list, replay.call_args_list

    def test_two_sessions_observe_first_of_target_in_both_relation_orders_and_forms(self):
        count, owner, calls, replays = self.exercise_locks()
        self.assertEqual((count, len(calls), len(replays)), (8, 10, 2))
        starts = [call.args[0] for call in owner.command.call_args_list if call.args[0].startswith("BEGIN;")]
        self.assertEqual(len(starts), 4)
        self.assertEqual(sum("/* rendered */" in sql for sql in starts), 2)
        self.assertIn('SELECT "sqlean_names_fixed_a"."users".id', starts[0])
        self.assertIn('SELECT "sqlean_names_fixed_b"."users".id', starts[2])
        for index, call in enumerate(calls[1:-1]):
            first = "a" if index < 4 else "b"
            selected = first if index % 2 == 0 else ("b" if first == "a" else "a")
            sql = call.kwargs["input"]
            self.assertIn(f'PERFORM id FROM "sqlean_names_fixed_{selected}"."users" FOR UPDATE NOWAIT', sql)
            self.assertIn("SET LOCAL statement_timeout = '2s';", sql)
            self.assertIn("RETURN SQLSTATE", sql)
            self.assertEqual(call.kwargs["timeout"], 10)
            self.assertIn("ON_ERROR_STOP=1", call.args[0])
        self.assertEqual(sum(call.args[0] == "ROLLBACK;" for call in owner.command.call_args_list), 4)
        owner.close.assert_called_once_with()
        self.assertTrue(calls[0].kwargs["input"].startswith("BEGIN;\n"))
        self.assertTrue(calls[0].kwargs["input"].endswith("\nCOMMIT;"))
        self.assertEqual(calls[-1].kwargs["input"].count("DROP SCHEMA "), 2)

    def test_lock_probe_rejects_timeout_wrong_target_extra_rows_and_bad_rollback(self):
        for observations in (["57014"], ["00000"], [""], ["55P03\n55P03"], ["55P03", "55P03"]):
            with self.subTest(observations=observations), self.assertRaises(AssertionError):
                self.exercise_locks(observed=observations)
        with self.assertRaises(AssertionError):
            self.exercise_locks(rollback=["not rolled back"])

    def test_unconfirmed_owner_stops_before_probes_and_closes_owner_and_schemas(self):
        for handshake in ([], ["0"], ["1", "1"]):
            owner = MagicMock()
            owner.command.return_value = handshake
            with self.subTest(handshake=handshake), \
                    patch.object(checker, "PersistentPsql", return_value=owner), \
                    patch.object(checker, "replay", side_effect=lambda mode, sql: {"sql": sql}), \
                    patch.object(checker, "run") as run, self.assertRaises(AssertionError):
                checker.first_lock_observations(["psql"])
            self.assertEqual(run.call_count, 2)
            self.assertIn("DROP SCHEMA ", run.call_args.kwargs["input"])
            owner.close.assert_called_once_with()

    def test_owner_construction_failure_still_cleans_up_the_claimed_schemas(self):
        with patch.object(checker, "PersistentPsql", side_effect=RuntimeError("owner failed")), \
                patch.object(checker, "run") as run, self.assertRaisesRegex(RuntimeError, "owner failed"):
            checker.first_lock_observations(["psql"])
        self.assertEqual(run.call_count, 2)
        self.assertTrue(run.call_args_list[0].kwargs["input"].endswith("\nCOMMIT;"))
        self.assertEqual(run.call_args_list[1].kwargs["input"].count("DROP SCHEMA "), 2)


if __name__ == "__main__":
    unittest.main()
