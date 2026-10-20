"""Protocol regressions for row comparisons and separate dialect evidence."""
from contextlib import nullcontext, redirect_stdout
from copy import deepcopy
import io
import json
from pathlib import Path
import subprocess
import tempfile
import unittest
from unittest.mock import patch

import check_row_comparisons_cli as checker
from check_postgresql_cli import NULL


def transcript(category, index, values):
    def field(value):
        return NULL if value is None else '"' + value.replace('"', '""') + '"'
    lines = []
    for form in ("source", "postgres"):
        lines += [checker.marker(category, index, True, form),
                  '"value","type"' if len(values) == 2 else '"error"',
                  ",".join(map(field, values))]
    return "\n".join(lines) + "\n"


class RowComparisonCliTests(unittest.TestCase):
    def fixture_directory(self, rows, concrete):
        directory = tempfile.TemporaryDirectory()
        self.addCleanup(directory.cleanup)
        root = Path(directory.name)
        (root / "synthetic.json").write_text(json.dumps(rows))
        (root / "concrete.jsonl").write_text("".join(json.dumps(row) + "\n" for row in concrete))
        return root

    @staticmethod
    def null_case():
        return {
            "id": "null", "sql": "SELECT ROW($1,2) = ROW(1,$2) AS v;",
            "sqlite_input": "SELECT (?1,2) = (1,?2) AS v;",
            "sqlite_sql": "SELECT (?1,2) = (1,?2) AS v;", "sqlite_supported": True,
            "parameter_types": "int?,int", "parameter_values": [None, 2],
            "output_columns": [{"name": "v", "type": "bool", "nullable": True}],
            "expected_value": None, "sqlite_value": None,
            "postgres_type": "boolean", "postgres_display_type": "boolean",
        }

    @staticmethod
    def different_dialect_case():
        return {
            "id": "unknown", "sql": "SELECT ROW('1',NULL) = ROW(1,NULL::INTEGER) AS v;",
            "sqlite_input": "SELECT ('1',NULL) = (1,CAST(NULL AS INTEGER)) AS v;",
            "sqlite_sql": None, "sqlite_supported": True,
            "parameter_types": "", "parameter_values": [],
            "output_columns": [{"name": "v", "type": "bool", "nullable": True}],
            "expected_value": None, "sqlite_value": 0,
            "postgres_type": "boolean", "postgres_display_type": "boolean",
        }

    def test_populations_and_dialect_expectations_are_explicit_and_distinct(self):
        rows, concrete = checker.load_cases()
        self.assertEqual((len(rows), len(concrete)), (50, 50))
        self.assertEqual(sum(row["sqlite_supported"] for row in rows), 38)
        self.assertEqual(sum(row["sqlite_sql"] is not None for row in rows), 28)
        by_shape = {row["shape"]: row for row in rows}
        for shape in ("contextual-unknown", "numeric-unknown", "numeric-modifier", "varchar-modifier"):
            self.assertEqual(by_shape[shape]["sqlite_value"], 0)
            self.assertNotEqual(by_shape[shape]["expected_value"], "false")
        self.assertFalse(by_shape["single-field"]["sqlite_supported"])
        self.assertFalse(by_shape["single-null"]["sqlite_supported"])
        self.assertEqual(by_shape["single-field"]["expected_value"], "true")

    def test_loader_rejects_missing_duplicate_metadata_and_dialect_population_changes(self):
        rows, concrete = checker.load_cases()
        bad = [(rows[:-1], concrete), (rows, concrete[:-1])]
        for key in ("id", "sql"):
            altered = deepcopy(rows)
            altered[1][key] = altered[0][key]
            bad.append((altered, concrete))
        for key, value in (("name", "wrong"), ("type", "integer"), ("nullable", False)):
            altered = deepcopy(rows)
            altered[0]["output_columns"][0][key] = value
            bad.append((altered, concrete))
        for mutation in ("supported", "source", "binding", "input_binding", "value"):
            altered = deepcopy(rows)
            if mutation == "supported":
                next(row for row in altered if not row["sqlite_supported"])["sqlite_supported"] = True
            elif mutation == "source":
                next(row for row in altered if row["sqlite_sql"] is not None)["sqlite_sql"] = None
            elif mutation == "binding":
                next(row for row in altered if row["parameter_values"] and row["sqlite_sql"])["sqlite_sql"] = \
                    "SELECT (?99,1) = (1,2) AS v;"
            elif mutation == "input_binding":
                next(row for row in altered if row["parameter_values"])["sqlite_input"] = \
                    "SELECT (?99,1) = (1,2) AS v;"
            else:
                next(row for row in altered if row["parameter_values"])["parameter_values"].append(3)
            bad.append((altered, concrete))
        for altered, source in bad:
            with self.subTest(size=len(altered)), \
                    patch.object(checker, "FIXTURES", self.fixture_directory(altered, source)), \
                    self.assertRaises(AssertionError):
                checker.load_cases()

    def test_operator_catalog_requires_all_strategies_and_equality_negators(self):
        script, expected = checker.operator_script()
        lines = script.splitlines()
        self.assertEqual(len(lines), 198)
        self.assertEqual(expected, [f"{i}|t" for i in range(198)])
        strategies = {"<": 1, "<=": 2, "=": 3, ">=": 4, ">": 5, "<>": 3}
        signatures = json.loads(checker.SIGNATURES.read_text())
        signatures += [{"operator": op, "left": "anyarray", "right": "anyarray"} for op in strategies]
        for line, signature in zip(lines, signatures):
            operator = signature["operator"]
            self.assertIn(f"a.amopstrategy={strategies[operator]}", line)
            self.assertIn("a.amopopr=" + ("o.oprnegate" if operator == "<>" else "o.oid"), line)
            for clause in (
                    "o.oprnamespace='pg_catalog'::regnamespace", "o.oprleft=", "o.oprright=",
                    "o.oprresult='boolean'::regtype", "p.prorettype='boolean'::regtype",
                    "p.proisstrict", "NOT p.proretset", "p.pronargs=2", "p.prokind='f'",
                    "am.amname='btree'", "f.opfnamespace='pg_catalog'::regnamespace",
                    "a.amoppurpose='s'", "a.amoplefttype=o.oprleft", "a.amoprighttype=o.oprright"):
                self.assertIn(clause, line)
        self.assertEqual(script.count("a.amopopr=o.oprnegate"), 33)
        self.assertEqual(script.count("o.oprleft='anyarray'::regtype"), 6)
        self.assertEqual(script.count("o.oprright='anyarray'::regtype"), 6)

    def test_operator_catalog_rejects_missing_or_duplicated_signature_evidence(self):
        rows = json.loads(checker.SIGNATURES.read_text())
        for altered in (rows[:-1], rows + rows[:1], rows[:-1] + rows[:1]):
            with tempfile.TemporaryDirectory() as directory:
                path = Path(directory) / "signatures.json"
                path.write_text(json.dumps(altered))
                with self.subTest(length=len(altered)), \
                        patch.object(checker, "SIGNATURES", path), self.assertRaises(AssertionError):
                    checker.operator_script()

    def test_parameters_follow_complete_left_then_right_rows_without_value_substitution(self):
        row = self.null_case()
        row.update(sql="SELECT ROW(?,?) < ROW(?,?) AS v;",
                   parameter_types="int,int,int,int", parameter_values=[1, 2, 1, 3])
        script, descriptors = checker.describe_script([row], [row["sql"]])
        self.assertIn("SELECT ROW($1,$2) < ROW($3,$4) AS v", script)
        self.assertIn("PREPARE array_description (int,int,int,int)", script)
        self.assertIn("EXECUTE array_description(1, 2, 1, 3)", script)
        self.assertEqual(descriptors, ["v|boolean", "v|boolean"])
        self.assertNotIn("RETURNS TABLE", script)
        row.update(sql="SELECT ROW($2,$1,$2) > ROW($1,$2,$1) AS v;",
                   parameter_types="int,int", parameter_values=[1, 2])
        script, _ = checker.describe_script([row], [row["sql"]])
        self.assertIn(row["sql"], script)
        self.assertIn("EXECUTE array_description(1, 2)", script)

    def test_sqlite_uses_its_authored_oracle_without_borrowing_postgresql_null(self):
        row = self.different_dialect_case()
        canonical = "SELECT (('1',NULL) = (1,CAST(NULL AS INTEGER))) AS v;"
        self.assertEqual(checker.sqlite_observations([row], [canonical]), 1)
        row["sqlite_value"] = None
        with self.assertRaises(AssertionError):
            checker.sqlite_observations([row], [canonical])
        row = self.different_dialect_case()
        row["expected_value"] = "false"  # Irrelevant to the independent SQLite assertion.
        self.assertEqual(checker.sqlite_observations([row], [canonical]), 1)

    def test_sqlite_numeric_unknown_fields_are_not_postgresql_contextually_coerced(self):
        rows, _ = checker.load_cases()
        row = next(row for row in rows if row["shape"] == "numeric-unknown")
        canonical = "SELECT ((1.25,'2.5') = (CAST(1.25 AS NUMERIC),2.5)) AS v;"
        self.assertEqual(checker.sqlite_observations([row], [canonical]), 1)
        wrong = deepcopy(row)
        wrong["sqlite_value"] = 1
        with self.assertRaises(AssertionError):
            checker.sqlite_observations([wrong], [canonical])

    def test_sqlite_rejects_missing_rendering_extra_rows_and_wrong_labels(self):
        row = self.null_case()
        self.assertEqual(checker.sqlite_observations([row], [row["sqlite_sql"]]), 2)
        for rendered in (None, "SELECT ?1 AS wrong WHERE ?2=2;",
                         "SELECT ?1 AS v WHERE ?2=2 UNION ALL SELECT NULL;"):
            with self.subTest(rendered=rendered), self.assertRaises(AssertionError):
                checker.sqlite_observations([row], [rendered])
        with self.assertRaises(AssertionError):
            checker.sqlite_observations([row], [])
        excluded = dict(row, sqlite_supported=False, sqlite_sql=None)
        self.assertEqual(checker.sqlite_observations([excluded], [None]), 0)
        with self.assertRaises(AssertionError):
            checker.sqlite_observations([excluded], [row["sqlite_sql"]])

    def test_sqlite_numbered_bindings_preserve_slot_identity_and_detect_reordering(self):
        row = dict(self.null_case(), parameter_types="int,int", parameter_values=[1, 9],
                   sqlite_sql=None, sqlite_value=1)
        canonical = "SELECT (?2,?1,?2) > (?1,?2,?1) AS v;"
        self.assertEqual(checker.sqlite_observations([row], [canonical]), 1)
        wrong = "SELECT (?1,?2,?1) > (?2,?1,?2) AS v;"
        with self.assertRaises(AssertionError):
            checker.sqlite_observations([row], [wrong])
        # A repeated slot is one binding, even when its first appearance is out of order.
        self.assertEqual(checker.sqlite_bindings(canonical, [1, 9]), {"1": 1, "2": 9})

    def test_sqlite_profile_uses_explicit_dialect_input_and_never_postgresql_row_keyword(self):
        row = self.null_case()
        with patch.object(checker, "replay", return_value={"sql": "rendered"}) as replay:
            self.assertEqual(checker.sqlite_render(row), "rendered")
        replay.assert_called_once_with("sqlite", row["sqlite_input"])
        self.assertIn("ROW(", row["sql"])
        self.assertNotIn("ROW(", row["sqlite_input"])

    def test_sqlite_profile_exclusions_require_structured_parser_or_coverage_failure(self):
        row = dict(self.null_case(), sqlite_supported=False)
        for code, status, diagnostic in ((3, "unsupported", "coverage.sqlite.row-arity"),
                                        (1, "invalid", "input.parse")):
            good = subprocess.CompletedProcess([], code, json.dumps({
                "status": status, "diagnostic": {"code": diagnostic}}), "")
            with patch.object(checker, "invoke", return_value=good) as invoke:
                self.assertIsNone(checker.sqlite_render(row))
            self.assertEqual(invoke.call_args.args[0], ["--render-assurance", "sqlite"])
            self.assertEqual(invoke.call_args.kwargs["stdin"], row["sqlite_input"])
        for code, status, diagnostic in ((0, "rendered", "coverage.sqlite.row-arity"),
                                         (1, "unsupported", "input.parse"),
                                         (1, "invalid", "coverage.sqlite.row-arity"),
                                         (3, "unsupported", "input.parse"),
                                         (3, "unsupported", "resource.depth")):
            result = subprocess.CompletedProcess([], code, json.dumps({
                "status": status, "diagnostic": {"code": diagnostic}}), "")
            with self.subTest(code=code, diagnostic=diagnostic), \
                    patch.object(checker, "invoke", return_value=result), self.assertRaises(AssertionError):
                checker.sqlite_render(row)

    def test_sql_null_cannot_be_confused_with_false_true_or_text_null(self):
        row = self.null_case()
        _, expected = checker.database_script([row], [row["sql"]])
        actual = checker.parse_results(transcript("exact_types", 1, [None, "boolean"]))
        self.assertEqual(checker.validate_results(actual, expected), 2)
        for value in ("false", "true", "NULL", NULL, ""):
            actual = checker.parse_results(transcript("exact_types", 1, [value, "boolean"]))
            with self.subTest(value=value), self.assertRaises(AssertionError):
                checker.validate_results(actual, expected)

    def test_missing_extra_wrong_arity_wrong_oid_and_wrong_row_count_fail(self):
        expected = {"case": (2, [[None, "boolean"]])}
        bad = [{}, {**expected, "extra": expected["case"]}, {"case": (1, [[None]])},
               {"case": (2, [[None, "integer"]])},
               {"case": (2, [[None, "boolean"], [None, "boolean"]])}]
        for actual in bad:
            with self.subTest(actual=actual), self.assertRaises(AssertionError):
                checker.validate_results(actual, expected)

    def test_missing_canonical_evidence_cannot_be_silently_zipped(self):
        for function, rows in ((checker.database_script, [self.null_case()]),
                               (checker.describe_script, [self.null_case()]),
                               (checker.error_script, checker.runtime_cases())):
            with self.subTest(function=function.__name__), self.assertRaises(AssertionError):
                function(rows, [])

    def test_runtime_errors_keep_exact_states_and_reject_unexpected_success(self):
        rows = checker.runtime_cases()
        self.assertEqual([row["sqlstate"] for row in rows], ["22P02", "22012", "22003", "2202E", "22023"])
        script, expected = checker.error_script(rows, [row["sql"] for row in rows])
        self.assertEqual(len(expected), 10)
        self.assertEqual(script.count("RETURN ''unexpected-success''"), 10)
        self.assertEqual(script.count("RETURN SQLSTATE"), 10)
        for index, row in enumerate(rows, 1):
            for form in ("source", "postgres"):
                self.assertEqual(expected[checker.marker("row_error", index, True, form)],
                                 (1, [[row["sqlstate"]]]))

    def exercise_main(self, *, values=None, metadata=None, operators=None, errors=None):
        row = self.null_case()
        concrete = {"sql": "SELECT (secret,1) = (2,3) FROM never_execute_concrete;"}
        runtime, label = checker.runtime_cases()[0], checker.label_cases()[0]
        values = transcript("exact_types", 1, [None, "boolean"]) if values is None else values
        metadata = "v|boolean\n" * 2 + "?column?|boolean\n" * 2 if metadata is None else metadata
        operators = "\n".join(f"{i}|t" for i in range(198)) + "\n" if operators is None else operators
        errors = transcript("row_error", 1, ["22P02"]) if errors is None else errors
        results = [subprocess.CompletedProcess(["psql"], 0, stdout, "") for stdout in
                   (values, metadata, operators, errors, "16.15\n")]
        with patch.object(checker, "load_cases", return_value=([row], [concrete])), \
                patch.object(checker, "runtime_cases", return_value=[runtime]), \
                patch.object(checker, "label_cases", return_value=[label]), \
                patch.object(checker, "validity") as validity, \
                patch.object(checker, "replay", side_effect=lambda mode, sql: {"sql": sql}) as replay, \
                patch.object(checker, "sqlite_render", return_value=row["sqlite_sql"]), \
                patch.object(checker, "boundaries", return_value=0), \
                patch.object(checker, "connection", return_value=nullcontext(["psql"])), \
                patch.object(checker, "run", side_effect=results) as run, \
                patch("sys.argv", ["check_row_comparisons_cli.py", "--dsn", "unused"]), \
                redirect_stdout(io.StringIO()):
            checker.main()
            return run.call_args_list, validity.call_args_list, replay.call_args_list

    def test_pipeline_executes_only_authored_cases_with_fail_fast_native_commands(self):
        calls, validity, replays = self.exercise_main()
        self.assertEqual(len(calls), 5)
        for call in calls[:4]:
            self.assertIn("ON_ERROR_STOP=1", call.args[0])
            self.assertEqual(call.kwargs["timeout"], 120)
            self.assertNotIn("never_execute_concrete", call.kwargs["input"])
        self.assertEqual(len(validity), 3)
        self.assertEqual(sum("never_execute_concrete" in call.args[1] for call in replays), 2)

    def test_pipeline_rejects_missing_changed_and_nonboolean_descriptors(self):
        for metadata in ("", "v|boolean\n" * 2 + "?column?|boolean\n",
                         "v|integer\n" * 2 + "?column?|boolean\n" * 2,
                         "v|boolean\n" * 2 + "wrong|boolean\n" * 2):
            with self.subTest(metadata=metadata), self.assertRaises(AssertionError):
                self.exercise_main(metadata=metadata)

    def test_pipeline_rejects_missing_false_duplicated_and_reordered_btree_observations(self):
        expected = [f"{i}|t" for i in range(198)]
        bad = [[], expected[:-1], ["0|f"] + expected[1:], expected + expected[:1],
               [expected[1], expected[0]] + expected[2:]]
        for lines in bad:
            with self.subTest(lines=lines[:2]), self.assertRaises(AssertionError):
                self.exercise_main(operators="\n".join(lines) + "\n")

    def test_pipeline_rejects_wrong_null_or_missing_copy_evidence(self):
        for values in ("", transcript("exact_types", 1, ["false", "boolean"])):
            with self.subTest(values=values), self.assertRaises(AssertionError):
                self.exercise_main(values=values)

    def test_pipeline_rejects_missing_wrong_or_unexpected_success_error_observations(self):
        for state in ("unexpected-success", "00000", "57014", "2202E"):
            with self.subTest(state=state), self.assertRaises(AssertionError):
                self.exercise_main(errors=transcript("row_error", 1, [state]))
        with self.assertRaises(AssertionError):
            self.exercise_main(errors="")

    def test_copy_parser_rejects_duplicate_markers_and_wrong_row_arity(self):
        output = transcript("exact_types", 1, [None, "boolean"])
        with self.assertRaisesRegex(ValueError, "Duplicate case marker"):
            checker.parse_results(output + output)
        key = checker.marker("exact_types", 1, True, "source")
        with self.assertRaisesRegex(ValueError, "Wrong result arity"):
            checker.parse_results(key + '\n"value","type"\n"false"\n')

    def test_parser_boundaries_require_structured_input_parse_errors(self):
        good = subprocess.CompletedProcess([], 1, json.dumps({
            "status": "invalid", "diagnostic": {"code": "input.parse"}}), "")
        with patch.object(checker, "assert_report") as reports, \
                patch.object(checker, "invoke", return_value=good) as invoke:
            self.assertEqual(checker.boundaries(), 21)
        self.assertEqual(len(invoke.call_args_list), 5)
        self.assertTrue(all(call.args[0][:2] == ["--render-assurance", "identity"]
                            for call in invoke.call_args_list))
        self.assertEqual(sum(call.args[1] == "invalid" for call in reports.call_args_list), 9)
        self.assertEqual(sum(call.args[1] == "unsupported" for call in reports.call_args_list), 6)
        for code, status, diagnostic in ((0, "rendered", "input.parse"),
                                         (1, "invalid", "resource.depth"),
                                         (3, "unsupported", "input.parse")):
            result = subprocess.CompletedProcess([], code, json.dumps({
                "status": status, "diagnostic": {"code": diagnostic}}), "")
            with self.subTest(code=code, diagnostic=diagnostic), \
                    patch.object(checker, "assert_report"), \
                    patch.object(checker, "invoke", return_value=result), self.assertRaises(AssertionError):
                checker.boundaries()


if __name__ == "__main__":
    unittest.main()
