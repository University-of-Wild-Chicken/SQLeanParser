"""Evidence-integrity regressions for the array subscript native harness."""
from contextlib import nullcontext, redirect_stdout
from copy import deepcopy
import io
import json
from pathlib import Path
import subprocess
import tempfile
import unittest
from unittest.mock import patch

import check_array_subscripts_cli as checker
from check_postgresql_cli import NULL


def transcript(category, index, values):
    """Authored COPY records keep SQL NULL separate from quoted text."""
    def field(value):
        return NULL if value is None else '"' + value.replace('"', '""') + '"'
    lines = []
    for form in ("source", "postgres"):
        lines += [
            checker.marker(category, index, True, form),
            '"value","type"' if len(values) == 2 else '"error"',
            ",".join(map(field, values)),
        ]
    return "\n".join(lines) + "\n"


class ArraySubscriptCliTests(unittest.TestCase):
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
            "sql": "SELECT ($1)[$2] AS v;", "sqlite_sql": "SELECT (?1)[?2] AS v;",
            "parameter_types": "numeric(6,2)[]?,int", "parameter_values": [None, 1],
            "output_columns": [{"name": "v", "type": "numeric", "nullable": True}],
            "expected_value": None, "postgres_type": "numeric", "postgres_display_type": "numeric",
        }

    @staticmethod
    def empty_case():
        return {
            "sql": "SELECT (ARRAY[1])[3:4] AS v;",
            "parameter_types": "", "parameter_values": [],
            "output_columns": [{"name": "v", "type": "integer[]", "nullable": True}],
            "expected_value": "{}", "postgres_type": "integer[]", "postgres_display_type": "integer[]",
        }

    def test_fifty_distinct_populations_cover_elements_slices_and_nullable_results(self):
        rows, concrete = checker.load_cases()
        self.assertEqual((len(rows), len(concrete)), (50, 50))
        self.assertTrue(all(row["output_columns"][0]["nullable"] for row in rows))
        self.assertTrue(any(row["expected_value"] is None for row in rows))
        self.assertTrue(any(row["expected_value"] == "{}" for row in rows))
        by_shape = {row["shape"]: row for row in rows}
        self.assertEqual(by_shape["two-dimensional-element"]["expected_value"], "12")
        self.assertEqual(by_shape["insufficient-indices"]["expected_value"], None)
        self.assertEqual(by_shape["element-then-slice"]["expected_value"], "{{11,12},{21,22}}")
        self.assertEqual(by_shape["slice-then-element"]["expected_value"], "{{21,22}}")
        self.assertEqual(by_shape["nested-slice-extraction"]["expected_value"], "22")
        self.assertNotEqual(by_shape["two-dimensional-element"]["output_columns"],
                            by_shape["two-dimensional-slice"]["output_columns"])

    def test_loader_rejects_missing_duplicate_wrong_output_and_wrong_binding_identity(self):
        rows, concrete = checker.load_cases()
        bad = [(rows[:-1], concrete), (rows, concrete[:-1])]
        for key in ("id", "sql"):
            altered = deepcopy(rows)
            altered[1][key] = altered[0][key]
            bad.append((altered, concrete))
        for field, value in (("name", "wrong"), ("nullable", False)):
            altered = deepcopy(rows)
            altered[0]["output_columns"][0][field] = value
            bad.append((altered, concrete))
        altered = deepcopy(rows)
        altered[0]["output_columns"].append(dict(altered[0]["output_columns"][0]))
        bad.append((altered, concrete))
        for mutation in ("values", "sqlite"):
            altered = deepcopy(rows)
            bound = next(row for row in altered if row["parameter_values"])
            if mutation == "values":
                bound["parameter_values"].append(2)
            else:
                bound["sqlite_sql"] = "SELECT (?99)[1] AS v;"
            bad.append((altered, concrete))
        for altered, source in bad:
            with self.subTest(size=len(altered)), \
                    patch.object(checker, "FIXTURES", self.fixture_directory(altered, source)), \
                    self.assertRaises(AssertionError):
                checker.load_cases()

    def test_prepared_parameter_modifiers_are_not_assumed_to_survive_extraction(self):
        row = self.null_case()
        script, expected = checker.database_script([row], [row["sql"]])
        self.assertIn("PREPARE exact_type_parameters (numeric(6,2)[],int)", script)
        self.assertIn("SELECT ($1)[$2] AS v", script)
        self.assertIn("EXECUTE exact_type_parameters (NULL, 1)", script)
        self.assertTrue(all(value == (2, [[None, "numeric"]]) for value in expected.values()))
        description, descriptors = checker.describe_script([row], [row["sql"]])
        self.assertIn("PREPARE array_description (numeric(6,2)[],int)", description)
        self.assertEqual(description.count("\\gdesc"), 2)
        self.assertNotIn("RETURNS TABLE", description)
        self.assertEqual(descriptors, ["v|numeric", "v|numeric"])
        with patch("check_array_types_cli.assert_report") as report:
            checker.validity(row)
        self.assertEqual(report.call_args.args[0],
                         ["--assurance", "contract", "--param-types", row["parameter_types"], row["sql"]])
        self.assertEqual(report.call_args.args[3], (("v", "numeric", True),))

    def test_explicit_cast_modifiers_are_checked_in_the_real_result_descriptor(self):
        rows, _ = checker.load_cases()
        selected = [row for row in rows if row["shape"] in (
            "numeric-modifier", "varchar-modifier", "timestamp-modifier",
            "slice-modifier", "parameter-modifier-erasure")]
        _, descriptors = checker.describe_script(selected, [row["sql"] for row in selected])
        self.assertEqual(descriptors, [
            "v|numeric(6,2)", "v|numeric(6,2)",
            "v|character varying(2)", "v|character varying(2)",
            "v|timestamp(2) without time zone", "v|timestamp(2) without time zone",
            "v|numeric", "v|numeric",
            "v|numeric(6,2)[]", "v|numeric(6,2)[]",
        ])

    def test_anonymous_lower_upper_and_base_parameters_retain_lexical_order(self):
        row = self.empty_case()
        row.update(sql="SELECT (?)[?:?][?] AS v;", parameter_types="int[],int,int,int",
                   parameter_values=["{1,2}", 1, 2, 2])
        script, _ = checker.describe_script([row], [row["sql"]])
        self.assertIn("SELECT ($1)[$2:$3][$4] AS v", script)
        self.assertIn("EXECUTE array_description('{1,2}', 1, 2, 2)", script)
        row.update(sql="SELECT (($2)[$1:$3])[$1] AS v;", parameter_types="int,int[],int",
                   parameter_values=[1, "{1,2}", 2])
        script, _ = checker.describe_script([row], [row["sql"]])
        self.assertIn("SELECT (($2)[$1:$3])[$1] AS v", script)
        self.assertIn("EXECUTE array_description(1, '{1,2}', 2)", script)

    def test_sql_null_cannot_be_confused_with_empty_array_or_text_null(self):
        row = self.null_case()
        _, expected = checker.database_script([row], [row["sql"]])
        actual = checker.parse_results(transcript("exact_types", 1, [None, "numeric"]))
        self.assertEqual(checker.validate_results(actual, expected), 2)
        for value in ("{}", "NULL", NULL, "", "0"):
            actual = checker.parse_results(transcript("exact_types", 1, [value, "numeric"]))
            with self.subTest(value=value), self.assertRaises(AssertionError):
                checker.validate_results(actual, expected)
        row = self.empty_case()
        _, expected = checker.database_script([row], [row["sql"]])
        actual = checker.parse_results(transcript("exact_types", 1, [None, "integer[]"]))
        with self.assertRaises(AssertionError):
            checker.validate_results(actual, expected)

    def test_missing_extra_wrong_arity_wrong_oid_and_wrong_row_count_fail(self):
        expected = {"case": (2, [["{}", "integer[]"]])}
        bad = [{}, {**expected, "extra": expected["case"]}, {"case": (1, [["{}"]])},
               {"case": (2, [["{}", "integer"]])},
               {"case": (2, [["{}", "integer[]"], ["{}", "integer[]"]])}]
        for actual in bad:
            with self.subTest(actual=actual), self.assertRaises(AssertionError):
                checker.validate_results(actual, expected)

    def test_missing_canonical_evidence_cannot_be_silently_zipped(self):
        for function, rows in ((checker.database_script, [self.null_case()]),
                               (checker.describe_script, [self.null_case()]),
                               (checker.error_script, checker.runtime_cases())):
            with self.subTest(function=function.__name__), self.assertRaises(AssertionError):
                function(rows, [])

    def test_runtime_failures_assert_exact_sqlstates_and_detect_unexpected_success(self):
        rows = checker.runtime_cases()
        self.assertEqual([row["sqlstate"] for row in rows], ["22003", "22P02", "22012", "2202E", "22P02"])
        script, expected = checker.error_script(rows, [row["sql"] for row in rows])
        self.assertEqual(len(expected), 10)
        self.assertEqual(script.count("RETURN ''unexpected-success''"), 10)
        self.assertEqual(script.count("RETURN SQLSTATE"), 10)
        self.assertIn("PREPARE pagination_parameters (TEXT)", script)
        for index, row in enumerate(rows, 1):
            for form in ("source", "postgres"):
                self.assertEqual(expected[checker.marker("subscript_error", index, True, form)],
                                 (1, [[row["sqlstate"]]]))

    def exercise_main(self, *, values=None, metadata=None, errors=None):
        rows = [self.null_case(), self.empty_case()]
        concrete = {"sql": "SELECT secret[1] FROM never_execute_concrete;"}
        runtime = checker.runtime_cases()[0]
        values = (transcript("exact_types", 1, [None, "numeric"]) +
                  transcript("exact_types", 2, ["{}", "integer[]"]) if values is None else values)
        metadata = ("v|numeric\n" * 2 + "v|integer[]\n" * 2 if metadata is None else metadata)
        errors = transcript("subscript_error", 1, ["22003"]) if errors is None else errors
        results = [subprocess.CompletedProcess(["psql"], 0, stdout, "") for stdout in
                   (values, metadata, errors, "16.15\n")]
        with patch.object(checker, "load_cases", return_value=(rows, [concrete])), \
                patch.object(checker, "runtime_cases", return_value=[runtime]), \
                patch.object(checker, "label_cases", return_value=[]), \
                patch.object(checker, "validity") as validity, \
                patch.object(checker, "replay", side_effect=lambda mode, sql: {"sql": sql}) as replay, \
                patch.object(checker, "reject_sqlite"), \
                patch.object(checker, "boundaries", return_value=0), \
                patch.object(checker, "connection", return_value=nullcontext(["psql"])), \
                patch.object(checker, "run", side_effect=results) as run, \
                patch("sys.argv", ["check_array_subscripts_cli.py", "--dsn", "unused"]), \
                redirect_stdout(io.StringIO()):
            checker.main()
            return run.call_args_list, validity.call_args_list, replay.call_args_list

    def test_pipeline_executes_only_authored_cases_with_fail_fast_native_commands(self):
        calls, validity, replays = self.exercise_main()
        self.assertEqual(len(calls), 4)
        for call in calls[:3]:
            self.assertIn("ON_ERROR_STOP=1", call.args[0])
            self.assertEqual(call.kwargs["timeout"], 120)
            self.assertNotIn("never_execute_concrete", call.kwargs["input"])
        self.assertEqual(len(validity), 3)
        self.assertEqual(sum("never_execute_concrete" in call.args[1] for call in replays), 2)

    def test_pipeline_rejects_missing_changed_or_reordered_native_type_descriptors(self):
        for metadata in ("", "v|numeric\n" * 2 + "v|integer[]\n",
                         "v|numeric(6,2)\n" * 2 + "v|integer[]\n" * 2,
                         "v|integer[]\n" * 2 + "v|numeric\n" * 2):
            with self.subTest(metadata=metadata), self.assertRaises(AssertionError):
                self.exercise_main(metadata=metadata)

    def test_pipeline_rejects_wrong_null_values_and_missing_copy_evidence(self):
        for values in ("", transcript("exact_types", 1, ["0", "numeric"]) +
                       transcript("exact_types", 2, ["{}", "integer[]"]),
                       transcript("exact_types", 1, [None, "numeric"])):
            with self.subTest(values=values), self.assertRaises(AssertionError):
                self.exercise_main(values=values)

    def test_pipeline_rejects_success_missing_and_wrong_runtime_error_evidence(self):
        for state in ("unexpected-success", "00000", "57014", "2202E"):
            with self.subTest(state=state), self.assertRaises(AssertionError):
                self.exercise_main(errors=transcript("subscript_error", 1, [state]))
        with self.assertRaises(AssertionError):
            self.exercise_main(errors="")

    def test_copy_parser_rejects_duplicate_markers_and_wrong_row_arity(self):
        output = transcript("exact_types", 1, [None, "numeric"])
        with self.assertRaisesRegex(ValueError, "Duplicate case marker"):
            checker.parse_results(output + output)
        key = checker.marker("exact_types", 1, True, "source")
        with self.assertRaisesRegex(ValueError, "Wrong result arity"):
            checker.parse_results(key + '\n"value","type"\n"0"\n')

    def test_syntax_boundaries_use_structured_renderer_parse_failures(self):
        result = subprocess.CompletedProcess([], 1, json.dumps({
            "status": "invalid", "diagnostic": {"code": "input.parse"}}), "")
        with patch.object(checker, "assert_report") as reports, \
                patch.object(checker, "invoke", return_value=result) as invoke:
            self.assertEqual(checker.boundaries(), 20)
        self.assertEqual(len(invoke.call_args_list), 8)
        self.assertTrue(all(call.args[0][:2] == ["--render-assurance", "identity"]
                            for call in invoke.call_args_list))
        self.assertEqual(sum(call.args[1] == "invalid" for call in reports.call_args_list), 9)
        self.assertEqual(sum(call.args[1] == "unsupported" for call in reports.call_args_list), 2)
        self.assertEqual(reports.call_args_list[-1].args[1:3], ("rejected", "checked"))

    def test_parse_boundary_cannot_pass_on_options_resources_or_success(self):
        for code, status, diagnostic in (
                (0, "rendered", "input.parse"), (2, "invalid", "input.parse"),
                (1, "unsupported", "input.parse"), (1, "invalid", "resource.depth")):
            result = subprocess.CompletedProcess([], code, json.dumps({
                "status": status, "diagnostic": {"code": diagnostic}}), "")
            with self.subTest(code=code, status=status, diagnostic=diagnostic), \
                    patch.object(checker, "invoke", return_value=result), \
                    self.assertRaises(AssertionError):
                checker.parse_failure("SELECT ARRAY[1][1]")


if __name__ == "__main__":
    unittest.main()
