"""Evidence-integrity tests for ILIKE/regex native observations and exclusions."""
from contextlib import nullcontext, redirect_stdout
from copy import deepcopy
import io
import json
from pathlib import Path
import subprocess
import tempfile
import unittest
from unittest.mock import patch

import check_pattern_matching_cli as checker
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


class PatternMatchingCliTests(unittest.TestCase):
    def fixture_root(self, populations=None, signatures=None):
        temporary = tempfile.TemporaryDirectory()
        self.addCleanup(temporary.cleanup)
        root = Path(temporary.name)
        if populations is not None:
            for factor, (rows, concrete) in populations.items():
                directory = root / "fixtures" / factor
                directory.mkdir(parents=True)
                (directory / "synthetic.json").write_text(json.dumps(rows))
                (directory / "concrete.jsonl").write_text(
                    "".join(json.dumps(row) + "\n" for row in concrete))
        if signatures is not None:
            directory = root / "fixtures/pattern_matching"
            directory.mkdir(parents=True)
            (directory / "operator_signatures.json").write_text(json.dumps(signatures))
        return root

    @staticmethod
    def populations():
        return {
            factor: (
                json.loads((checker.ROOT / "fixtures" / factor / "synthetic.json").read_text()),
                [json.loads(line) for line in
                 (checker.ROOT / "fixtures" / factor / "concrete.jsonl").read_text().splitlines()],
            ) for factor in ("ilike", "regex")
        }

    @staticmethod
    def null_case():
        return {
            "id": "null-pattern", "source_kind": "synthetic",
            "sql": "SELECT $1 ILIKE $2 AS v;", "parameter_types": "text?,text",
            "parameter_values": [None, "a%"],
            "output_columns": [{"name": "v", "type": "bool", "nullable": True}],
            "postgres_type": "boolean", "postgres_display_type": "boolean",
            "expected_value": None, "sqlite_input": "SELECT ?1 ILIKE ?2 AS v;",
            "sqlite_supported": False,
        }

    def test_two_closed_populations_keep_padding_null_and_generic_precedence_cases(self):
        rows, source = checker.load_cases()
        self.assertEqual((len(rows), len(source)), (100, 100))
        self.assertEqual(sum(row["output_columns"][0]["type"] == "text" for row in rows), 2)
        self.assertTrue(all(row["sqlite_supported"] is False for row in rows))
        for factor in ("ilike", "regex"):
            cases = {row["shape"]: row for row in rows if row["id"].startswith(factor + "-")}
            self.assertEqual(cases["char-subject-padding"]["expected_value"], "false")
            self.assertEqual(cases["char-pattern-trim"]["expected_value"], "true")
            self.assertEqual(cases["explicit-char-text"]["expected_value"], "true")
            self.assertIsNone(cases["null-bad-pattern"]["expected_value"])
            self.assertTrue(cases["null-bad-pattern"]["output_columns"][0]["nullable"])
        regex = {row["shape"]: row for row in rows if row["id"].startswith("regex-")}
        self.assertEqual(regex["generic-left-association"]["expected_value"], "truebc")
        self.assertEqual(regex["not-generic-left-association"]["expected_value"], "falsebc")

    def test_loader_rejects_missing_duplicate_or_cross_typed_result_metadata(self):
        original = self.populations()
        mutations = ("missing_synthetic", "missing_source", "duplicate_id", "duplicate_sql",
                     "name", "type", "nullable", "arity", "native_type", "native_display",
                     "null_nonnullable", "expected_nonstring", "source_kind", "sqlite_supported",
                     "binding_count", "binding_order")
        for mutation in mutations:
            populations = deepcopy(original)
            rows, concrete = populations["ilike"]
            if mutation == "missing_synthetic":
                rows.pop()
            elif mutation == "missing_source":
                concrete.pop()
            elif mutation.startswith("duplicate_"):
                key = mutation.removeprefix("duplicate_")
                rows[1][key] = rows[0][key]
            elif mutation in ("name", "type", "nullable"):
                rows[0]["output_columns"][0][mutation] = {
                    "name": "wrong", "type": "integer", "nullable": 1,
                }[mutation]
            elif mutation == "arity":
                rows[0]["output_columns"].append(rows[0]["output_columns"][0])
            elif mutation == "native_type":
                rows[0]["postgres_type"] = "text"
            elif mutation == "native_display":
                rows[0]["postgres_display_type"] = "bool"
            elif mutation == "null_nonnullable":
                rows[0]["expected_value"] = None
            elif mutation == "expected_nonstring":
                rows[0]["expected_value"] = True
            elif mutation == "source_kind":
                rows[0]["source_kind"] = "application-constant"
            elif mutation == "sqlite_supported":
                rows[0]["sqlite_supported"] = True
            else:
                row = next(row for row in rows if row["shape"] == "reordered")
                if mutation == "binding_count":
                    row["parameter_values"].append("unused")
                else:
                    row["sqlite_input"] = "SELECT ?1 ILIKE ?2 AS v;"
            with self.subTest(mutation=mutation), \
                    patch.object(checker, "ROOT", self.fixture_root(populations)), \
                    self.assertRaises(AssertionError):
                checker.load_cases()

    def test_ten_inventory_signatures_plus_two_native_not_ilike_overloads_are_exact(self):
        script, expected = checker.operator_script()
        self.assertEqual(expected, [f"{index}|t" for index in range(12)])
        rows = json.loads((checker.ROOT / "fixtures/pattern_matching/operator_signatures.json").read_text())
        self.assertEqual(len(rows), 10)
        wanted = {
            (operator, left, "text", "boolean", left + suffix)
            for operator, suffix in (("~~*", "iclike"), ("~", "regexeq"), ("~*", "icregexeq"),
                                     ("!~", "regexne"), ("!~*", "icregexne"))
            for left in ("text", "bpchar")
        }
        self.assertEqual({tuple(row[key] for key in ("operator", "left", "right", "output", "function"))
                          for row in rows}, wanted)
        extended = rows + [
            {"operator": "!~~*", "left": left, "right": "text", "output": "boolean",
             "function": left + "icnlike"} for left in ("text", "bpchar")
        ]
        for line, row in zip(script.splitlines(), extended):
            for clause in (
                    "o.oprnamespace='pg_catalog'::regnamespace",
                    f"o.oprname='{row['operator']}'",
                    f"o.oprleft='{row['left']}'::regtype", "o.oprright='text'::regtype",
                    "o.oprresult='boolean'::regtype", "p.prorettype='boolean'::regtype",
                    f"p.proname='{row['function']}'", "p.pronamespace='pg_catalog'::regnamespace",
                    f"p.proargtypes[0]='{row['left']}'::regtype", "p.proargtypes[1]='text'::regtype",
                    "p.proisstrict", "NOT p.proretset", "p.pronargs=2", "p.prokind='f'"):
                self.assertIn(clause, line)

    def test_operator_inventory_cannot_omit_duplicate_or_retype_a_family(self):
        rows = json.loads((checker.ROOT / "fixtures/pattern_matching/operator_signatures.json").read_text())
        bad = [rows[:-1], rows + rows[:1], rows[:-1] + rows[:1]]
        for key, value in (("left", "varchar"), ("right", "bpchar"), ("output", "text"),
                           ("function", "textlike"), ("operator", "~~")):
            changed = deepcopy(rows)
            changed[0][key] = value
            bad.append(changed)
        for changed in bad:
            with self.subTest(changed=changed[0]), \
                    patch.object(checker, "ROOT", self.fixture_root(signatures=changed)), \
                    self.assertRaises(AssertionError):
                checker.operator_script()

    def test_native_prepared_queries_retain_parameter_order_and_output_descriptors(self):
        row = dict(self.null_case(), sql="SELECT $2 ILIKE $1 AS v;", parameter_types="text,text",
                   parameter_values=["a%", "AbC"], expected_value="true")
        source, expected = checker.database_script([row], [row["sql"]])
        self.assertIn("SET LOCAL statement_timeout = '5s'", source)
        self.assertIn("SET LOCAL standard_conforming_strings = on", source)
        self.assertIn("PREPARE exact_type_parameters (text,text)", source)
        self.assertIn("SELECT $2 ILIKE $1 AS v", source)
        self.assertIn("EXECUTE exact_type_parameters (''''a%'''', ''''AbC'''')", source)
        self.assertTrue(all(value == (2, [["true", "boolean"]]) for value in expected.values()))
        description, descriptors = checker.describe_script([row], [row["sql"]])
        self.assertEqual(description.count("\\gdesc"), 2)
        self.assertEqual(description.count("SELECT $2 ILIKE $1 AS v;"), 2)
        self.assertIn("EXECUTE array_description('a%', 'AbC')", description)
        self.assertEqual(descriptors, ["v|boolean"] * 2)
        self.assertNotIn("RETURNS TABLE", description)

    def test_anonymous_repeated_and_nullable_bindings_are_not_inlined_or_reordered(self):
        row = dict(self.null_case(), sql="SELECT ? !~* ? AS v;", parameter_types="text,text",
                   parameter_values=["AbC", "^z"], expected_value="true")
        script, _ = checker.describe_script([row], [row["sql"]])
        self.assertIn("SELECT $1 !~* $2 AS v;", script)
        self.assertIn("EXECUTE array_description('AbC', '^z')", script)
        row.update(sql="SELECT $1 ~ $1 AS v;", parameter_types="text",
                   parameter_values=["abc"])
        script, _ = checker.describe_script([row], [row["sql"]])
        self.assertEqual(script.count("SELECT $1 ~ $1 AS v;"), 2)
        self.assertIn("PREPARE array_description (text)", script)
        with patch("check_array_types_cli.assert_report") as report:
            checker.validity(self.null_case())
        self.assertEqual(report.call_args.args[0], [
            "--assurance", "contract", "--param-types", "text?,text", "SELECT $1 ILIKE $2 AS v;",
        ])
        self.assertEqual(report.call_args.args[3], (("v", "bool", True),))

    def test_null_false_and_text_results_cannot_substitute_for_boolean_evidence(self):
        row = self.null_case()
        _, expected = checker.database_script([row], [row["sql"]])
        good = checker.parse_results(transcript("exact_types", 1, [None, "boolean"]))
        self.assertEqual(checker.validate_results(good, expected), 2)
        for value, type_ in (("false", "boolean"), ("NULL", "boolean"), ("null", "boolean"),
                              (None, "text"), ("truebc", "text")):
            actual = checker.parse_results(transcript("exact_types", 1, [value, type_]))
            with self.subTest(value=value, type=type_), self.assertRaises(AssertionError):
                checker.validate_results(actual, expected)

    def test_runtime_invalid_patterns_keep_exact_errors_separate_from_static_nullability(self):
        rows = checker.runtime_cases()
        self.assertEqual([row["sqlstate"] for row in rows], ["2201B"] * 4 + ["22025"] * 2)
        self.assertTrue(all(not row["output_columns"][0]["nullable"] for row in rows))
        script, expected = checker.error_script(rows, [row["sql"] for row in rows])
        self.assertEqual(len(expected), 12)
        self.assertEqual(script.count("RETURN ''unexpected-success''"), 12)
        self.assertEqual(script.count("RETURN SQLSTATE"), 12)
        self.assertEqual(script.count("DEALLOCATE pagination_parameters;"), 12)
        for index, row in enumerate(rows, 1):
            for form in ("source", "postgres"):
                self.assertEqual(expected[checker.marker("pattern_error", index, True, form)],
                                 (1, [[row["sqlstate"]]]))

    def test_missing_rendered_evidence_cannot_disappear_through_zip(self):
        for function, cases in ((checker.database_script, [self.null_case()]),
                                (checker.describe_script, [self.null_case()]),
                                (checker.error_script, checker.runtime_cases())):
            with self.subTest(function=function.__name__), self.assertRaises(AssertionError):
                function(cases, [])

    def test_sqlite_exclusions_require_matching_exit_status_and_diagnostic(self):
        case = self.null_case()
        accepted = ((1, "invalid", "input.parse"),
                    (3, "unsupported", "coverage.sqlite.ILIKE"),
                    (3, "unsupported", "coverage.sqlite.regex"))
        for code, status, diagnostic in accepted:
            result = subprocess.CompletedProcess([], code, json.dumps({
                "status": status, "diagnostic": {"code": diagnostic}}), "")
            with patch.object(checker, "invoke", return_value=result) as invoke:
                checker.reject_sqlite(case)
            self.assertEqual(invoke.call_args.args[0], ["--render-assurance", "sqlite"])
            self.assertEqual(invoke.call_args.kwargs["stdin"], case["sqlite_input"])
        rejected = ((0, "rendered", "coverage.sqlite.regex"),
                    (3, "invalid", "input.parse"), (1, "unsupported", "coverage.sqlite.ILIKE"),
                    (1, "invalid", "coverage.sqlite.regex"), (3, "unsupported", "input.parse"),
                    (3, "unsupported", "coverage.sqlite.type"), (3, "unsupported", "resource.depth"))
        for code, status, diagnostic in rejected:
            result = subprocess.CompletedProcess([], code, json.dumps({
                "status": status, "diagnostic": {"code": diagnostic}}), "")
            with self.subTest(status=status, diagnostic=diagnostic), \
                    patch.object(checker, "invoke", return_value=result), self.assertRaises(AssertionError):
                checker.reject_sqlite(case)

    def test_labels_keep_boolean_and_generic_operator_result_names(self):
        labels = checker.label_cases()
        self.assertEqual(len(labels), 8)
        self.assertEqual({row["output_columns"][0]["name"] for row in labels}, {"?column?"})
        script, expected = checker.describe_script(labels, [row["sql"] for row in labels])
        self.assertEqual(expected, ["?column?|boolean"] * 14 + ["?column?|text"] * 2)
        self.assertEqual(script.count("\\gdesc"), 16)
        self.assertIn("SELECT NULL ~ '[';", script)

    def exercise_main(self, *, values=None, metadata=None, operators=None, errors=None):
        row = self.null_case()
        concrete = {"sql": "SELECT private_value ~ private_pattern FROM never_execute_source;"}
        runtime, label = checker.runtime_cases()[0], checker.label_cases()[-1]
        values = transcript("exact_types", 1, [None, "boolean"]) if values is None else values
        metadata = "v|boolean\n" * 2 + "?column?|text\n" * 2 if metadata is None else metadata
        operators = "\n".join(f"{index}|t" for index in range(12)) + "\n" if operators is None else operators
        errors = transcript("pattern_error", 1, ["2201B"]) if errors is None else errors
        results = [subprocess.CompletedProcess(["psql"], 0, text, "") for text in
                   (values, metadata, operators, errors, "16.15\n")]
        with patch.object(checker, "load_cases", return_value=([row], [concrete])), \
                patch.object(checker, "runtime_cases", return_value=[runtime]), \
                patch.object(checker, "label_cases", return_value=[label]), \
                patch.object(checker, "validity") as validity, \
                patch.object(checker, "replay", side_effect=lambda profile, sql: {"sql": sql}) as replay, \
                patch.object(checker, "reject_sqlite") as excluded, \
                patch.object(checker, "boundaries", return_value=0), \
                patch.object(checker, "connection", return_value=nullcontext(["psql"])), \
                patch.object(checker, "run", side_effect=results) as run, \
                patch("sys.argv", ["check_pattern_matching_cli.py", "--dsn", "unused"]), \
                redirect_stdout(io.StringIO()):
            checker.main()
            return run.call_args_list, validity.call_args_list, replay.call_args_list, excluded.call_args_list

    def test_pipeline_executes_only_authored_queries_with_bounded_fail_fast_commands(self):
        calls, validity, replays, excluded = self.exercise_main()
        self.assertEqual(len(calls), 5)
        for call in calls[:4]:
            self.assertIn("ON_ERROR_STOP=1", call.args[0])
            self.assertEqual(call.kwargs["timeout"], 120)
            self.assertNotIn("never_execute_source", call.kwargs["input"])
        self.assertEqual(len(validity), 3)
        self.assertEqual(len(excluded), 1)
        self.assertEqual([call.args[0] for call in replays if "never_execute_source" in call.args[1]],
                         ["identity", "postgres"])

    def test_pipeline_rejects_missing_renamed_reordered_or_wrong_type_descriptors(self):
        for metadata in ("", "v|boolean\n" * 2 + "?column?|text\n",
                         "v|boolean\n" * 2 + "?column?|boolean\n" * 2,
                         "wrong|boolean\n" * 2 + "?column?|text\n" * 2,
                         "?column?|text\n" * 2 + "v|boolean\n" * 2):
            with self.subTest(metadata=metadata), self.assertRaises(AssertionError):
                self.exercise_main(metadata=metadata)

    def test_pipeline_rejects_false_missing_duplicate_and_reordered_native_overloads(self):
        expected = [f"{index}|t" for index in range(12)]
        for lines in ([], expected[:-1], ["0|f"] + expected[1:], expected + expected[:1],
                      [expected[1], expected[0]] + expected[2:]):
            with self.subTest(lines=lines), self.assertRaises(AssertionError):
                self.exercise_main(operators="\n".join(lines) + "\n")

    def test_pipeline_rejects_missing_values_false_for_null_or_wrong_oid(self):
        for values in ("", transcript("exact_types", 1, ["false", "boolean"]),
                       transcript("exact_types", 1, [None, "text"])):
            with self.subTest(values=values), self.assertRaises(AssertionError):
                self.exercise_main(values=values)

    def test_pipeline_rejects_success_timeout_and_the_wrong_runtime_error(self):
        for state in ("unexpected-success", "00000", "57014", "22025", "22023"):
            with self.subTest(state=state), self.assertRaises(AssertionError):
                self.exercise_main(errors=transcript("pattern_error", 1, [state]))
        with self.assertRaises(AssertionError):
            self.exercise_main(errors="")

    def test_result_arity_extra_rows_extra_cases_and_duplicate_markers_fail(self):
        expected = {"case": (2, [[None, "boolean"]])}
        for actual in ({}, {**expected, "extra": expected["case"]}, {"case": (1, [[None]])},
                       {"case": (2, [[None, "boolean"], [None, "boolean"]])}):
            with self.subTest(actual=actual), self.assertRaises(AssertionError):
                checker.validate_results(actual, expected)
        text = transcript("exact_types", 1, [None, "boolean"])
        with self.assertRaisesRegex(ValueError, "Duplicate case marker"):
            checker.parse_results(text + text)

    def test_boundaries_distinguish_invalid_unsupported_syntax_and_coarse_checked_rejection(self):
        good = subprocess.CompletedProcess([], 1, json.dumps({
            "status": "invalid", "diagnostic": {"code": "input.parse"}}), "")
        with patch.object(checker, "assert_report") as reports, \
                patch.object(checker, "invoke", return_value=good) as invoke:
            self.assertEqual(checker.boundaries(), 41)
        self.assertEqual(sum(call.args[1] == "invalid" for call in reports.call_args_list), 30)
        self.assertEqual(sum(call.args[1] == "unsupported" for call in reports.call_args_list), 2)
        self.assertEqual(sum(call.args[1:] == ("rejected", "checked") for call in reports.call_args_list), 1)
        self.assertEqual(len(invoke.call_args_list), 6)
        for code, status, diagnostic in ((0, "rendered", "input.parse"),
                                         (1, "invalid", "coverage.regex"),
                                         (3, "unsupported", "input.parse")):
            result = subprocess.CompletedProcess([], code, json.dumps({
                "status": status, "diagnostic": {"code": diagnostic}}), "")
            with self.subTest(status=status), patch.object(checker, "assert_report"), \
                    patch.object(checker, "invoke", return_value=result), self.assertRaises(AssertionError):
                checker.boundaries()


if __name__ == "__main__":
    unittest.main()
