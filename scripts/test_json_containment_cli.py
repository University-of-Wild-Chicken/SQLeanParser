"""Protocol regressions for containment certificates and finite native evidence."""
from contextlib import nullcontext, redirect_stdout
from copy import deepcopy
import io
import json
from pathlib import Path
import subprocess
import tempfile
import unittest
from unittest.mock import patch

import check_json_containment_cli as checker
from check_postgresql_cli import NULL


def transcript(category, values):
    def field(value):
        return NULL if value is None else '"' + value.replace('"', '""') + '"'
    lines = []
    for form in ("source", "postgres"):
        lines += [checker.marker(category, 1, True, form),
                  '"value","type"' if len(values) == 2 else '"observation"',
                  ",".join(map(field, values))]
    return "\n".join(lines) + "\n"


class JsonContainmentCliTests(unittest.TestCase):
    def fixture_directory(self, rows=None, source=None, signatures=None):
        temporary = tempfile.TemporaryDirectory()
        self.addCleanup(temporary.cleanup)
        directory = Path(temporary.name)
        if rows is not None:
            (directory / "synthetic.json").write_text(json.dumps(rows))
        if source is not None:
            (directory / "concrete.jsonl").write_text("".join(json.dumps(row) + "\n" for row in source))
        if signatures is not None:
            (directory / "operator_signatures.json").write_text(json.dumps(signatures))
        return directory

    @staticmethod
    def case():
        return {
            "id": "containment", "source_kind": "synthetic",
            "sql": "SELECT $2 @> $1 AS v;", "parameter_types": "jsonb,jsonb",
            "parameter_values": ['{"a":1}', '{"a":1,"b":2}'],
            "output_columns": [{"name": "v", "type": "bool", "nullable": False}],
            "postgres_type": "boolean", "postgres_display_type": "boolean",
            "expected_value": "true", "sqlite_input": "SELECT ?2 @> ?1 AS v;",
            "sqlite_supported": False,
        }

    def test_populations_keep_both_directions_and_null_vs_json_null_distinct(self):
        rows, source = checker.load_cases()
        self.assertEqual((len(rows), len(source)), (50, 50))
        self.assertEqual(sum("@>" in row["sql"] for row in rows), 25)
        self.assertEqual(sum("<@" in row["sql"] for row in rows), 25)
        self.assertEqual([row["observed_syntax"]["source_free"] for row in source],
                         [True] * 42 + [False] * 8)
        for direction in ("contains", "contained"):
            cases = {row["shape"]: row for row in rows if f"-{direction}-" in row["id"]}
            self.assertEqual(len(cases), 25)
            self.assertEqual(cases["json-null"]["expected_value"], "true")
            self.assertFalse(cases["json-null"]["output_columns"][0]["nullable"])
            self.assertEqual(cases["json-null-not-false"]["expected_value"], "false")
            for shape in ("sql-null", "nullable-binding"):
                self.assertIsNone(cases[shape]["expected_value"])
                self.assertTrue(cases[shape]["output_columns"][0]["nullable"])
            self.assertEqual(cases["nested-extraction"]["expected_value"], "true")
            self.assertTrue(cases["nested-extraction"]["output_columns"][0]["nullable"])
            self.assertFalse(cases["coalesce"]["output_columns"][0]["nullable"])

    def test_loader_rejects_counts_duplicates_metadata_bindings_and_forged_scope(self):
        original, source = checker.load_cases()
        for mutation in ("missing", "source_missing", "duplicate_id", "duplicate_sql", "source_duplicate",
                         "name", "type", "nullable", "arity", "native_type", "display_type",
                         "value", "null_nonnull", "source_kind", "sqlite", "extra_binding",
                         "missing_binding", "binding_order", "source_scope_count", "source_scope_bool"):
            rows, concrete = deepcopy(original), deepcopy(source)
            if mutation == "missing":
                rows.pop()
            elif mutation == "source_missing":
                concrete.pop()
            elif mutation.startswith("duplicate_"):
                key = mutation.removeprefix("duplicate_")
                rows[1][key] = rows[0][key]
            elif mutation == "source_duplicate":
                concrete[1]["sql"] = concrete[0]["sql"]
            elif mutation in ("name", "type", "nullable"):
                rows[0]["output_columns"][0][mutation] = {
                    "name": "wrong", "type": "jsonb", "nullable": 0,
                }[mutation]
            elif mutation == "arity":
                rows[0]["output_columns"].append(rows[0]["output_columns"][0])
            elif mutation == "native_type":
                rows[0]["postgres_type"] = "bool"
            elif mutation == "display_type":
                rows[0]["postgres_display_type"] = "jsonb"
            elif mutation == "value":
                rows[0]["expected_value"] = True
            elif mutation == "null_nonnull":
                rows[0]["expected_value"] = None
            elif mutation == "source_kind":
                rows[0]["source_kind"] = "engine-regression"
            elif mutation == "sqlite":
                rows[0]["sqlite_supported"] = True
            elif mutation.startswith("source_scope"):
                concrete[0]["observed_syntax"]["source_free"] = (
                    False if mutation == "source_scope_count" else 1)
            else:
                row = next(row for row in rows if row["shape"] == "reordered")
                if mutation == "extra_binding":
                    row["parameter_values"].append("unused")
                elif mutation == "missing_binding":
                    row["parameter_values"].pop()
                else:
                    row["sqlite_input"] = "SELECT ?1 @> ?2 AS v;"
            with self.subTest(mutation=mutation), \
                    patch.object(checker, "FIXTURES", self.fixture_directory(rows, concrete)), \
                    self.assertRaises(AssertionError):
                checker.load_cases()

    def test_two_catalog_signatures_require_exact_jsonb_boolean_strict_functions(self):
        script, expected = checker.operator_script()
        self.assertEqual(expected, ["0|t", "1|t"])
        rows = json.loads((checker.FIXTURES / "operator_signatures.json").read_text())
        self.assertEqual({tuple(row[key] for key in ("operator", "left", "right", "output", "function"))
                          for row in rows}, {
            ("@>", "jsonb", "jsonb", "boolean", "jsonb_contains"),
            ("<@", "jsonb", "jsonb", "boolean", "jsonb_contained"),
        })
        for line, row in zip(script.splitlines(), rows):
            for clause in ("o.oprnamespace='pg_catalog'::regnamespace",
                           f"o.oprname='{row['operator']}'", "o.oprleft='jsonb'::regtype",
                           "o.oprright='jsonb'::regtype", "o.oprresult='boolean'::regtype",
                           "p.prorettype='boolean'::regtype", f"p.proname='{row['function']}'",
                           "p.pronamespace='pg_catalog'::regnamespace",
                           "p.proargtypes[0]='jsonb'::regtype", "p.proargtypes[1]='jsonb'::regtype",
                           "p.proisstrict", "NOT p.proretset", "p.pronargs=2", "p.prokind='f'"):
                self.assertIn(clause, line)

    def test_catalog_inventory_cannot_omit_duplicate_or_replace_signatures(self):
        original = json.loads((checker.FIXTURES / "operator_signatures.json").read_text())
        bad = [original[:-1], original + original[:1], original[:-1] + original[:1]]
        for key, value in (("operator", "?"), ("left", "json"), ("right", "text"),
                           ("output", "jsonb"), ("function", "arraycontains")):
            rows = deepcopy(original)
            rows[0][key] = value
            bad.append(rows)
        for rows in bad:
            with self.subTest(rows=rows), \
                    patch.object(checker, "FIXTURES", self.fixture_directory(signatures=rows)), \
                    self.assertRaises(AssertionError):
                checker.operator_script()

    def test_native_value_checks_keep_true_false_sql_null_and_native_oid_separate(self):
        row = self.case()
        script, expected = checker.database_script([row], [row["sql"]])
        self.assertEqual(checker.validate_results(checker.parse_results(
            transcript("exact_types", ["true", "boolean"])), expected), 2)
        for values in (["false", "boolean"], [None, "boolean"], ["null", "boolean"],
                       ["true", "jsonb"], ["true", "text"], ["t", "boolean"]):
            with self.subTest(values=values), self.assertRaises(AssertionError):
                checker.validate_results(checker.parse_results(transcript("exact_types", values)), expected)
        self.assertIn("v::text, pg_typeof(v)::text", script)
        self.assertIn("SET LOCAL statement_timeout = '5s'", script)
        self.assertIn("SET LOCAL standard_conforming_strings = on", script)
        self.assertTrue(script.endswith("ROLLBACK;"))

    def test_reordered_repeated_and_anonymous_bindings_preserve_values_and_identity(self):
        row = self.case()
        script, descriptors = checker.describe_script([row], [row["sql"]])
        self.assertEqual(script.count("SELECT $2 @> $1 AS v;"), 2)
        self.assertIn("PREPARE array_description (jsonb,jsonb)", script)
        self.assertIn("""EXECUTE array_description('{"a":1}', '{"a":1,"b":2}')""", script)
        self.assertEqual(descriptors, ["v|boolean"] * 2)
        rows, _ = checker.load_cases()
        anonymous = [row for row in rows if row["shape"] == "anonymous"]
        self.assertEqual(anonymous[0]["parameter_values"], list(reversed(anonymous[1]["parameter_values"])))
        for case in anonymous:
            script, _ = checker.database_script([case], [case["sql"]])
            self.assertIn("CAST($1 AS JSONB)", script)
            self.assertIn("CAST($2 AS JSONB)", script)
            self.assertNotIn("CAST(? AS JSONB)", script)
        repeated = next(row for row in rows if row["shape"] == "repeated")
        script, _ = checker.describe_script([repeated], [repeated["sql"]])
        self.assertEqual(script.count("$1"), 4)
        self.assertIn("PREPARE array_description (jsonb)", script)
        nullable = next(row for row in rows if row["shape"] == "nullable-binding")
        script, _ = checker.describe_script([nullable], [nullable["sql"]])
        self.assertIn("EXECUTE array_description(NULL)", script)
        self.assertNotIn("(jsonb?)", script)
        with patch("check_array_types_cli.assert_report") as report:
            checker.validity(nullable)
        self.assertEqual(report.call_args.args[3], (("v", "bool", True),))

    def test_runtime_conversion_errors_are_statics_nonnull_but_not_success(self):
        cases = checker.runtime_cases()
        self.assertEqual([row["sqlstate"] for row in cases], ["22P02", "22P02", "22P05", "22P05"])
        self.assertTrue(all(row["output_columns"][0]["nullable"] is False for row in cases))
        script, expected = checker.error_script(cases, [row["sql"] for row in cases])
        self.assertEqual(len(expected), 8)
        self.assertEqual(script.count("RETURN ''unexpected-success''"), 8)
        self.assertEqual(script.count("RETURN SQLSTATE"), 8)
        self.assertIn("SET LOCAL statement_timeout = '5s'", script)
        self.assertEqual(script.count("PREPARE pagination_parameters (TEXT)"), 8)
        for index, row in enumerate(cases, 1):
            for form in ("source", "postgres"):
                self.assertEqual(expected[checker.marker("containment_error", index, True, form)],
                                 (1, [[row["sqlstate"]]]))

    def test_missing_canonical_queries_cannot_be_silently_truncated(self):
        row = self.case()
        for function in (checker.database_script, checker.describe_script):
            with self.subTest(function=function.__name__), self.assertRaises(AssertionError):
                function([row], [])
        with self.assertRaises(AssertionError):
            checker.error_script(checker.runtime_cases(), [])

    def test_sqlite_exclusion_requires_matching_status_exit_and_feature(self):
        row = self.case()
        for code, status, diagnostic in ((1, "invalid", "input.parse"),
                                         (3, "unsupported", "coverage.sqlite.containment")):
            result = subprocess.CompletedProcess([], code, json.dumps({
                "status": status, "diagnostic": {"code": diagnostic}}), "")
            with patch.object(checker, "invoke", return_value=result) as invoke:
                checker.reject_sqlite(row)
            self.assertEqual(invoke.call_args.kwargs["stdin"], row["sqlite_input"])
        for code, status, diagnostic in ((0, "rendered", "coverage.sqlite.containment"),
                                         (3, "invalid", "input.parse"),
                                         (1, "unsupported", "coverage.sqlite.containment"),
                                         (3, "unsupported", "input.parse"),
                                         (3, "unsupported", "coverage.sqlite.type"),
                                         (3, "unsupported", "resource.depth")):
            result = subprocess.CompletedProcess([], code, json.dumps({
                "status": status, "diagnostic": {"code": diagnostic}}), "")
            with self.subTest(status=status, diagnostic=diagnostic), \
                    patch.object(checker, "invoke", return_value=result), self.assertRaises(AssertionError):
                checker.reject_sqlite(row)

    def test_labels_keep_nullable_boolean_and_precedence_text_results_distinct(self):
        labels = checker.label_cases()
        self.assertEqual(len(labels), 6)
        script, expected = checker.describe_script(labels, [row["sql"] for row in labels])
        self.assertEqual(expected, ["?column?|" + type_ for type_ in
                                    ["boolean"] * 4 + ["text", "boolean"] for _ in range(2)])
        self.assertEqual([row["output_columns"][0]["nullable"] for row in labels],
                         [False, False, True, True, False, False])
        self.assertEqual(script.count("\\gdesc"), 12)
        self.assertNotIn("RETURNS TABLE", script)

    def exercise_main(self, *, values=None, errors=None, metadata=None, operators=None):
        row = self.case()
        source = [
            {"sql": "SELECT '{}'::JSONB @> '{}' /* never_execute_literal_source */;",
             "observed_syntax": {"source_free": True}},
            {"sql": "SELECT COUNT(*) FROM never_execute_table_source WHERE j @> '{}';",
             "observed_syntax": {"source_free": False}},
        ]
        runtime, label = checker.runtime_cases()[0], checker.label_cases()[0]
        values = transcript("exact_types", ["true", "boolean"]) if values is None else values
        errors = transcript("containment_error", ["22P02"]) if errors is None else errors
        metadata = "v|boolean\n" * 2 + "?column?|boolean\n" * 2 if metadata is None else metadata
        operators = "0|t\n1|t\n" if operators is None else operators
        results = [subprocess.CompletedProcess(["psql"], 0, text, "") for text in
                   (values, errors, metadata, operators, "16.15\n")]
        with patch.object(checker, "load_cases", return_value=([row], source)), \
                patch.object(checker, "runtime_cases", return_value=[runtime]), \
                patch.object(checker, "label_cases", return_value=[label]), \
                patch.object(checker, "validity") as validity, \
                patch.object(checker, "assert_report") as certificates, \
                patch.object(checker, "replay", side_effect=lambda profile, sql: {"sql": sql}) as replay, \
                patch.object(checker, "reject_sqlite") as excluded, \
                patch.object(checker, "boundaries", return_value=0), \
                patch.object(checker, "connection", return_value=nullcontext(["psql"])), \
                patch.object(checker, "run", side_effect=results) as run, \
                patch("sys.argv", ["check_json_containment_cli.py", "--dsn", "unused"]), \
                redirect_stdout(io.StringIO()):
            checker.main()
            return (run.call_args_list, validity.call_args_list, replay.call_args_list,
                    excluded.call_args_list, certificates.call_args_list)

    def test_pipeline_executes_only_authored_sql_and_certifies_fixed_literal_sources(self):
        calls, validity, replays, excluded, certificates = self.exercise_main()
        self.assertEqual(len(calls), 5)
        for call in calls[:4]:
            self.assertIn("ON_ERROR_STOP=1", call.args[0])
            self.assertEqual(call.kwargs["timeout"], 120)
            self.assertNotIn("never_execute_", call.kwargs["input"])
        self.assertEqual(len(validity), 3)
        self.assertEqual(len(excluded), 1)
        self.assertEqual([(call.args[0], "table_source" in call.args[1]) for call in replays
                          if "never_execute_" in call.args[1]],
                         [("identity", False), ("postgres", False), ("identity", True), ("postgres", True)])
        self.assertEqual(len(certificates), 1)
        self.assertEqual(certificates[0].args, (
            ["--assurance", "contract", "SELECT '{}'::JSONB @> '{}' /* never_execute_literal_source */;"],
            "valid", "contract", (("?column?", "bool", False),)))

    def test_pipeline_rejects_false_null_wrong_oid_missing_and_duplicate_values(self):
        good = transcript("exact_types", ["true", "boolean"])
        for values in ("", good + good, transcript("exact_types", ["false", "boolean"]),
                       transcript("exact_types", [None, "boolean"]),
                       transcript("exact_types", ["true", "jsonb"])):
            with self.subTest(values=values), self.assertRaises((AssertionError, ValueError)):
                self.exercise_main(values=values)

    def test_pipeline_rejects_missing_renamed_wrong_type_or_reordered_descriptors(self):
        for metadata in ("", "v|boolean\n" * 2 + "?column?|boolean\n",
                         "v|jsonb\n" * 2 + "?column?|boolean\n" * 2,
                         "v|boolean\n" * 2 + "renamed|boolean\n" * 2,
                         "?column?|boolean\n" * 2 + "v|boolean\n" * 2):
            with self.subTest(metadata=metadata), self.assertRaises(AssertionError):
                self.exercise_main(metadata=metadata)

    def test_pipeline_rejects_false_missing_duplicate_or_reordered_catalog_evidence(self):
        for operators in ("", "0|t\n", "0|f\n1|t\n", "0|t\n1|t\n0|t\n", "1|t\n0|t\n"):
            with self.subTest(operators=operators), self.assertRaises(AssertionError):
                self.exercise_main(operators=operators)

    def test_pipeline_rejects_unexpected_success_timeout_and_wrong_conversion_error(self):
        for state in ("unexpected-success", "00000", "57014", "22P05", "22003"):
            with self.subTest(state=state), self.assertRaises(AssertionError):
                self.exercise_main(errors=transcript("containment_error", [state]))
        with self.assertRaises(AssertionError):
            self.exercise_main(errors="")

    def test_result_arity_extra_rows_extra_cases_and_duplicate_markers_fail(self):
        expected = {"case": (2, [["true", "boolean"]])}
        for actual in ({}, {**expected, "extra": expected["case"]},
                       {"case": (1, [["true"]])}, {"case": (2, [["true", "boolean"]] * 2)}):
            with self.subTest(actual=actual), self.assertRaises(AssertionError):
                checker.validate_results(actual, expected)
        text = transcript("exact_types", ["true", "boolean"])
        with self.assertRaisesRegex(ValueError, "Duplicate case marker"):
            checker.parse_results(text + text)

    def test_boundaries_separate_invalid_unsupported_syntax_and_checked_rejection(self):
        good = subprocess.CompletedProcess([], 1, json.dumps({
            "status": "invalid", "diagnostic": {"code": "input.parse"}}), "")
        with patch.object(checker, "assert_report") as reports, \
                patch.object(checker, "invoke", return_value=good) as invoke:
            self.assertEqual(checker.boundaries(), 26)
        self.assertEqual(sum(call.args[1] == "invalid" for call in reports.call_args_list), 12)
        self.assertEqual(sum(call.args[1] == "unsupported" for call in reports.call_args_list), 7)
        self.assertEqual(sum(call.args[1:] == ("rejected", "checked") for call in reports.call_args_list), 1)
        self.assertEqual(len(invoke.call_args_list), 6)
        for code, status, diagnostic in ((0, "rendered", "input.parse"),
                                         (1, "invalid", "coverage.json"),
                                         (3, "unsupported", "input.parse")):
            result = subprocess.CompletedProcess([], code, json.dumps({
                "status": status, "diagnostic": {"code": diagnostic}}), "")
            with self.subTest(status=status), patch.object(checker, "assert_report"), \
                    patch.object(checker, "invoke", return_value=result), self.assertRaises(AssertionError):
                checker.boundaries()


if __name__ == "__main__":
    unittest.main()
