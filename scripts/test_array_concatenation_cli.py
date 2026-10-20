"""Evidence-integrity tests for polymorphic, non-strict array concatenation."""
from contextlib import nullcontext, redirect_stdout
from copy import deepcopy
import io
import json
from pathlib import Path
import subprocess
import tempfile
import unittest
from unittest.mock import patch

import check_array_concatenation_cli as checker
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


class ArrayConcatenationCliTests(unittest.TestCase):
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
    def null_array_case():
        return {
            "id": "nullable-concat", "source_kind": "synthetic",
            "sql": "SELECT $2 || $1 || $2 AS v;", "parameter_types": "integer[]?,integer[]?",
            "parameter_values": [None, None],
            "output_columns": [{"name": "v", "type": "integer[]", "nullable": True}],
            "postgres_type": "integer[]", "postgres_display_type": "integer[]",
            "expected_value": None, "sqlite_input": "SELECT ?2 || ?1 || ?2 AS v;",
            "sqlite_supported": False,
        }

    def test_population_distinguishes_null_arrays_null_elements_and_empty_arrays(self):
        rows, source = checker.load_cases()
        self.assertEqual((len(rows), len(source)), (50, 50))
        self.assertTrue(all(row["observed_syntax"]["source_free"] is True for row in source))
        cases = {row["shape"]: row for row in rows}
        self.assertEqual(len(cases), 50)
        for shape in ("both-null-arrays", "nullable-cat-bindings"):
            self.assertIsNone(cases[shape]["expected_value"])
            self.assertTrue(cases[shape]["output_columns"][0]["nullable"])
        for shape in ("append-null-to-null", "prepend-null-to-null",
                      "nullable-append-bindings", "nullable-prepend-bindings"):
            self.assertEqual(cases[shape]["expected_value"], "{NULL}")
            self.assertFalse(cases[shape]["output_columns"][0]["nullable"])
        self.assertEqual(cases["nullable-case-with-empty"]["expected_value"], "{}")
        self.assertFalse(cases["nullable-case-with-empty"]["output_columns"][0]["nullable"])
        self.assertEqual(cases["jsonb-json-null-and-sql-null"]["expected_value"], '{"null",NULL,1}')

    def test_fixture_retains_bounds_typmod_erasure_and_native_bpchar_alias(self):
        cases = {row["shape"]: row for row in checker.load_cases()[0]}
        self.assertEqual(cases["lower-bounds-cat"]["expected_value"], "[0:3]={1,2,3,4}")
        self.assertEqual(cases["lower-bounds-prepend"]["expected_value"], "[0:2]={0,1,2}")
        self.assertEqual(cases["numeric-modifiers-erased"]["output_columns"][0]["type"], "numeric[]")
        self.assertEqual(cases["numeric-modifiers-erased"]["expected_value"], "{1.23,2.35}")
        self.assertEqual(cases["binding-modifier-erasure"]["expected_value"], "{1.23,2.345}")
        char = cases["char-left-common-type"]
        self.assertEqual((char["output_columns"][0]["type"], char["postgres_type"],
                          char["postgres_display_type"], char["expected_value"]),
                         ("bpchar[]", "character[]", "bpchar[]", '{"a  ",b}'))
        self.assertEqual(cases["text-left-common-type"]["expected_value"], "{a,b}")

    def test_loader_rejects_missing_duplicates_metadata_bindings_and_source_scope(self):
        original, source = checker.load_cases()
        for mutation in ("missing", "source_missing", "duplicate_id", "duplicate_sql", "source_duplicate",
                         "name", "type", "nullable", "arity", "native_type", "display_type",
                         "bpchar_display", "value", "null_nonnull", "source_kind", "sqlite",
                         "extra_binding", "missing_binding", "binding_order", "scope_false", "scope_int"):
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
                    "name": "wrong", "type": "integer", "nullable": 0,
                }[mutation]
            elif mutation == "arity":
                rows[0]["output_columns"].append(rows[0]["output_columns"][0])
            elif mutation == "native_type":
                rows[0]["postgres_type"] = "integer"
            elif mutation == "display_type":
                rows[0]["postgres_display_type"] = "smallint[]"
            elif mutation == "bpchar_display":
                row = next(row for row in rows if row["shape"] == "char-left-common-type")
                row["postgres_display_type"] = "character[]"
            elif mutation == "value":
                rows[0]["expected_value"] = [1, 2, 3, 4]
            elif mutation == "null_nonnull":
                rows[0]["expected_value"] = None
            elif mutation == "source_kind":
                rows[0]["source_kind"] = "engine-regression"
            elif mutation == "sqlite":
                rows[0]["sqlite_supported"] = True
            elif mutation.startswith("scope_"):
                concrete[0]["observed_syntax"]["source_free"] = False if mutation == "scope_false" else 1
            else:
                row = next(row for row in rows if row["shape"] == "reordered-repeated-slots")
                if mutation == "extra_binding":
                    row["parameter_values"].append("{9}")
                elif mutation == "missing_binding":
                    row["parameter_values"].pop()
                else:
                    row["sqlite_input"] = "SELECT ?1 || ?2 || ?1 AS v;"
            with self.subTest(mutation=mutation), \
                    patch.object(checker, "FIXTURES", self.fixture_directory(rows, concrete)), \
                    self.assertRaises(AssertionError):
                checker.load_cases()

    def test_three_generic_catalog_families_are_exact_and_explicitly_nonstrict(self):
        script, expected = checker.operator_script()
        self.assertEqual(expected, ["0|t", "1|t", "2|t"])
        rows = json.loads((checker.FIXTURES / "operator_signatures.json").read_text())
        self.assertEqual({tuple(row[key] for key in ("operator", "left", "right", "output", "function"))
                          for row in rows}, {
            ("||", "anycompatiblearray", "anycompatiblearray", "anycompatiblearray", "array_cat"),
            ("||", "anycompatiblearray", "anycompatible", "anycompatiblearray", "array_append"),
            ("||", "anycompatible", "anycompatiblearray", "anycompatiblearray", "array_prepend"),
        })
        for line, row in zip(script.splitlines(), rows):
            for clause in ("o.oprnamespace='pg_catalog'::regnamespace", "o.oprname='||'",
                           f"o.oprleft='{row['left']}'::regtype", f"o.oprright='{row['right']}'::regtype",
                           "o.oprresult='anycompatiblearray'::regtype",
                           "p.prorettype='anycompatiblearray'::regtype", f"p.proname='{row['function']}'",
                           "p.pronamespace='pg_catalog'::regnamespace",
                           f"p.proargtypes[0]='{row['left']}'::regtype",
                           f"p.proargtypes[1]='{row['right']}'::regtype",
                           "NOT p.proisstrict", "NOT p.proretset", "p.pronargs=2", "p.prokind='f'"):
                self.assertIn(clause, line)
            self.assertNotIn("AND p.proisstrict", line)

    def test_catalog_inventory_cannot_omit_duplicate_or_substitute_legacy_polymorphism(self):
        original = json.loads((checker.FIXTURES / "operator_signatures.json").read_text())
        bad = [original[:-1], original + original[:1], original[:-1] + original[:1]]
        for key, value in (("operator", "+"), ("left", "anyarray"), ("right", "anyelement"),
                           ("output", "text"), ("function", "textcat")):
            rows = deepcopy(original)
            rows[0][key] = value
            bad.append(rows)
        for rows in bad:
            with self.subTest(rows=rows), \
                    patch.object(checker, "FIXTURES", self.fixture_directory(signatures=rows)), \
                    self.assertRaises(AssertionError):
                checker.operator_script()

    def test_outer_null_probe_does_not_inspect_array_elements_or_stringify_values(self):
        row = self.null_array_case()
        script, expected = checker.null_script([row], [row["sql"]])
        self.assertEqual(checker.validate_results(checker.parse_results(
            transcript("array_concat_null", ["true"])), expected), 2)
        self.assertIn("SELECT (v IS NULL)::TEXT FROM (SELECT $2 || $1 || $2 AS v)", script)
        self.assertNotIn("v::text", script.lower())
        self.assertNotIn("unnest", script.lower())
        self.assertEqual(script.count("PREPARE array_null_parameters (integer[],integer[])"), 2)
        self.assertIn("EXECUTE array_null_parameters (NULL, NULL)", script)
        self.assertEqual(script.count("DEALLOCATE array_null_parameters"), 2)
        self.assertIn("SET LOCAL statement_timeout = '5s'", script)
        self.assertTrue(script.endswith("ROLLBACK;"))
        row.update(expected_value="{NULL}", parameter_types="integer[]?,integer?",
                   sql="SELECT $1 || $2 AS v;")
        _, expected = checker.null_script([row], [row["sql"]])
        self.assertTrue(all(value == (1, [["false"]]) for value in expected.values()))

    def test_native_values_retain_outer_null_element_null_bounds_and_oid(self):
        row = self.null_array_case()
        _, expected = checker.database_script([row], [row["sql"]])
        self.assertEqual(checker.validate_results(checker.parse_results(
            transcript("exact_types", [None, "integer[]"])), expected), 2)
        for values in (["{NULL}", "integer[]"], ["{}", "integer[]"], ["NULL", "integer[]"],
                       [None, "bigint[]"], [None, "text"]):
            with self.subTest(values=values), self.assertRaises(AssertionError):
                checker.validate_results(checker.parse_results(transcript("exact_types", values)), expected)
        row.update(expected_value="[0:1]={1,2}")
        _, expected = checker.database_script([row], [row["sql"]])
        with self.assertRaises(AssertionError):
            checker.validate_results(checker.parse_results(
                transcript("exact_types", ["{1,2}", "integer[]"])), expected)

    def test_prepared_reordered_repeated_anonymous_and_nullable_bindings_keep_identity(self):
        rows, _ = checker.load_cases()
        row = next(row for row in rows if row["shape"] == "reordered-repeated-slots")
        script, descriptors = checker.describe_script([row], [row["sql"]])
        self.assertEqual(script.count(row["sql"]), 2)
        self.assertIn("PREPARE array_description (integer[],integer[])", script)
        self.assertIn("EXECUTE array_description('{1}', '{2}')", script)
        self.assertEqual(descriptors, ["v|integer[]"] * 2)
        anonymous = next(row for row in rows if row["shape"] == "anonymous-arrays")
        script, _ = checker.null_script([anonymous], [anonymous["sql"]])
        self.assertIn("CAST($1 AS INTEGER[]) || CAST($2 AS INTEGER[])", script)
        self.assertNotIn("CAST(? AS INTEGER[])", script)
        nullable = next(row for row in rows if row["shape"] == "nullable-append-bindings")
        script, _ = checker.describe_script([nullable], [nullable["sql"]])
        self.assertIn("PREPARE array_description (integer[],integer)", script)
        self.assertIn("EXECUTE array_description(NULL, NULL)", script)
        with patch("check_array_types_cli.assert_report") as report:
            checker.validity(nullable)
        self.assertEqual(report.call_args.args[3], (("v", "integer[]", False),))

    def test_runtime_shape_and_conversion_errors_remain_distinct_from_static_types(self):
        cases = checker.runtime_cases()
        self.assertEqual([row["sqlstate"] for row in cases],
                         ["2202E", "2202E", "22000", "22000", "2202E", "22P02", "22003"])
        self.assertTrue(all(row["output_columns"] == [
            {"name": "v", "type": "integer[]", "nullable": False}] for row in cases))
        script, expected = checker.error_script(cases, [row["sql"] for row in cases])
        self.assertEqual(len(expected), 14)
        self.assertEqual(script.count("RETURN ''unexpected-success''"), 14)
        self.assertEqual(script.count("RETURN SQLSTATE"), 14)
        self.assertIn("SET LOCAL statement_timeout = '5s'", script)
        for index, row in enumerate(cases, 1):
            for form in ("source", "postgres"):
                self.assertEqual(expected[checker.marker("array_concat_error", index, True, form)],
                                 (1, [[row["sqlstate"]]]))

    def test_missing_canonical_inputs_are_not_silently_truncated(self):
        row = self.null_array_case()
        for function in (checker.database_script, checker.null_script, checker.describe_script):
            with self.subTest(function=function.__name__), self.assertRaises(AssertionError):
                function([row], [])
        with self.assertRaises(AssertionError):
            checker.error_script(checker.runtime_cases(), [])

    def test_sqlite_exclusions_require_matching_status_exit_and_array_feature(self):
        row = self.null_array_case()
        allowed = ((1, "invalid", "input.parse"), (3, "unsupported", "coverage.sqlite.array-type"),
                   (3, "unsupported", "coverage.sqlite.array-constructor"))
        for code, status, diagnostic in allowed:
            result = subprocess.CompletedProcess([], code, json.dumps({
                "status": status, "diagnostic": {"code": diagnostic}}), "")
            with patch.object(checker, "invoke", return_value=result) as invoke:
                checker.reject_sqlite(row)
            self.assertEqual(invoke.call_args.kwargs["stdin"], row["sqlite_input"])
        for code, status, diagnostic in ((0, "rendered", "coverage.sqlite.array-type"),
                                         (3, "invalid", "input.parse"),
                                         (1, "unsupported", "coverage.sqlite.array-constructor"),
                                         (3, "unsupported", "input.parse"),
                                         (3, "unsupported", "coverage.sqlite.type"),
                                         (3, "unsupported", "resource.depth")):
            result = subprocess.CompletedProcess([], code, json.dumps({
                "status": status, "diagnostic": {"code": diagnostic}}), "")
            with self.subTest(status=status, diagnostic=diagnostic), \
                    patch.object(checker, "invoke", return_value=result), self.assertRaises(AssertionError):
                checker.reject_sqlite(row)

    def test_real_descriptors_preserve_bpchar_spelling_but_remove_concat_typmods(self):
        labels = checker.label_cases()
        self.assertEqual(len(labels), 6)
        script, descriptors = checker.describe_script(labels, [row["sql"] for row in labels])
        self.assertEqual(descriptors, ["?column?|" + type_ for type_ in
                                      ["integer[]"] * 4 + ["bpchar[]", "numeric[]"] for _ in range(2)])
        self.assertEqual([row["output_columns"][0]["nullable"] for row in labels],
                         [False, True, False, False, False, False])
        self.assertEqual(script.count("\\gdesc"), 12)
        self.assertNotIn("RETURNS TABLE", script)
        self.assertNotIn("?column?|character[]", "\n".join(descriptors))

    def exercise_main(self, *, values=None, nulls=None, errors=None, metadata=None, operators=None):
        row = self.null_array_case()
        source = {"sql": "SELECT ARRAY[1] || ARRAY[2] /* never_execute_source */;",
                  "observed_syntax": {"source_free": True}}
        runtime, label = checker.runtime_cases()[0], checker.label_cases()[4]
        values = transcript("exact_types", [None, "integer[]"]) if values is None else values
        nulls = transcript("array_concat_null", ["true"]) if nulls is None else nulls
        errors = transcript("array_concat_error", ["2202E"]) if errors is None else errors
        metadata = "v|integer[]\n" * 2 + "?column?|bpchar[]\n" * 2 if metadata is None else metadata
        operators = "0|t\n1|t\n2|t\n" if operators is None else operators
        results = [subprocess.CompletedProcess(["psql"], 0, text, "") for text in
                   (values, nulls, errors, metadata, operators, "16.15\n")]
        with patch.object(checker, "load_cases", return_value=([row], [source])), \
                patch.object(checker, "runtime_cases", return_value=[runtime]), \
                patch.object(checker, "label_cases", return_value=[label]), \
                patch.object(checker, "validity") as validity, \
                patch.object(checker, "assert_report") as certificates, \
                patch.object(checker, "replay", side_effect=lambda profile, sql: {"sql": sql}) as replay, \
                patch.object(checker, "reject_sqlite") as excluded, \
                patch.object(checker, "boundaries", return_value=0), \
                patch.object(checker, "connection", return_value=nullcontext(["psql"])), \
                patch.object(checker, "run", side_effect=results) as run, \
                patch("sys.argv", ["check_array_concatenation_cli.py", "--dsn", "unused"]), \
                redirect_stdout(io.StringIO()):
            checker.main()
            return (run.call_args_list, validity.call_args_list, replay.call_args_list,
                    excluded.call_args_list, certificates.call_args_list)

    def test_pipeline_certifies_source_population_but_executes_only_bounded_authored_sql(self):
        calls, validity, replays, excluded, certificates = self.exercise_main()
        self.assertEqual(len(calls), 6)
        for call in calls[:5]:
            self.assertIn("ON_ERROR_STOP=1", call.args[0])
            self.assertEqual(call.kwargs["timeout"], 120)
            self.assertNotIn("never_execute_source", call.kwargs["input"])
        self.assertEqual(len(validity), 3)
        self.assertEqual(len(excluded), 1)
        self.assertEqual([call.args[0] for call in replays if "never_execute_source" in call.args[1]],
                         ["identity", "postgres"])
        self.assertEqual(len(certificates), 1)
        self.assertEqual(certificates[0].args, (
            ["--assurance", "contract", "SELECT ARRAY[1] || ARRAY[2] /* never_execute_source */;"],
            "valid", "contract"))

    def test_pipeline_rejects_element_null_empty_array_wrong_oid_and_missing_values(self):
        good = transcript("exact_types", [None, "integer[]"])
        for values in ("", good + good, transcript("exact_types", ["{NULL}", "integer[]"]),
                       transcript("exact_types", ["{}", "integer[]"]),
                       transcript("exact_types", [None, "bigint[]"])):
            with self.subTest(values=values), self.assertRaises((AssertionError, ValueError)):
                self.exercise_main(values=values)

    def test_pipeline_requires_separate_outer_null_observations(self):
        for nulls in ("", transcript("array_concat_null", ["false"]),
                      transcript("array_concat_null", [None]), transcript("array_concat_null", ["NULL"])):
            with self.subTest(nulls=nulls), self.assertRaises(AssertionError):
                self.exercise_main(nulls=nulls)

    def test_pipeline_rejects_missing_renamed_wrong_alias_or_reordered_descriptors(self):
        for metadata in ("", "v|integer[]\n" * 2 + "?column?|bpchar[]\n",
                         "v|bigint[]\n" * 2 + "?column?|bpchar[]\n" * 2,
                         "v|integer[]\n" * 2 + "?column?|character[]\n" * 2,
                         "v|integer[]\n" * 2 + "renamed|bpchar[]\n" * 2,
                         "?column?|bpchar[]\n" * 2 + "v|integer[]\n" * 2):
            with self.subTest(metadata=metadata), self.assertRaises(AssertionError):
                self.exercise_main(metadata=metadata)

    def test_pipeline_rejects_false_missing_duplicate_or_reordered_catalog_evidence(self):
        for operators in ("", "0|t\n1|t\n", "0|f\n1|t\n2|t\n",
                          "0|t\n1|t\n2|t\n0|t\n", "1|t\n0|t\n2|t\n"):
            with self.subTest(operators=operators), self.assertRaises(AssertionError):
                self.exercise_main(operators=operators)

    def test_pipeline_rejects_unexpected_success_timeout_and_wrong_runtime_error(self):
        for state in ("unexpected-success", "00000", "57014", "22000", "22P02", "22003"):
            with self.subTest(state=state), self.assertRaises(AssertionError):
                self.exercise_main(errors=transcript("array_concat_error", [state]))
        with self.assertRaises(AssertionError):
            self.exercise_main(errors="")

    def test_result_arity_extra_rows_extra_cases_and_duplicate_markers_fail(self):
        expected = {"case": (1, [["true"]])}
        for actual in ({}, {**expected, "extra": expected["case"]},
                       {"case": (2, [["true", "integer[]"]])}, {"case": (1, [["true"]] * 2)}):
            with self.subTest(actual=actual), self.assertRaises(AssertionError):
                checker.validate_results(actual, expected)
        text = transcript("array_concat_null", ["true"])
        with self.assertRaisesRegex(ValueError, "Duplicate case marker"):
            checker.parse_results(text + text)

    def test_boundaries_separate_type_failures_unknowns_lexing_and_checked_tier(self):
        good = subprocess.CompletedProcess([], 1, json.dumps({
            "status": "invalid", "diagnostic": {"code": "input.parse"}}), "")
        with patch.object(checker, "assert_report") as reports, \
                patch.object(checker, "invoke", return_value=good) as invoke:
            self.assertEqual(checker.boundaries(), 15)
        self.assertEqual(sum(call.args[1] == "invalid" for call in reports.call_args_list), 5)
        self.assertEqual(sum(call.args[1] == "unsupported" for call in reports.call_args_list), 3)
        self.assertEqual(sum(call.args[1] == "valid" for call in reports.call_args_list), 3)
        self.assertEqual(sum(call.args[1:] == ("rejected", "checked") for call in reports.call_args_list), 3)
        self.assertEqual(len(invoke.call_args_list), 1)
        valid_columns = [call.args[3] for call in reports.call_args_list if call.args[1] == "valid"]
        self.assertEqual(valid_columns, [(("v", "text", False),), (("v", "text", True),),
                                         (("v", "integer[]", False),)])
        for code, status, diagnostic in ((0, "rendered", "input.parse"),
                                         (1, "invalid", "coverage.concat"),
                                         (3, "unsupported", "input.parse")):
            result = subprocess.CompletedProcess([], code, json.dumps({
                "status": status, "diagnostic": {"code": diagnostic}}), "")
            with self.subTest(status=status), patch.object(checker, "assert_report"), \
                    patch.object(checker, "invoke", return_value=result), self.assertRaises(AssertionError):
                checker.boundaries()


if __name__ == "__main__":
    unittest.main()
