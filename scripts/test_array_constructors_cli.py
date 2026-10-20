"""Offline regressions for constructor bindings and native evidence integrity."""
from collections import Counter
from contextlib import nullcontext, redirect_stdout
from copy import deepcopy
import csv
import io
import json
from pathlib import Path
import subprocess
import tempfile
import unittest
from unittest.mock import patch

import check_array_constructors_cli as checker
from generate_array_constructor_examples import cases


def csv_evidence(category, values, index=1):
    """Author a source/canonical COPY transcript, including the real markers."""
    result = io.StringIO()
    for form in ("source", "postgres"):
        result.write(checker.marker(category, index, True, form) + "\n")
        writer = csv.writer(result, quoting=csv.QUOTE_ALL, lineterminator="\n")
        writer.writerow(["value", "type"] if len(values) == 2 else ["error"])
        writer.writerow(values)
    return result.getvalue()


class ArrayConstructorsCliTests(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        cls.rows, cls.concrete = checker.load_cases()
        cls.by_shape = {row["shape"]: row for row in cls.rows}

    def fixture_directory(self, rows=None, concrete=None):
        directory = tempfile.TemporaryDirectory()
        self.addCleanup(directory.cleanup)
        path = Path(directory.name)
        (path / "synthetic.json").write_text(json.dumps(self.rows if rows is None else rows))
        (path / "concrete.jsonl").write_text("".join(
            json.dumps(row) + "\n" for row in (self.concrete if concrete is None else concrete)))
        return path

    def test_fifty_authored_examples_reproduce_with_one_output_each(self):
        self.assertEqual(self.rows, cases())
        self.assertEqual(len(self.rows), 50)
        self.assertEqual(len(self.by_shape), 50)
        self.assertEqual(len(self.concrete), 50)
        for row in self.rows:
            self.assertEqual(len(row["output_columns"]), 1)
            self.assertEqual(row["output_columns"][0]["name"], "v")
            self.assertIs(row["output_columns"][0]["nullable"], False)

    def test_loader_rejects_missing_duplicate_and_relabelled_population(self):
        bad = []
        rows = deepcopy(self.rows)
        rows[1]["sql"] = rows[0]["sql"]
        bad.append((rows, self.concrete))
        rows = deepcopy(self.rows)
        rows[1]["id"] = rows[0]["id"]
        bad.append((rows, self.concrete))
        bad.extend(((self.rows[:-1], self.concrete), (self.rows, self.concrete[:-1])))
        for rows, source in bad:
            with self.subTest(counts=(len(rows), len(source))):
                with patch.object(checker, "FIXTURES", self.fixture_directory(rows, source)):
                    with self.assertRaises(AssertionError):
                        checker.load_cases()

    def test_loader_rejects_unbound_extra_and_reordered_sqlite_parameter_slots(self):
        for alteration in ("unbound", "extra", "sqlite-order"):
            rows = deepcopy(self.rows)
            row = next(row for row in rows if row["shape"] == "numbered-order")
            if alteration == "unbound":
                row["parameter_values"] = [10]
            elif alteration == "extra":
                row["parameter_values"].append(30)
            else:
                row["sqlite_sql"] = "SELECT ARRAY[?1,?2,?1] AS v;"
            with self.subTest(alteration=alteration):
                with patch.object(checker, "FIXTURES", self.fixture_directory(rows)):
                    with self.assertRaises(AssertionError):
                        checker.load_cases()

    def test_anonymous_nested_binding_order_is_lexical_not_dimension_order(self):
        row = self.by_shape["anonymous-order"]
        self.assertEqual(checker.parameters(row["sql"], "postgres"),
                         [("anonymous", 1), ("anonymous", 2), ("anonymous", 3), ("anonymous", 4)])
        description, expected = checker.describe_script([row], [row["sql"]])
        self.assertIn("SELECT ARRAY[[$1,$2],[$3,$4]] AS v;", description)
        self.assertIn("EXECUTE array_description(1, 2, 3, 4)", description)
        self.assertEqual(expected, ["v|integer[]", "v|integer[]"])
        values, observations = checker.database_script([row], [row["sql"]])
        self.assertIn("ARRAY[[$1,$2],[$3,$4]]", values)
        self.assertNotIn("ARRAY[[1,2],[3,4]]", values)
        self.assertTrue(all(value == (2, [["{{1,2},{3,4}}", "integer[]"]])
                            for value in observations.values()))

    def test_numbered_repetition_keeps_binding_slot_order(self):
        row = self.by_shape["numbered-order"]
        self.assertEqual(checker.parameters(row["sql"], "postgres"),
                         [("numbered", 2), ("numbered", 1), ("numbered", 2)])
        description, _ = checker.describe_script([row], [row["sql"]])
        self.assertIn("ARRAY[$2,$1,$2]", description)
        self.assertIn("EXECUTE array_description(10, 20)", description)
        _, expected = checker.database_script([row], [row["sql"]])
        self.assertTrue(all(value == (2, [["{20,10,20}", "integer[]"]])
                            for value in expected.values()))

    def test_nullable_elements_do_not_make_the_constructed_array_null(self):
        row = self.by_shape["nullable-element"]
        self.assertEqual(row["parameter_values"], [None])
        self.assertEqual(row["expected_value"], "{NULL,2}")
        self.assertIs(row["output_columns"][0]["nullable"], False)
        script, expected = checker.database_script([row], [row["sql"]])
        self.assertIn("PREPARE exact_type_parameters (int)", script)
        self.assertIn("EXECUTE exact_type_parameters (NULL)", script)
        self.assertTrue(all(value == (2, [["{NULL,2}", "integer[]"]])
                            for value in expected.values()))

    def test_unknown_null_erases_common_typmod_even_after_one_explicit_cast(self):
        uncast = self.by_shape["parameter-modifier-erasure"]
        casted = self.by_shape["parameter-explicit-modifier"]
        self.assertEqual(uncast["parameter_types"], casted["parameter_types"])
        self.assertEqual(uncast["parameter_values"], casted["parameter_values"])
        self.assertEqual(uncast["expected_value"], "{1.234,NULL}")
        self.assertEqual(casted["expected_value"], "{1.23,NULL}")
        for row in (uncast, casted):
            self.assertEqual(row["postgres_display_type"], "numeric[]")
            self.assertEqual(row["output_columns"][0]["type"], "numeric[]")
        script, expected = checker.describe_script([uncast, casted], [uncast["sql"], casted["sql"]])
        self.assertEqual(expected, ["v|numeric[]"] * 4)
        self.assertIn("CAST($1 AS NUMERIC(6,2))", script)
        self.assertIn("EXECUTE array_description('1.234')", script)

    def test_equal_and_unequal_element_modifiers_have_separate_descriptors(self):
        equal = self.by_shape["equal-numeric-modifiers"]
        unequal = self.by_shape["unequal-numeric-modifiers"]
        script, expected = checker.describe_script([equal, unequal], [equal["sql"], unequal["sql"]])
        self.assertEqual(expected, ["v|numeric(6,2)[]"] * 2 + ["v|numeric[]"] * 2)
        self.assertEqual(script.count("\\gdesc"), 4)
        self.assertNotIn("RETURNS TABLE", script)

    def test_nested_empty_arrays_keep_value_and_type_evidence_separate(self):
        row = self.by_shape["empty-nested-modifier"]
        self.assertIn("[][]", row["sql"])
        self.assertEqual(row["expected_value"], "{}")
        self.assertEqual(row["postgres_type"], "numeric[]")
        self.assertEqual(row["postgres_display_type"], "numeric(6,2)[]")
        self.assertEqual(row["output_columns"][0]["type"], "numeric(6,2)[]")

    def test_json_null_sql_null_and_bytea_data_are_distinct_authored_values(self):
        self.assertEqual(self.by_shape["jsonb"]["expected_value"],
                         r'{"{\"a\": 1}","null",NULL}')
        self.assertEqual(self.by_shape["bytea"]["expected_value"],
                         r'{"\\x00",NULL,"\\x6162"}')
        self.assertEqual(self.by_shape["unknown-strings"]["expected_value"],
                         '{"a,b","NULL",quote\'d}')

    def test_all_result_descriptors_preserve_alias_and_modifier_metadata(self):
        rows = self.rows + checker.modifier_cases() + checker.label_cases()
        script, expected = checker.describe_script(rows, [row["sql"] for row in rows])
        self.assertEqual(len(expected), 120)
        self.assertEqual(script.count("\\gdesc"), 120)
        self.assertIn("v|timestamp(2) without time zone[]", expected)
        self.assertIn("v|character varying(2)[]", expected)
        self.assertEqual(expected[-8:], ["array|integer[]"] * 6 + ["coalesce|integer[]"] * 2)

    def test_unmodified_bpchar_is_not_the_char_one_declaration(self):
        rows = checker.modifier_cases()
        self.assertEqual(len(rows), 6)
        self.assertEqual([row["output_columns"][0]["type"] for row in rows],
                         ["bpchar", "bpchar[]", "bpchar[]", "bpchar[]", "char(2)[]", "bpchar"])
        self.assertEqual(rows[0]["parameter_types"], "char(3)")
        self.assertEqual(rows[0]["expected_value"], "abcd")
        self.assertEqual(rows[1]["parameter_types"], "char(3)[]")
        self.assertEqual(rows[1]["expected_value"], "{abcd,NULL}")
        script, expected = checker.describe_script(rows, [row["sql"] for row in rows])
        self.assertEqual(expected, [
            "v|bpchar", "v|bpchar", "v|bpchar[]", "v|bpchar[]",
            "v|bpchar[]", "v|bpchar[]", "v|bpchar[]", "v|bpchar[]",
            "v|character(2)[]", "v|character(2)[]", "v|bpchar", "v|bpchar",
        ])
        self.assertIn("PREPARE array_description (char(3)[]) AS SELECT $1 AS v;", script)
        self.assertNotIn("v|char[]", expected)
        self.assertNotIn("v|character(1)[]", expected)

    def test_bpchar_contract_expectation_keeps_parameter_declaration_separate(self):
        row = checker.modifier_cases()[1]
        with patch("check_array_types_cli.assert_report") as report:
            checker.validity(row)
        arguments = report.call_args.args
        self.assertEqual(arguments[0],
                         ["--assurance", "contract", "--param-types", "char(3)[]", row["sql"]])
        self.assertEqual(arguments[3], (("v", "bpchar[]", False),))

    def test_missing_canonical_value_description_or_error_cannot_be_silently_zipped(self):
        for function, rows in (
                (checker.database_script, self.rows),
                (checker.describe_script, self.rows),
                (checker.error_script, checker.runtime_cases())):
            with self.subTest(function=function.__name__), self.assertRaises(AssertionError):
                function(rows, [row["sql"] for row in rows[:-1]])

    def test_runtime_errors_require_exact_states_and_explicit_unexpected_success(self):
        rows = checker.runtime_cases()
        self.assertEqual(Counter(row["sqlstate"] for row in rows),
                         {"2202E": 3, "22P02": 1, "22012": 1, "22023": 1, "22003": 1})
        script, expected = checker.error_script(rows, [row["sql"] for row in rows])
        self.assertEqual(len(expected), 14)
        self.assertEqual(script.count("RETURN ''unexpected-success''"), 14)
        self.assertEqual(script.count("RETURN SQLSTATE"), 14)
        self.assertIn("PREPARE pagination_parameters (TEXT) AS SELECT ARRAY[$1]::INTEGER[] AS v;", script)
        self.assertIn("bad integer", script)
        for index, row in enumerate(rows, 1):
            for form in ("source", "postgres"):
                key = checker.marker("array_constructor_error", index, True, form)
                self.assertEqual(expected[key], (1, [[row["sqlstate"]]]))

    def test_missing_extra_wrong_arity_and_wrong_type_value_evidence_fail(self):
        expected = {"case": (2, [["{NULL,2}", "integer[]"]])}
        bad = [
            {}, {**expected, "extra": expected["case"]},
            {"case": (1, [["{NULL,2}"]])},
            {"case": (2, [[None, "integer[]"]])},
            {"case": (2, [["{NULL,2}", "bigint[]"]])},
            {"case": (2, [["{NULL,2}", "integer[]"], ["{NULL,2}", "integer[]"]])},
        ]
        for actual in bad:
            with self.subTest(actual=actual), self.assertRaises(AssertionError):
                checker.validate_results(actual, expected)

    def exercise_main(self, *, metadata=None, errors=None):
        """Run the real protocol plumbing with authored finite psql transcripts."""
        row = self.by_shape["integers"]
        extra = checker.modifier_cases()[1]
        concrete = {"sql": "SELECT external_table_secret FROM never_execute_concrete;"}
        runtime = checker.runtime_cases()[0]
        label = checker.label_cases()[0]
        values_output = (csv_evidence("exact_types", ["{1,2,3}", "integer[]"])
                         + csv_evidence("exact_types", ["{abcd,NULL}", "character[]"], 2))
        metadata_output = ("v|integer[]\nv|integer[]\nv|bpchar[]\nv|bpchar[]\n"
                           "array|integer[]\narray|integer[]\n"
                           if metadata is None else metadata)
        errors_output = (csv_evidence("array_constructor_error", ["2202E"])
                         if errors is None else errors)
        results = [subprocess.CompletedProcess(["psql"], 0, stdout, "") for stdout in
                   (values_output, metadata_output, errors_output, "16.15\n")]
        with patch.object(checker, "load_cases", return_value=([row], [concrete])), \
                patch.object(checker, "modifier_cases", return_value=[extra]), \
                patch.object(checker, "runtime_cases", return_value=[runtime]), \
                patch.object(checker, "label_cases", return_value=[label]), \
                patch.object(checker, "validity") as validity, \
                patch.object(checker, "replay", side_effect=lambda mode, sql: {"sql": sql}) as replay, \
                patch.object(checker, "reject_sqlite"), \
                patch.object(checker, "boundaries", return_value=0), \
                patch.object(checker, "connection", return_value=nullcontext(["psql"])), \
                patch.object(checker, "run", side_effect=results) as run, \
                patch("sys.argv", ["check_array_constructors_cli.py", "--dsn", "unused"]), \
                redirect_stdout(io.StringIO()):
            checker.main()
            return run.call_args_list, validity.call_args_list, replay.call_args_list

    def test_native_pipeline_executes_only_authored_cases_and_uses_fail_fast_psql(self):
        calls, validity, replays = self.exercise_main()
        self.assertEqual(len(calls), 4)
        for call in calls[:3]:
            self.assertIn("ON_ERROR_STOP=1", call.args[0])
            self.assertEqual(call.kwargs["timeout"], 120)
            self.assertNotIn("never_execute_concrete", call.kwargs["input"])
        self.assertEqual(len(validity), 4)  # Synthetic, modifier, runtime boundary, output label.
        self.assertEqual(sum("never_execute_concrete" in call.args[1] for call in replays), 2)

    def test_native_pipeline_rejects_missing_renamed_or_modified_descriptors(self):
        for metadata in (
                "v|integer[]\nv|integer[]\nv|bpchar[]\nv|bpchar[]\narray|integer[]\n",
                "v|integer[]\nv|integer[]\nv|char[]\nv|char[]\narray|integer[]\narray|integer[]\n",
                "v|integer[]\nv|integer[]\nv|character(1)[]\nv|character(1)[]\narray|integer[]\narray|integer[]\n",
                "v|integer[]\nv|integer[]\nv|bpchar[]\nv|bpchar[]\nwrong|integer[]\narray|integer[]\n",
                "array|integer[]\narray|integer[]\nv|bpchar[]\nv|bpchar[]\nv|integer[]\nv|integer[]\n"):
            with self.subTest(metadata=metadata), self.assertRaises(AssertionError):
                self.exercise_main(metadata=metadata)

    def test_native_pipeline_does_not_treat_success_or_other_errors_as_expected_failure(self):
        for state in ("unexpected-success", "00000", "57014", "22P02"):
            with self.subTest(state=state), self.assertRaises(AssertionError):
                self.exercise_main(errors=csv_evidence("array_constructor_error", [state]))
        with self.assertRaises(AssertionError):
            self.exercise_main(errors="")

    def test_copy_transcript_rejects_duplicate_markers_and_malformed_arity(self):
        transcript = csv_evidence("array_constructor_error", ["2202E"])
        with self.assertRaisesRegex(ValueError, "Duplicate case marker"):
            checker.parse_results(transcript + transcript)
        marker = checker.marker("exact_types", 1, True, "source")
        with self.assertRaisesRegex(ValueError, "Wrong result arity"):
            checker.parse_results(marker + '\n"value","type"\n"{1,2,3}"\n')


if __name__ == "__main__":
    unittest.main()
