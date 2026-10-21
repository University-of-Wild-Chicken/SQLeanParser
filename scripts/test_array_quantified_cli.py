"""Evidence-integrity regressions for quantified-array native observations."""
from contextlib import nullcontext, redirect_stdout
from copy import deepcopy
import io
import itertools
import json
from pathlib import Path
import subprocess
import tempfile
import unittest
from unittest.mock import patch

import check_array_quantified_cli as checker
from check_postgresql_cli import NULL


def comparison_signatures():
    """Independent expected scalar inventory, with bpchar's native identity."""
    groups = [
        ("smallint", "integer", "bigint"),
        ("real", "double precision"),
        ("date", "timestamp", "timestamptz"),
    ]
    pairs = set().union(*(set(itertools.product(group, repeat=2)) for group in groups))
    pairs.update((name, name) for name in (
        "numeric", "text", "bpchar", "boolean", "time", "timetz", "interval", "uuid", "jsonb", "bytea"))
    return {(operator, left, right) for operator in ("=", "<>", "<", "<=", ">", ">=")
            for left, right in pairs}


def canonical_type(name):
    aliases = {
        "int2": "smallint", "int4": "integer", "int8": "bigint",
        "float4": "real", "float8": "double precision", "bool": "boolean",
        # Unquoted SQL CHAR resolves to bpchar; the internal one-byte type is
        # spelled with embedded identifier quotes: '"char"'::regtype.
        "char": "bpchar",
        "timestamp without time zone": "timestamp", "timestamp with time zone": "timestamptz",
        "time without time zone": "time", "time with time zone": "timetz",
    }
    return aliases.get(name, name)


def transcript(category, index, values):
    """Authored COPY records distinguish SQL NULL from quoted text."""
    def field(value):
        return NULL if value is None else '"' + value.replace('"', '""') + '"'
    output = []
    for form in ("source", "postgres"):
        output += [
            checker.marker(category, index, True, form),
            '"value","type"' if len(values) == 2 else '"error"',
            ",".join(map(field, values)),
        ]
    return "\n".join(output) + "\n"


class ArrayQuantifiedCliTests(unittest.TestCase):
    def fixture_directory(self, rows=None, concrete=None, signatures=None):
        directory = tempfile.TemporaryDirectory()
        self.addCleanup(directory.cleanup)
        root = Path(directory.name)
        if rows is not None:
            (root / "synthetic.json").write_text(json.dumps(rows))
        if concrete is not None:
            (root / "concrete.jsonl").write_text("".join(json.dumps(row) + "\n" for row in concrete))
        if signatures is not None:
            (root / "operator_signatures.json").write_text(json.dumps(signatures))
        return root

    def test_operator_inventory_is_exactly_all_six_names_for_32_scalar_pairs(self):
        rows = json.loads((checker.FIXTURES / "operator_signatures.json").read_text())
        observed = {(row["operator"], canonical_type(row["left"]), canonical_type(row["right"]))
                    for row in rows}
        self.assertEqual(len(rows), 192)
        self.assertEqual(observed, comparison_signatures())
        self.assertNotIn(("=", "json", "json"), observed)
        self.assertNotIn(("=", '"char"', '"char"'), observed)

    def test_operator_probe_checks_namespace_inputs_boolean_strictness_and_scalar_result(self):
        script, expected = checker.operator_script()
        self.assertEqual(len(expected), 192)
        self.assertEqual(expected, [f"{i}|t" for i in range(192)])
        for clause in (
                "o.oprnamespace='pg_catalog'::regnamespace",
                "o.oprleft=", "o.oprright=", "o.oprresult='boolean'::regtype",
                "p.prorettype='boolean'::regtype", "p.proisstrict", "NOT p.proretset",
                "p.pronargs=2", "p.prokind='f'"):
            self.assertEqual(script.count(clause), 192, clause)
        self.assertTrue("'bpchar'::regtype" in script or "'char'::regtype" in script)
        self.assertNotIn("'\"char\"'::regtype", script)
        self.assertNotIn("ANY(", script)  # Probe catalog signatures, never infer them from truth values.

    def test_operator_probe_rejects_missing_duplicate_and_missing_operator_name(self):
        rows = json.loads((checker.FIXTURES / "operator_signatures.json").read_text())
        bad = [rows[:-1], rows + rows[:1], rows[:-1] + rows[:1]]
        for altered in bad:
            with self.subTest(size=len(altered)), \
                    patch.object(checker, "FIXTURES", self.fixture_directory(signatures=altered)), \
                    self.assertRaises(AssertionError):
                checker.operator_script()

    def test_fifty_source_and_synthetic_populations_are_distinct_with_nullable_bool_results(self):
        rows, concrete = checker.load_cases()
        self.assertEqual(len(rows), 50)
        self.assertEqual(len(concrete), 50)
        self.assertEqual({row["expected_value"] for row in rows}, {"true", "false", None})
        self.assertTrue(all(row["postgres_type"] == "boolean" for row in rows))
        self.assertTrue(all(row["postgres_display_type"] == "boolean" for row in rows))
        for quantifier in ("ANY", "SOME", "ALL"):
            self.assertTrue(any(quantifier + "(" in row["sql"].replace(" ", "") for row in rows))

    def test_loader_rejects_missing_duplicate_wrong_output_and_missing_bindings(self):
        rows, concrete = checker.load_cases()
        bad = [(rows[:-1], concrete), (rows, concrete[:-1])]
        duplicate = deepcopy(rows)
        duplicate[1]["sql"] = duplicate[0]["sql"]
        bad.append((duplicate, concrete))
        duplicate = deepcopy(rows)
        duplicate[1]["id"] = duplicate[0]["id"]
        bad.append((duplicate, concrete))
        for field, value in (("type", "integer"), ("nullable", False), ("name", "different")):
            changed = deepcopy(rows)
            changed[0]["output_columns"][0][field] = value
            bad.append((changed, concrete))
        changed = deepcopy(rows)
        bound = next(row for row in changed if row["parameter_values"])
        bound["parameter_values"].append("unbound extra argument")
        bad.append((changed, concrete))
        for altered, source in bad:
            with self.subTest(size=len(altered)), \
                    patch.object(checker, "FIXTURES", self.fixture_directory(altered, source)), \
                    self.assertRaises(AssertionError):
                checker.load_cases()

    @staticmethod
    def null_case():
        return {
            "sql": "SELECT $1 = ANY($2) AS v;", "sqlite_sql": "SELECT ?1 = ANY(?2) AS v;",
            "parameter_types": "integer,integer[]?", "parameter_values": [1, None],
            "output_columns": [{"name": "v", "type": "bool", "nullable": True}],
            "expected_value": None, "postgres_type": "boolean", "postgres_display_type": "boolean",
        }

    @staticmethod
    def empty_case():
        return {
            "sql": "SELECT NULL::INTEGER = ANY(ARRAY[]::INTEGER[]) AS v;",
            "parameter_types": "", "parameter_values": [],
            "output_columns": [{"name": "v", "type": "bool", "nullable": True}],
            "expected_value": "false", "postgres_type": "boolean", "postgres_display_type": "boolean",
        }

    def test_binding_types_and_values_are_not_substituted_into_boolean_select(self):
        row = self.null_case()
        script, expected = checker.database_script([row], [row["sql"]])
        self.assertIn("PREPARE exact_type_parameters (integer,integer[])", script)
        self.assertIn("SELECT $1 = ANY($2) AS v", script)
        self.assertIn("EXECUTE exact_type_parameters (1, NULL)", script)
        self.assertTrue(all(value == (2, [[None, "boolean"]]) for value in expected.values()))
        description, metadata = checker.describe_script([row], [row["sql"]])
        self.assertIn("PREPARE array_description (integer,integer[]) AS SELECT $1 = ANY($2) AS v;", description)
        self.assertIn("EXECUTE array_description(1, NULL)", description)
        self.assertNotIn("RETURNS TABLE", description)
        self.assertEqual(metadata, ["v|boolean", "v|boolean"])
        with patch("check_array_types_cli.assert_report") as report:
            checker.validity(row)
        self.assertEqual(report.call_args.args[0],
                         ["--assurance", "contract", "--param-types", "integer,integer[]?", row["sql"]])
        self.assertEqual(report.call_args.args[3], (("v", "bool", True),))

    def test_anonymous_operands_remain_left_to_right_with_repeated_numbered_slots(self):
        row = self.null_case()
        row.update(sql="SELECT ? <> SOME(ARRAY[?,?]) AS v;",
                   parameter_types="integer,integer,integer", parameter_values=[1, 2, 3])
        script, _ = checker.describe_script([row], [row["sql"]])
        self.assertIn("SELECT $1 <> SOME(ARRAY[$2,$3]) AS v;", script)
        self.assertIn("EXECUTE array_description(1, 2, 3)", script)
        row["sql"] = "SELECT $2 <> SOME(ARRAY[$1,$2,$3]) AS v;"
        script, _ = checker.describe_script([row], [row["sql"]])
        self.assertIn("SELECT $2 <> SOME(ARRAY[$1,$2,$3]) AS v;", script)

    def test_real_null_transcript_cannot_be_confused_with_false_or_text_null(self):
        null_result = checker.parse_results(transcript("exact_types", 1, [None, "boolean"]))
        _, expected = checker.database_script([self.null_case()], [self.null_case()["sql"]])
        self.assertEqual(checker.validate_results(null_result, expected), 2)
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

    def test_missing_canonical_native_evidence_cannot_be_silently_zipped(self):
        for function, rows in ((checker.database_script, [self.null_case()]),
                               (checker.describe_script, [self.null_case()]),
                               (checker.error_script, checker.runtime_cases())):
            with self.subTest(function=function.__name__), self.assertRaises(AssertionError):
                function(rows, [])

    def test_runtime_boundaries_preserve_exact_states_and_detect_unexpected_success(self):
        rows = checker.runtime_cases()
        self.assertEqual([row["sqlstate"] for row in rows], ["22P02", "22P02", "22012", "2202E", "22023"])
        script, expected = checker.error_script(rows, [row["sql"] for row in rows])
        self.assertEqual(len(expected), 10)
        self.assertEqual(script.count("RETURN ''unexpected-success''"), 10)
        self.assertEqual(script.count("RETURN SQLSTATE"), 10)
        self.assertIn("PREPARE pagination_parameters (TEXT)", script)
        self.assertIn("SELECT 1 = ANY(CAST($1 AS INTEGER[])) AS v;", script)
        for index, row in enumerate(rows, 1):
            for form in ("source", "postgres"):
                self.assertEqual(expected[checker.marker("quantified_error", index, True, form)],
                                 (1, [[row["sqlstate"]]]))

    def exercise_main(self, *, values=None, metadata=None, operators=None, errors=None):
        rows = [self.null_case(), self.empty_case()]
        concrete = {"sql": "SELECT secret FROM never_execute_concrete;"}
        runtime, label = checker.runtime_cases()[0], checker.label_cases()[0]
        values = (transcript("exact_types", 1, [None, "boolean"]) +
                  transcript("exact_types", 2, ["false", "boolean"]) if values is None else values)
        metadata = ("v|boolean\n" * 4 + "?column?|boolean\n" * 2 if metadata is None else metadata)
        operators = ("\n".join(f"{i}|t" for i in range(192)) + "\n" if operators is None else operators)
        errors = transcript("quantified_error", 1, ["22P02"]) if errors is None else errors
        results = [subprocess.CompletedProcess(["psql"], 0, stdout, "") for stdout in
                   (values, metadata, operators, errors, "16.15\n")]
        with patch.object(checker, "load_cases", return_value=(rows, [concrete])), \
                patch.object(checker, "runtime_cases", return_value=[runtime]), \
                patch.object(checker, "label_cases", return_value=[label]), \
                patch.object(checker, "validity") as validity, \
                patch.object(checker, "replay", side_effect=lambda mode, sql: {"sql": sql}) as replay, \
                patch.object(checker, "reject_sqlite"), \
                patch.object(checker, "boundaries", return_value=0), \
                patch.object(checker, "connection", return_value=nullcontext(["psql"])), \
                patch.object(checker, "run", side_effect=results) as run, \
                patch("sys.argv", ["check_array_quantified_cli.py", "--dsn", "unused"]), \
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
        self.assertEqual(len(validity), 4)
        self.assertEqual(sum("never_execute_concrete" in call.args[1] for call in replays), 2)

    def test_pipeline_rejects_missing_renamed_or_nonboolean_descriptors(self):
        for metadata in ("", "v|boolean\n" * 4 + "?column?|boolean\n",
                         "v|boolean\n" * 4 + "wrong|boolean\n" * 2,
                         "v|integer\n" * 4 + "?column?|boolean\n" * 2):
            with self.subTest(metadata=metadata), self.assertRaises(AssertionError):
                self.exercise_main(metadata=metadata)

    def test_pipeline_rejects_missing_false_duplicated_or_reordered_operator_observations(self):
        expected = [f"{i}|t" for i in range(192)]
        bad = [[], expected[:-1], ["0|f"] + expected[1:], expected + expected[:1],
               [expected[1], expected[0]] + expected[2:]]
        for lines in bad:
            with self.subTest(lines=lines[:2]), self.assertRaises(AssertionError):
                self.exercise_main(operators="\n".join(lines) + "\n")

    def test_pipeline_rejects_wrong_null_results_and_missing_copy_evidence(self):
        for values in ("", transcript("exact_types", 1, ["false", "boolean"]) +
                       transcript("exact_types", 2, ["false", "boolean"]),
                       transcript("exact_types", 1, [None, "boolean"])):
            with self.subTest(values=values), self.assertRaises(AssertionError):
                self.exercise_main(values=values)

    def test_pipeline_rejects_success_and_wrong_errors_for_expected_failures(self):
        for state in ("unexpected-success", "00000", "57014", "2202E"):
            with self.subTest(state=state), self.assertRaises(AssertionError):
                self.exercise_main(errors=transcript("quantified_error", 1, [state]))
        with self.assertRaises(AssertionError):
            self.exercise_main(errors="")

    def test_copy_parser_rejects_duplicate_markers_and_wrong_row_arity(self):
        output = transcript("exact_types", 1, [None, "boolean"])
        with self.assertRaisesRegex(ValueError, "Duplicate case marker"):
            checker.parse_results(output + output)
        key = checker.marker("exact_types", 1, True, "source")
        with self.assertRaisesRegex(ValueError, "Wrong result arity"):
            checker.parse_results(key + '\n"value","type"\n"false"\n')

    def test_query_rhs_uses_query_operator_types_and_cast_rhs_uses_array_types(self):
        report={"diagnostic":{"code":"quantified_subquery_signature"}}
        with patch.object(checker,"assert_report",return_value=report) as reports, \
                patch.object(checker,"invoke") as invoke:
            self.assertEqual(checker.boundaries(),15)
        self.assertFalse(invoke.called)
        self.assertEqual(sum(call.args[1]=="invalid" for call in reports.call_args_list),13)
        self.assertEqual(sum(call.args[1]=="unsupported" for call in reports.call_args_list),0)
        scalar_sql="SELECT 1 = ANY(CAST((SELECT ARRAY[1]) AS INTEGER[]))"
        scalar_calls=[call for call in reports.call_args_list if call.args[0][-1]==scalar_sql]
        self.assertEqual(len(scalar_calls),1)
        self.assertEqual(scalar_calls[0].args[1:],("valid","contract",(("?column?","bool",True),)))
        self.assertEqual(reports.call_args_list[-1].args[1:3],("rejected","checked"))

    def test_query_rhs_rejects_missing_or_wrong_operator_diagnostic(self):
        for report in ({"diagnostic":{"code":"input.parse"}},
                       {"diagnostic":{"code":"operator_signature"}},
                       {"diagnostic":{"code":"resource.depth"}}):
            with self.subTest(report=report), patch.object(checker,"assert_report",return_value=report), \
                    self.assertRaises(AssertionError):
                checker.boundaries()


if __name__ == "__main__":
    unittest.main()
