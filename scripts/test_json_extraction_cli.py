"""Evidence-integrity tests for JSON extraction values, SQL NULLs and signatures."""
from contextlib import nullcontext, redirect_stdout
from copy import deepcopy
import io
import json
from pathlib import Path
import subprocess
import tempfile
import unittest
from unittest.mock import patch

import check_json_extraction_cli as checker
from check_postgresql_cli import NULL


def transcript(category, index, values):
    def field(value):
        return NULL if value is None else '"' + value.replace('"', '""') + '"'
    lines = []
    for form in ("source", "postgres"):
        lines += [checker.marker(category, index, True, form),
                  '"value","type"' if len(values) == 2 else '"observation"',
                  ",".join(map(field, values))]
    return "\n".join(lines) + "\n"


class JsonExtractionCliTests(unittest.TestCase):
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
    def json_null_case():
        return {
            "id": "json-null", "source_kind": "synthetic",
            "sql": "SELECT $1 -> $2 AS v;", "parameter_types": "jsonb,text",
            "parameter_values": ['{"a":null}', "a"],
            "output_columns": [{"name": "v", "type": "jsonb", "nullable": True}],
            "postgres_type": "jsonb", "postgres_display_type": "jsonb",
            "expected_value": "null", "expected_sql_null": False,
            "sqlite_input": "SELECT ?1 -> ?2 AS v;", "sqlite_supported": False,
        }

    def test_populations_keep_json_null_sql_null_and_json_format_distinct(self):
        rows, source = checker.load_cases()
        self.assertEqual((len(rows), len(source)), (50, 50))
        self.assertEqual({row["postgres_type"] for row in rows}, {"json", "jsonb", "text"})
        self.assertTrue(all(row["output_columns"][0]["nullable"] is True for row in rows))
        for base in ("json", "jsonb"):
            cases = {row["shape"]: row for row in rows if f"-{base}-" in row["id"]}
            self.assertEqual(cases["json-null"]["expected_value"], "null")
            self.assertFalse(cases["json-null"]["expected_sql_null"])
            for shape in ("json-null-as-text", "sql-null-subject", "missing-key", "null-path-member"):
                self.assertIsNone(cases[shape]["expected_value"])
                self.assertTrue(cases[shape]["expected_sql_null"])
            self.assertEqual(cases["empty-path"]["expected_value"],
                             '{"a":1}' if base == "json" else '{"a": 1}')
            self.assertEqual(cases["generic-precedence"]["expected_value"], "xy")

    def test_loader_rejects_missing_duplicate_type_nullability_and_null_oracle_drift(self):
        original, source = checker.load_cases()
        for mutation in ("missing", "source_missing", "duplicate_id", "duplicate_sql", "name",
                         "type", "nullable", "arity", "native_type", "display_type",
                         "sql_null_type", "sql_null_mismatch", "nonstr_value", "source_kind",
                         "sqlite", "extra_binding", "missing_binding", "binding_order"):
            rows, concrete = deepcopy(original), deepcopy(source)
            if mutation == "missing":
                rows.pop()
            elif mutation == "source_missing":
                concrete.pop()
            elif mutation.startswith("duplicate_"):
                key = mutation.removeprefix("duplicate_")
                rows[1][key] = rows[0][key]
            elif mutation in ("name", "type", "nullable"):
                rows[0]["output_columns"][0][mutation] = {
                    "name": "wrong", "type": "integer", "nullable": False,
                }[mutation]
            elif mutation == "arity":
                rows[0]["output_columns"].append(rows[0]["output_columns"][0])
            elif mutation == "native_type":
                rows[0]["postgres_type"] = "text"
            elif mutation == "display_type":
                rows[0]["postgres_display_type"] = "jsonb"
            elif mutation == "sql_null_type":
                rows[0]["expected_sql_null"] = 0
            elif mutation == "sql_null_mismatch":
                rows[0]["expected_sql_null"] = True
            elif mutation == "nonstr_value":
                rows[0]["expected_value"] = 1
            elif mutation == "source_kind":
                rows[0]["source_kind"] = "engine-regression"
            elif mutation == "sqlite":
                rows[0]["sqlite_supported"] = True
            else:
                row = next(row for row in rows if row["shape"] == "reordered-repeat")
                if mutation == "extra_binding":
                    row["parameter_values"].append("unused")
                elif mutation == "missing_binding":
                    row["parameter_values"].pop()
                else:
                    row["sqlite_input"] = "SELECT ?1 -> ?2 ->> ?2 AS v;"
            with self.subTest(mutation=mutation), \
                    patch.object(checker, "FIXTURES", self.fixture_directory(rows, concrete)), \
                    self.assertRaises(AssertionError):
                checker.load_cases()

    def test_twelve_catalog_overloads_preserve_array_argument_and_variadic_metadata(self):
        script, expected = checker.operator_script()
        self.assertEqual(expected, [f"{index}|t" for index in range(12)])
        rows = json.loads((checker.FIXTURES / "operator_signatures.json").read_text())
        self.assertEqual(len(rows), 12)
        wanted = set()
        for base in ("json", "jsonb"):
            for operator, suffix in (("->", ""), ("->>", "_text")):
                for right, procedure in (("text", "_object_field"), ("integer", "_array_element")):
                    wanted.add((operator, base, right, "text" if suffix else base, base + procedure + suffix))
            for operator, suffix in (("#>", ""), ("#>>", "_text")):
                wanted.add((operator, base, "text[]", "text" if suffix else base,
                            base + "_extract_path" + suffix))
        self.assertEqual({tuple(row[key] for key in ("operator", "left", "right", "output", "function"))
                          for row in rows}, wanted)
        for line, row in zip(script.splitlines(), rows):
            for clause in (
                    "o.oprnamespace='pg_catalog'::regnamespace", f"o.oprname='{row['operator']}'",
                    f"o.oprleft='{row['left']}'::regtype", f"o.oprright='{row['right']}'::regtype",
                    f"o.oprresult='{row['output']}'::regtype", f"p.prorettype='{row['output']}'::regtype",
                    f"p.proname='{row['function']}'", "p.pronamespace='pg_catalog'::regnamespace",
                    f"p.proargtypes[0]='{row['left']}'::regtype", f"p.proargtypes[1]='{row['right']}'::regtype",
                    "p.proisstrict", "NOT p.proretset", "p.pronargs=2", "p.prokind='f'"):
                self.assertIn(clause, line)
            self.assertIn("p.provariadic=" + ("'text'::regtype" if row["right"] == "text[]" else "0"), line)

    def test_catalog_inventory_cannot_omit_duplicate_or_replace_key_and_result_types(self):
        original = json.loads((checker.FIXTURES / "operator_signatures.json").read_text())
        bad = [original[:-1], original + original[:1], original[:-1] + original[:1]]
        for key, value in (("operator", "@>"), ("left", "text"), ("right", "bigint"),
                           ("output", "boolean"), ("function", "json_extract_path")):
            rows = deepcopy(original)
            rows[0][key] = value
            bad.append(rows)
        for rows in bad:
            with self.subTest(rows=rows[0]), \
                    patch.object(checker, "FIXTURES", self.fixture_directory(signatures=rows)), \
                    self.assertRaises(AssertionError):
                checker.operator_script()

    def test_sql_null_probe_is_independent_of_json_text_serialization(self):
        row = self.json_null_case()
        script, expected = checker.null_script([row], [row["sql"]])
        self.assertIn("SELECT (v IS NULL)::TEXT FROM (SELECT $1 -> $2 AS v)", script)
        self.assertEqual(script.count("PREPARE json_null_parameters (jsonb,text)"), 2)
        self.assertIn("SET LOCAL statement_timeout = '5s'", script)
        self.assertIn("SET LOCAL standard_conforming_strings = on", script)
        self.assertEqual(script.count("DEALLOCATE json_null_parameters;"), 2)
        self.assertNotIn("v::text", script.lower())
        self.assertTrue(all(value == (1, [["false"]]) for value in expected.values()))
        actual = checker.parse_results(transcript("json_null", 1, ["false"]))
        self.assertEqual(checker.validate_results(actual, expected), 2)
        for wrong in ("true", "null", None):
            actual = checker.parse_results(transcript("json_null", 1, [wrong]))
            with self.subTest(wrong=wrong), self.assertRaises(AssertionError):
                checker.validate_results(actual, expected)

    def test_json_null_sql_null_and_json_string_null_have_different_value_evidence(self):
        row = self.json_null_case()
        _, expected = checker.database_script([row], [row["sql"]])
        self.assertEqual(checker.validate_results(
            checker.parse_results(transcript("exact_types", 1, ["null", "jsonb"])), expected), 2)
        for value, type_ in ((None, "jsonb"), ('"null"', "jsonb"), ("null", "text"), ("null", "json")):
            actual = checker.parse_results(transcript("exact_types", 1, [value, type_]))
            with self.subTest(value=value, type=type_), self.assertRaises(AssertionError):
                checker.validate_results(actual, expected)

    def test_json_and_jsonb_whitespace_are_not_normalized_away_by_comparison(self):
        expected = {"case": (2, [['{"a":1}', "json"]])}
        for value, type_ in (('{"a": 1}', "json"), ('{"a":1}', "jsonb"), ("1", "text")):
            with self.subTest(value=value, type=type_), self.assertRaises(AssertionError):
                checker.validate_results({"case": (2, [[value, type_]])}, expected)

    def test_prepared_reordered_repeated_and_anonymous_bindings_keep_identity(self):
        row = dict(self.json_null_case(), sql="SELECT $2 -> $1 ->> $1 AS v;",
                   parameter_types="text,jsonb", parameter_values=["a", '{"a":{"a":"x"}}'],
                   postgres_display_type="text")
        script, descriptors = checker.describe_script([row], [row["sql"]])
        self.assertEqual(script.count("SELECT $2 -> $1 ->> $1 AS v;"), 2)
        self.assertIn("PREPARE array_description (text,jsonb)", script)
        self.assertIn("""EXECUTE array_description('a', '{"a":{"a":"x"}}')""", script)
        self.assertEqual(descriptors, ["v|text"] * 2)
        row.update(sql="SELECT ? #>> ? AS v;", parameter_types="jsonb?,text[]",
                   parameter_values=[None, "{a}"], expected_sql_null=True)
        script, expected = checker.null_script([row], [row["sql"]])
        self.assertIn("SELECT $1 #>> $2 AS v", script)
        self.assertIn("PREPARE json_null_parameters (jsonb,text[])", script)
        self.assertIn("EXECUTE json_null_parameters (NULL, ''''{a}'''')", script)
        self.assertTrue(all(value == (1, [["true"]]) for value in expected.values()))
        with patch("check_array_types_cli.assert_report") as report:
            checker.validity(self.json_null_case())
        self.assertEqual(report.call_args.args[3], (("v", "jsonb", True),))

    def test_runtime_conversion_errors_do_not_become_static_nonnull_or_success(self):
        rows = checker.runtime_cases()
        self.assertEqual([row["sqlstate"] for row in rows], ["22P02", "22P02", "22P05", "22P02", "22003"])
        self.assertTrue(all(row["output_columns"][0]["nullable"] is True for row in rows))
        script, expected = checker.error_script(rows, [row["sql"] for row in rows])
        self.assertIn("SET LOCAL statement_timeout = '5s'", script)
        self.assertEqual(script.count("RETURN ''unexpected-success''"), 10)
        self.assertEqual(script.count("RETURN SQLSTATE"), 10)
        for index, row in enumerate(rows, 1):
            for form in ("source", "postgres"):
                self.assertEqual(expected[checker.marker("json_extraction_error", index, True, form)],
                                 (1, [[row["sqlstate"]]]))

    def test_missing_renderings_cannot_be_silently_truncated(self):
        row = self.json_null_case()
        for function in (checker.database_script, checker.null_script, checker.describe_script):
            with self.subTest(function=function.__name__), self.assertRaises(AssertionError):
                function([row], [])
        with self.assertRaises(AssertionError):
            checker.error_script(checker.runtime_cases(), [])

    def test_sqlite_rejections_require_exact_status_exit_and_feature_evidence(self):
        row = self.json_null_case()
        for code, status, diagnostic in ((1, "invalid", "input.parse"),
                                         (3, "unsupported", "coverage.sqlite.json-extraction")):
            result = subprocess.CompletedProcess([], code, json.dumps({
                "status": status, "diagnostic": {"code": diagnostic}}), "")
            with patch.object(checker, "invoke", return_value=result) as invoke:
                checker.reject_sqlite(row)
            self.assertEqual(invoke.call_args.kwargs["stdin"], row["sqlite_input"])
        for code, status, diagnostic in ((0, "rendered", "coverage.sqlite.json-extraction"),
                                         (3, "invalid", "input.parse"),
                                         (1, "unsupported", "coverage.sqlite.json-extraction"),
                                         (3, "unsupported", "input.parse"),
                                         (3, "unsupported", "coverage.sqlite.type"),
                                         (3, "unsupported", "resource.depth")):
            result = subprocess.CompletedProcess([], code, json.dumps({
                "status": status, "diagnostic": {"code": diagnostic}}), "")
            with self.subTest(status=status, diagnostic=diagnostic), \
                    patch.object(checker, "invoke", return_value=result), self.assertRaises(AssertionError):
                checker.reject_sqlite(row)

    def test_unaliased_operators_and_explicit_cast_have_exact_result_labels(self):
        labels = checker.label_cases()
        self.assertEqual(len(labels), 9)
        script, descriptors = checker.describe_script(labels, [row["sql"] for row in labels])
        self.assertEqual(descriptors, [f"{name}|{type_}" for name, type_ in (
            ("?column?", "json"), ("?column?", "jsonb"), ("?column?", "text"), ("?column?", "text"),
            ("?column?", "json"), ("?column?", "jsonb"), ("?column?", "text"), ("?column?", "text"),
            ("text", "text")) for _ in range(2)])
        self.assertEqual(script.count("\\gdesc"), 18)
        self.assertNotIn("RETURNS TABLE", script)

    def exercise_main(self, *, values=None, nulls=None, errors=None, metadata=None, operators=None):
        row = self.json_null_case()
        source = {"sql": "SELECT secret_json -> 'a' FROM never_execute_source;"}
        runtime, label = checker.runtime_cases()[0], checker.label_cases()[-1]
        values = transcript("exact_types", 1, ["null", "jsonb"]) if values is None else values
        nulls = transcript("json_null", 1, ["false"]) if nulls is None else nulls
        errors = transcript("json_extraction_error", 1, ["22P02"]) if errors is None else errors
        metadata = "v|jsonb\n" * 2 + "text|text\n" * 2 if metadata is None else metadata
        operators = "\n".join(f"{index}|t" for index in range(12)) + "\n" if operators is None else operators
        results = [subprocess.CompletedProcess(["psql"], 0, text, "") for text in
                   (values, nulls, errors, metadata, operators, "16.15\n")]
        with patch.object(checker, "load_cases", return_value=([row], [source])), \
                patch.object(checker, "runtime_cases", return_value=[runtime]), \
                patch.object(checker, "label_cases", return_value=[label]), \
                patch.object(checker, "validity") as validity, \
                patch.object(checker, "assert_report") as source_certificates, \
                patch.object(checker, "replay", side_effect=lambda profile, sql: {"sql": sql}) as replay, \
                patch.object(checker, "reject_sqlite") as excluded, \
                patch.object(checker, "boundaries", return_value=0), \
                patch.object(checker, "connection", return_value=nullcontext(["psql"])), \
                patch.object(checker, "run", side_effect=results) as run, \
                patch("sys.argv", ["check_json_extraction_cli.py", "--dsn", "unused"]), \
                redirect_stdout(io.StringIO()):
            checker.main()
            return (run.call_args_list, validity.call_args_list, replay.call_args_list,
                    excluded.call_args_list, source_certificates.call_args_list)

    def test_pipeline_executes_only_authored_sql_with_bounded_fail_fast_commands(self):
        calls, validity, replays, excluded, source_certificates = self.exercise_main()
        self.assertEqual(len(calls), 6)
        for call in calls[:5]:
            self.assertIn("ON_ERROR_STOP=1", call.args[0])
            self.assertEqual(call.kwargs["timeout"], 120)
            self.assertNotIn("never_execute_source", call.kwargs["input"])
        self.assertEqual(len(validity), 3)
        self.assertEqual(len(excluded), 1)
        self.assertEqual([call.args[0] for call in replays if "never_execute_source" in call.args[1]],
                         ["identity", "postgres"])
        self.assertEqual(len(source_certificates), 1)
        self.assertEqual(source_certificates[0].args, (
            ["--assurance", "contract", "SELECT secret_json -> 'a' FROM never_execute_source;"],
            "valid", "contract"))

    def test_pipeline_rejects_absent_or_wrong_separate_sql_null_observations(self):
        for nulls in ("", transcript("json_null", 1, ["true"]),
                      transcript("json_null", 1, [None]), transcript("json_null", 1, ["null"])):
            with self.subTest(nulls=nulls), self.assertRaises(AssertionError):
                self.exercise_main(nulls=nulls)

    def test_pipeline_rejects_wrong_values_oids_or_missing_value_evidence(self):
        for values in ("", transcript("exact_types", 1, [None, "jsonb"]),
                       transcript("exact_types", 1, ["null", "text"]),
                       transcript("exact_types", 1, ['"null"', "jsonb"])):
            with self.subTest(values=values), self.assertRaises(AssertionError):
                self.exercise_main(values=values)

    def test_pipeline_rejects_missing_renamed_or_wrong_type_descriptors(self):
        for metadata in ("", "v|jsonb\n" * 2 + "text|text\n",
                         "v|json\n" * 2 + "text|text\n" * 2,
                         "v|jsonb\n" * 2 + "?column?|text\n" * 2,
                         "text|text\n" * 2 + "v|jsonb\n" * 2):
            with self.subTest(metadata=metadata), self.assertRaises(AssertionError):
                self.exercise_main(metadata=metadata)

    def test_pipeline_rejects_false_missing_duplicate_or_reordered_catalog_rows(self):
        expected = [f"{index}|t" for index in range(12)]
        for lines in ([], expected[:-1], ["0|f"] + expected[1:], expected + expected[:1],
                      [expected[1], expected[0]] + expected[2:]):
            with self.subTest(lines=lines), self.assertRaises(AssertionError):
                self.exercise_main(operators="\n".join(lines) + "\n")

    def test_pipeline_rejects_unexpected_success_timeout_and_wrong_runtime_error(self):
        for state in ("unexpected-success", "00000", "57014", "22003", "22P05"):
            with self.subTest(state=state), self.assertRaises(AssertionError):
                self.exercise_main(errors=transcript("json_extraction_error", 1, [state]))
        with self.assertRaises(AssertionError):
            self.exercise_main(errors="")

    def test_result_arity_extra_rows_extra_cases_and_duplicate_markers_fail(self):
        expected = {"case": (1, [["false"]])}
        for actual in ({}, {**expected, "extra": expected["case"]},
                       {"case": (2, [["false", "jsonb"]])}, {"case": (1, [["false"], ["false"]])}):
            with self.subTest(actual=actual), self.assertRaises(AssertionError):
                checker.validate_results(actual, expected)
        text = transcript("json_null", 1, ["false"])
        with self.assertRaisesRegex(ValueError, "Duplicate case marker"):
            checker.parse_results(text + text)

    def test_boundaries_keep_invalid_unsupported_syntax_and_checked_rejection_distinct(self):
        good = subprocess.CompletedProcess([], 1, json.dumps({
            "status": "invalid", "diagnostic": {"code": "input.parse"}}), "")
        with patch.object(checker, "assert_report") as reports, \
                patch.object(checker, "invoke", return_value=good) as invoke:
            self.assertEqual(checker.boundaries(), 26)
        self.assertEqual(sum(call.args[1] == "invalid" for call in reports.call_args_list), 15)
        self.assertEqual(sum(call.args[1] == "unsupported" for call in reports.call_args_list), 3)
        self.assertEqual(sum(call.args[1] == "valid" for call in reports.call_args_list), 1)
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
