"""EXTRACT evidence, exact NUMERIC observations, and source-execution boundary."""
from contextlib import nullcontext, redirect_stdout
from copy import deepcopy
import io
import json
from pathlib import Path
import subprocess
import tempfile
import unittest
from unittest.mock import patch

import check_assurance_cli as assurance
import check_extract_cli as checker
from check_postgresql_cli import NULL
from generate_extract_examples import cases


def transcript(category, values, index=1):
    def field(value):
        return NULL if value is None else '"' + value.replace('"', '""') + '"'
    lines = []
    for form in ("source", "postgres"):
        lines += [checker.marker(category, index, True, form),
                  '"value","type"' if len(values) == 2 else '"observation"',
                  ",".join(map(field, values))]
    return "\n".join(lines) + "\n"


class ExtractCliTests(unittest.TestCase):
    def fixture_directory(self, rows=None, source=None, declarations=None):
        temporary = tempfile.TemporaryDirectory()
        self.addCleanup(temporary.cleanup)
        directory = Path(temporary.name)
        if rows is not None:
            (directory / "synthetic.json").write_text(json.dumps(rows))
        if source is not None:
            (directory / "concrete.jsonl").write_text("".join(json.dumps(row) + "\n" for row in source))
        if declarations is not None:
            (directory / "function_signatures.json").write_text(json.dumps(declarations))
        return directory

    @staticmethod
    def case(shape="fractional-second"):
        return next(row for row in cases() if row["shape"] == shape)

    def test_fifty_author_oracles_and_fifty_unchanged_sources_are_closed(self):
        rows, source = checker.load_cases()
        self.assertEqual(rows, cases())
        self.assertEqual((len(rows), len(source)), (50, 50))
        self.assertTrue(all(row["source_kind"] == "engine-regression" for row in source))
        for row in source:
            self.assertEqual(row["raw_sql"], row["sql"])
            self.assertEqual(row["transformations"], [])
            self.assertIs(row["observed_syntax"]["source_free"], True)
            self.assertIsNone(row["parameter_types"])
        self.assertEqual(sum(row["expected_value"] is None for row in rows), 6)
        self.assertTrue(all(row["expected_value"] is None or isinstance(row["expected_value"], str)
                            for row in rows))

    def test_fractional_numeric_infinity_and_sql_null_are_distinct(self):
        expected = {
            "fractional-second": "56.789000", "milliseconds": "56789.000",
            "microseconds": "56789000", "negative-second": "-4.500000",
            "time-epoch": "3723.500000", "infinite-year": "Infinity",
            "infinite-day": None, "negative-infinite-second": None,
            "explicit-time-rounding": "57.000000", "case-interval": "1.250000",
        }
        for shape, value in expected.items():
            case = self.case(shape)
            self.assertEqual(case["expected_value"], value)
            _, wanted = checker.database_script([case], [case["sql"]])
            checker.validate_results(checker.parse_results(
                transcript("exact_types", [value, "numeric"])), wanted)
        case = self.case()
        _, wanted = checker.database_script([case], [case["sql"]])
        for value, type_name in (("56.789", "numeric"), ("56.79", "numeric"),
                                 ("56.789000", "double precision"), (None, "numeric"),
                                 ("Infinity", "numeric"), ("NULL", "numeric")):
            with self.subTest(value=value, type_name=type_name), self.assertRaises(AssertionError):
                checker.validate_results(checker.parse_results(
                    transcript("exact_types", [value, type_name])), wanted)

    def test_loader_rejects_missing_duplicate_metadata_and_binding_changes(self):
        original_rows, original_source = checker.load_cases()
        for mutation in ("missing", "source_missing", "duplicate_id", "duplicate_sql",
                         "source_duplicate", "name", "type", "nullable", "arity", "oid",
                         "display", "value", "null_nonnull", "kind", "sqlite", "scope",
                         "extra_binding", "missing_binding", "binding_order"):
            rows, source = deepcopy(original_rows), deepcopy(original_source)
            row = rows[0]
            if mutation == "missing":
                rows.pop()
            elif mutation == "source_missing":
                source.pop()
            elif mutation.startswith("duplicate_"):
                key = mutation.removeprefix("duplicate_")
                rows[1][key] = rows[0][key]
            elif mutation == "source_duplicate":
                source[1]["sql"] = source[0]["sql"]
            elif mutation in ("name", "type", "nullable"):
                row["output_columns"][0][mutation] = {"name": "wrong", "type": "double", "nullable": 1}[mutation]
            elif mutation == "arity":
                row["output_columns"] *= 2
            elif mutation == "oid":
                row["postgres_type"] = "double precision"
            elif mutation == "display":
                row["postgres_display_type"] = "numeric(8,2)"
            elif mutation == "value":
                row["expected_value"] = 2024
            elif mutation == "null_nonnull":
                next(row for row in rows if row["shape"] == "hour-24")["expected_value"] = None
            elif mutation == "kind":
                row["source_kind"] = "engine-regression"
            elif mutation == "sqlite":
                row["sqlite_supported"] = True
            elif mutation == "scope":
                source[0]["observed_syntax"]["source_free"] = 1
            else:
                row = next(row for row in rows if row["shape"] == "reordered")
                if mutation == "extra_binding":
                    row["parameter_values"].append("unused")
                elif mutation == "missing_binding":
                    row["parameter_values"].pop()
                else:
                    row["sqlite_input"] = row["sqlite_input"].replace("?2", "?3").replace("?1", "?2").replace("?3", "?1")
            with self.subTest(mutation=mutation), patch.object(checker, "FIXTURES",
                    self.fixture_directory(rows, source)), self.assertRaises(AssertionError):
                checker.load_cases()

    def test_parameter_order_repetition_anonymous_mapping_and_null_stay_in_execute(self):
        for shape in ("reordered", "repeated", "anonymous", "nullable-binding"):
            case = self.case(shape)
            scripts = [checker.database_script([case], [case["sql"]])[0],
                       checker.null_script([case], [case["sql"]])[0],
                       checker.describe_script([case], [case["sql"]])[0]]
            for script in scripts:
                self.assertIn("PREPARE ", script)
                self.assertNotIn("FROM CAST(? AS DATE)", script)
                self.assertNotIn("(time?)", script)
                if shape == "reordered":
                    self.assertEqual(script.count("EXTRACT(YEAR FROM $2) + EXTRACT(MONTH FROM $1)"), 2)
                    # EXECUTE appears directly in gdesc and inside two SQL
                    # string layers in the value/NULL capture functions.
                    self.assertIn("(2024-02-29, 2025-01-02)", script.replace("'", ""))
                elif shape == "repeated":
                    self.assertEqual(script.count("EXTRACT(HOUR FROM $1) + EXTRACT(MINUTE FROM $1)"), 2)
                elif shape == "anonymous":
                    self.assertEqual(script.count("EXTRACT(YEAR FROM CAST($1 AS DATE))"), 2)
                else:
                    self.assertIn("(NULL)", script)

    def test_shared_validity_requires_exact_schema_and_declarative_evidence(self):
        case = self.case()
        report = {
            "status": "valid", "assurance": "declarative",
            "profile": assurance.PROFILES["contract"], "evidence": "declarative-derivation",
            "catalogUnchanged": True, "typePrecision": "exact",
            "outputColumns": deepcopy(case["output_columns"]),
        }
        good = subprocess.CompletedProcess([], 0, json.dumps(report), "")
        with patch.object(assurance, "invoke", return_value=good) as invoke:
            checker.validity(case)
        self.assertEqual(invoke.call_args.args[0], ["--assurance", "contract", case["sql"]])
        mutations = []
        for key, value in (("status", "checked"), ("assurance", "executable"),
                           ("profile", "wrong-profile"), ("evidence", "checker-acceptance"),
                           ("catalogUnchanged", False), ("typePrecision", "family")):
            bad = deepcopy(report)
            bad[key] = value
            mutations.append(bad)
        for key in ("outputColumns", "evidence", "catalogUnchanged"):
            bad = deepcopy(report)
            del bad[key]
            mutations.append(bad)
        for key, value in (("name", "?column?"), ("type", "double"), ("nullable", True)):
            bad = deepcopy(report)
            bad["outputColumns"][0][key] = value
            mutations.append(bad)
        for bad in mutations:
            result = subprocess.CompletedProcess([], 0, json.dumps(bad), "")
            with self.subTest(report=bad), patch.object(assurance, "invoke", return_value=result), \
                    self.assertRaises(AssertionError):
                checker.validity(case)
        for code in (1, 3, 4):
            with patch.object(assurance, "invoke", return_value=subprocess.CompletedProcess(
                    [], code, json.dumps(report), "")), self.assertRaises(AssertionError):
                checker.validity(case)

    def test_json_nullability_requires_booleans_even_without_expected_columns(self):
        report = {
            "status": "valid", "assurance": "declarative",
            "profile": assurance.PROFILES["contract"], "evidence": "declarative-derivation",
            "catalogUnchanged": True, "typePrecision": "exact",
            "outputColumns": [{"name": "v", "type": "numeric", "nullable": False}],
        }
        args = ["--assurance", "contract", self.case()["sql"]]
        for nullable in (False, True):
            good = deepcopy(report)
            good["outputColumns"][0]["nullable"] = nullable
            with patch.object(assurance, "invoke", return_value=subprocess.CompletedProcess(
                    [], 0, json.dumps(good), "")):
                assurance.assert_report(args, "valid", "contract")
        bad_reports = []
        for value in (0, 1, 0.0, 1.0, "true", "false", None):
            bad = deepcopy(report)
            bad["outputColumns"][0]["nullable"] = value
            bad_reports.append(bad)
        missing = deepcopy(report)
        del missing["outputColumns"][0]["nullable"]
        bad_reports.append(missing)
        for columns in ({}, None, "columns", [None], [False]):
            bad = deepcopy(report)
            bad["outputColumns"] = columns
            bad_reports.append(bad)
        for bad in bad_reports:
            result = subprocess.CompletedProcess([], 0, json.dumps(bad), "")
            for columns in (None, (("v", "numeric", False),)):
                with self.subTest(report=bad, expected=columns), patch.object(
                        assurance, "invoke", return_value=result), self.assertRaises(AssertionError):
                    assurance.assert_report(args, "valid", "contract", columns)

    def test_catalog_requires_six_exact_strict_numeric_declarations(self):
        script, wanted = checker.function_script()
        self.assertEqual(wanted, [f"{i}|t" for i in range(6)])
        self.assertEqual(script.count("p.provolatile='s'"), 1)
        self.assertEqual(script.count("p.provolatile='i'"), 5)
        for line in script.splitlines():
            for clause in ("p.pronamespace='pg_catalog'::regnamespace", "p.proname='extract'",
                           "p.proargtypes[0]='text'::regtype", "p.prorettype='numeric'::regtype",
                           "p.pronargs=2", "p.prokind='f'", "p.proisstrict", "NOT p.proretset"):
                self.assertIn(clause, line)
            self.assertEqual("p.provolatile='s'" in line, "='timestamp with time zone'::regtype" in line)
        declarations = json.loads((checker.FIXTURES / "function_signatures.json").read_text())
        bad = [declarations[:-1], declarations + declarations[:1],
               declarations[:-1] + declarations[:1]]
        for key, value in (("name", "date_part"), ("inputs", ["text", "text"]), ("output", "float8")):
            changed = deepcopy(declarations)
            changed[0][key] = value
            bad.append(changed)
        for rows in bad:
            with self.subTest(rows=rows), patch.object(checker, "FIXTURES",
                    self.fixture_directory(declarations=rows)), self.assertRaises(AssertionError):
                checker.function_script()

    def test_six_null_shortcuts_keep_invalid_unit_and_native_null_checks(self):
        shortcuts = checker.null_shortcuts()
        self.assertEqual(len(shortcuts), 6)
        self.assertEqual(len({row["sql"] for row in shortcuts}), 6)
        self.assertTrue(all("EXTRACT('not a unit' FROM NULL::" in row["sql"] for row in shortcuts))
        self.assertTrue(all(row["expected_value"] is None for row in shortcuts))
        self.assertTrue(all(row["output_columns"][0]["nullable"] is True for row in shortcuts))
        sql, wanted = checker.null_script(shortcuts, [row["sql"] for row in shortcuts])
        self.assertEqual(len(wanted), 12)
        self.assertTrue(all(value == (1, [["true"]]) for value in wanted.values()))
        self.assertEqual(sql.count("(v IS NULL)::TEXT"), 12)
        self.assertIn("SET LOCAL statement_timeout = '5s'", sql)
        self.assertIn("SET LOCAL TIME ZONE 'UTC'", sql)
        self.assertTrue(sql.endswith("ROLLBACK;"))

    def test_runtime_units_unsupported_fields_and_conversion_have_exact_sqlstates(self):
        rows = checker.runtime_cases()
        self.assertEqual([row["sqlstate"] for row in rows],
                         ["22023", "22023", "0A000", "0A000", "0A000", "0A000", "22007", "22008", "22023"])
        self.assertTrue(all(row["parameter_types"] == "text" for row in rows))
        sql, wanted = checker.error_script(rows, [row["sql"] for row in rows])
        self.assertEqual(len(wanted), 18)
        self.assertEqual(sql.count("RETURN SQLSTATE"), 18)
        self.assertEqual(sql.count("RETURN ''unexpected-success''"), 18)
        self.assertEqual(sql.count("PREPARE pagination_parameters (TEXT)"), 18)
        self.assertIn("EXTRACT('da''y' FROM CAST($1 AS DATE))", sql)
        self.assertTrue(sql.endswith("ROLLBACK;"))

    def test_missing_canonical_entries_fail_before_zip_truncation(self):
        case = self.case()
        for function in (checker.database_script, checker.null_script, checker.describe_script):
            with self.subTest(function=function.__name__), self.assertRaises(AssertionError):
                function([case], [])
        with self.assertRaises(AssertionError):
            checker.error_script(checker.runtime_cases(), [])

    def test_sqlite_rejection_requires_exact_paired_status_diagnostic_and_exit(self):
        for code, status, diagnostic in ((1, "invalid", "input.parse"),
                                         (3, "unsupported", "coverage.sqlite.extract")):
            result = subprocess.CompletedProcess([], code, json.dumps({
                "status": status, "diagnostic": {"code": diagnostic}}), "")
            with patch.object(checker, "invoke", return_value=result) as invoke:
                checker.reject_sqlite(self.case())
            self.assertEqual(invoke.call_args.kwargs["stdin"], self.case()["sqlite_input"])
        for code, status, diagnostic in ((0, "rendered", "coverage.sqlite.extract"),
                                         (1, "unsupported", "coverage.sqlite.extract"),
                                         (3, "invalid", "input.parse"),
                                         (3, "unsupported", "coverage.sqlite.cast"),
                                         (4, "inconclusive", "resource.depth")):
            result = subprocess.CompletedProcess([], code, json.dumps({
                "status": status, "diagnostic": {"code": diagnostic}}), "")
            with self.subTest(code=code, status=status), patch.object(checker, "invoke", return_value=result), \
                    self.assertRaises(AssertionError):
                checker.reject_sqlite(self.case())

    def test_prepared_labels_and_modifiers_are_exact_and_do_not_execute_described_queries(self):
        labels = checker.label_cases()
        self.assertEqual(len(labels), 9)
        sql, wanted = checker.describe_script(labels, [row["sql"] for row in labels])
        self.assertEqual(wanted, [value for pair in (
            ("extract", "numeric"), ("extract", "text"), ("extract", "numeric"),
            ("?column?", "numeric"), ("coalesce", "numeric"), ("extract", "numeric(8,2)"),
            ("extract", "numeric"), ("extract", "numeric"), ("extract", "numeric"))
            for value in ["|".join(pair)] * 2])
        self.assertEqual(sql.count("\\gdesc"), 18)
        self.assertNotIn("RETURNS TABLE", sql)
        self.assertIn("EXTRACT('TIMEZONE' FROM TIMESTAMP 'infinity')", sql)

    def exercise_main(self, *, values=None, nulls=None, errors=None, metadata=None, functions=None):
        row, runtime, label, shortcut = (self.case(), checker.runtime_cases()[0],
                                        checker.label_cases()[0], checker.null_shortcuts()[0])
        source_sql = "SELECT EXTRACT(YEAR FROM DATE '2000-01-01') /* never_execute_source */;"
        source = [{"sql": source_sql, "observed_syntax": {"source_free": True}}]
        values = (transcript("exact_types", ["56.789000", "numeric"]) +
                  transcript("exact_types", [None, "numeric"], 2)) if values is None else values
        nulls = (transcript("extract_null", ["false"]) +
                 transcript("extract_null", ["true"], 2)) if nulls is None else nulls
        errors = transcript("extract_error", ["22023"]) if errors is None else errors
        metadata = "v|numeric\n" * 4 + "extract|numeric\n" * 2 if metadata is None else metadata
        functions = "".join(f"{i}|t\n" for i in range(6)) if functions is None else functions
        results = [subprocess.CompletedProcess(["psql"], 0, output, "") for output in
                   (values, nulls, errors, metadata, functions, "16.15\n")]
        with patch.object(checker, "load_cases", return_value=([row], source)), \
                patch.object(checker, "runtime_cases", return_value=[runtime]), \
                patch.object(checker, "label_cases", return_value=[label]), \
                patch.object(checker, "null_shortcuts", return_value=[shortcut]), \
                patch.object(checker, "validity") as validity, \
                patch.object(checker, "assert_report") as certificates, \
                patch.object(checker, "replay", side_effect=lambda profile, sql: {"sql": sql}) as replay, \
                patch.object(checker, "reject_sqlite"), \
                patch.object(checker, "boundaries", return_value=0), \
                patch.object(checker, "connection", return_value=nullcontext(["psql"])), \
                patch.object(checker, "run", side_effect=results) as run, \
                patch("sys.argv", ["check_extract_cli.py", "--dsn", "unused"]), \
                redirect_stdout(io.StringIO()):
            checker.main()
            return run.call_args_list, validity.call_args_list, certificates.call_args_list, replay.call_args_list

    def test_pipeline_keeps_source_queries_in_certificate_rendering_checks_only(self):
        calls, validity, certificates, replays = self.exercise_main()
        self.assertEqual(len(calls), 6)
        for call in calls[:5]:
            self.assertIn("ON_ERROR_STOP=1", call.args[0])
            self.assertEqual(call.kwargs["timeout"], 120)
            self.assertNotIn("never_execute_source", call.kwargs["input"])
        self.assertEqual(len(validity), 4)
        self.assertEqual(len(certificates), 1)
        self.assertIn("never_execute_source", certificates[0].args[0][-1])
        self.assertEqual(certificates[0].args[1:], ("valid", "contract"))
        self.assertEqual(sum("never_execute_source" in call.args[1] for call in replays), 2)

    def test_pipeline_rejects_missing_duplicated_wrong_precision_oid_and_null_values(self):
        good = transcript("exact_types", ["56.789000", "numeric"])
        shortcut = transcript("exact_types", [None, "numeric"], 2)
        bad = ["", good, shortcut, good + shortcut + shortcut]
        for value, oid in (("56.789", "numeric"), ("56.790000", "numeric"),
                           ("56.789000", "double precision"), (None, "numeric")):
            bad.append(transcript("exact_types", [value, oid]) + shortcut)
        for values in bad:
            with self.subTest(values=values), self.assertRaises((AssertionError, ValueError)):
                self.exercise_main(values=values)

    def test_pipeline_requires_sql_null_bits_even_when_text_values_look_similar(self):
        good = transcript("extract_null", ["false"]) + transcript("extract_null", ["true"], 2)
        for nulls in ("", good + good, transcript("extract_null", ["false"]),
                      transcript("extract_null", ["true"]) + transcript("extract_null", ["false"], 2),
                      transcript("extract_null", ["false"]) + transcript("extract_null", [None], 2),
                      transcript("extract_null", ["false"]) + transcript("extract_null", ["t"], 2)):
            with self.subTest(nulls=nulls), self.assertRaises((AssertionError, ValueError)):
                self.exercise_main(nulls=nulls)

    def test_pipeline_rejects_wrong_missing_reordered_and_renamed_descriptors(self):
        for metadata in ("", "v|numeric\n" * 4 + "extract|numeric\n",
                         "v|double precision\n" * 4 + "extract|numeric\n" * 2,
                         "v|numeric\n" * 4 + "renamed|numeric\n" * 2,
                         "extract|numeric\n" * 2 + "v|numeric\n" * 4):
            with self.subTest(metadata=metadata), self.assertRaises(AssertionError):
                self.exercise_main(metadata=metadata)

    def test_pipeline_rejects_missing_duplicate_false_or_reordered_function_evidence(self):
        good = [f"{i}|t" for i in range(6)]
        bad = [[], good[:-1], good + good[:1], list(reversed(good))]
        for i in range(6):
            changed = good[:]
            changed[i] = f"{i}|f"
            bad.append(changed)
        for rows in bad:
            with self.subTest(rows=rows), self.assertRaises(AssertionError):
                self.exercise_main(functions="\n".join(rows) + "\n")

    def test_pipeline_requires_actual_runtime_errors_not_success_timeout_or_another_error(self):
        good = transcript("extract_error", ["22023"])
        for errors in ("", good + good, transcript("extract_error", ["unexpected-success"]),
                       transcript("extract_error", ["57014"]), transcript("extract_error", ["0A000"]),
                       transcript("extract_error", [None])):
            with self.subTest(errors=errors), self.assertRaises((AssertionError, ValueError)):
                self.exercise_main(errors=errors)

    def test_boundaries_separate_type_coverage_runtime_units_and_malformed_syntax(self):
        good = subprocess.CompletedProcess([], 1, json.dumps({
            "status": "invalid", "diagnostic": {"code": "input.parse"}}), "")
        with patch.object(checker, "assert_report") as reports, \
                patch.object(checker, "invoke", return_value=good) as invoke:
            self.assertEqual(checker.boundaries(), 23)
        self.assertEqual([sum(call.args[1] == status for call in reports.call_args_list)
                          for status in ("invalid", "unsupported", "valid", "rejected")],
                         [9, 2, 3, 1])
        self.assertEqual(len(invoke.call_args_list), 8)
        for sql in ("SELECT EXTRACT(foo FROM DATE '2024-01-01')",
                    "SELECT EXTRACT(HOUR FROM DATE '2024-01-01')"):
            self.assertTrue(any(call.args[0][-1] == sql and call.args[1] == "valid"
                                for call in reports.call_args_list))
        bad = subprocess.CompletedProcess([], 3, json.dumps({
            "status": "unsupported", "diagnostic": {"code": "input.parse"}}), "")
        with patch.object(checker, "assert_report"), patch.object(checker, "invoke", return_value=bad), \
                self.assertRaises(AssertionError):
            checker.boundaries()


if __name__ == "__main__":
    unittest.main()
