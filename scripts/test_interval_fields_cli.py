"""Protocol integrity for interval ranges, precision and native typmod evidence."""
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
import check_interval_fields_cli as checker
from check_postgresql_cli import NULL, marker
from generate_interval_field_examples import cases

MASKS = {
    "year": 4, "month": 2, "day": 8, "hour": 1024, "minute": 2048, "second": 4096,
    "year to month": 6, "day to hour": 1032, "day to minute": 3080,
    "day to second": 7176, "hour to minute": 3072, "hour to second": 7168,
    "minute to second": 6144,
}


def transcript(category, values, index=1):
    def field(value):
        return NULL if value is None else '"' + value.replace('"', '""') + '"'
    lines = []
    for form in ("source", "postgres"):
        lines += [marker(category, index, True, form),
                  '"value","type"' if len(values) == 2 else '"observation"',
                  ",".join(map(field, values))]
    return "\n".join(lines) + "\n"


class IntervalFieldsCliTests(unittest.TestCase):
    @staticmethod
    def case(shape="literal-year"):
        return next(row for row in cases() if row["shape"] == shape)

    def fixture_directory(self, rows, source):
        temporary = tempfile.TemporaryDirectory()
        self.addCleanup(temporary.cleanup)
        directory = Path(temporary.name)
        (directory / "synthetic.json").write_text(json.dumps(rows))
        (directory / "concrete.jsonl").write_text("".join(json.dumps(row) + "\n" for row in source))
        return directory

    def test_closed_authored_and_unchanged_populations_keep_all_thirteen_masks(self):
        rows, source = checker.load_cases()
        self.assertEqual(rows, cases())
        self.assertEqual((len(rows), len(source)), (50, 50))
        self.assertEqual(checker.FIELDS, MASKS)
        self.assertEqual({r["observed_syntax"]["interval_fields"][0]["fields"] for r in source}, set(MASKS))
        self.assertTrue(all(r["raw_sql"] == r["sql"] and r["transformations"] == [] for r in source))
        self.assertEqual(sum(r["expected_value"] is None for r in rows), 1)

    def test_loader_rejects_missing_duplicates_wrong_modifiers_masks_and_bindings(self):
        original_rows, original_source = checker.load_cases()
        mutations = (
            "missing", "source_missing", "duplicate_id", "duplicate_sql", "source_duplicate",
            "name", "nullable", "arity", "oid", "display", "value", "null_nonnull", "kind",
            "sqlite", "extra_binding", "missing_binding", "binding_order", "raw_sql", "rewrite",
            "scope", "invented_parameters", "mask", "float_mask", "precision_bool",
            "precision_limit", "precision_field", "all_ranges",
        )
        for mutation in mutations:
            rows, source = deepcopy(original_rows), deepcopy(original_source)
            row, form = rows[0], source[0]["observed_syntax"]["interval_fields"][0]
            if mutation == "missing":
                rows.pop()
            elif mutation == "source_missing":
                source.pop()
            elif mutation.startswith("duplicate_"):
                key = mutation.removeprefix("duplicate_")
                rows[1][key] = rows[0][key]
            elif mutation == "source_duplicate":
                source[1]["sql"] = source[0]["sql"]
            elif mutation in ("name", "nullable"):
                row["output_columns"][0][mutation] = {"name": "wrong", "nullable": 0}[mutation]
            elif mutation == "arity":
                row["output_columns"] *= 2
            elif mutation == "oid":
                row["postgres_type"] = "interval year"
            elif mutation == "display":
                row["postgres_display_type"] = "interval"
            elif mutation == "value":
                row["expected_value"] = 1
            elif mutation == "null_nonnull":
                row["expected_value"] = None
            elif mutation == "kind":
                row["source_kind"] = "engine-regression"
            elif mutation == "sqlite":
                row["sqlite_supported"] = True
            elif mutation in ("extra_binding", "missing_binding", "binding_order"):
                row = next(r for r in rows if r["shape"] == "reordered")
                if mutation == "extra_binding":
                    row["parameter_values"].append("unused")
                elif mutation == "missing_binding":
                    row["parameter_values"].pop()
                else:
                    row["sqlite_input"] = "SELECT CAST(?1 AS INTERVAL YEAR) > CAST(?2 AS INTERVAL MONTH) AS v;"
            elif mutation == "raw_sql":
                source[0]["raw_sql"] += " "
            elif mutation == "rewrite":
                source[0]["transformations"] = ["changed"]
            elif mutation == "scope":
                source[0]["observed_syntax"]["source_free"] = 1
            elif mutation == "invented_parameters":
                source[0]["parameter_types"] = ""
            elif mutation == "mask":
                form["mask"] = 32767
            elif mutation == "float_mask":
                form["mask"] = float(form["mask"])
            elif mutation == "precision_bool":
                form["precision"] = True
            elif mutation == "precision_limit":
                form["precision"] = 7
            elif mutation == "precision_field":
                form = next(item["observed_syntax"]["interval_fields"][0] for item in source
                            if item["observed_syntax"]["interval_fields"][0]["fields"] == "year")
                form["precision"] = 2
            else:
                for item in source:
                    field = item["observed_syntax"]["interval_fields"][0]
                    field["fields"], field["mask"], field["precision"] = "second", 4096, None
            with self.subTest(mutation=mutation), patch.object(checker, "FIXTURES",
                    self.fixture_directory(rows, source)), self.assertRaises(AssertionError):
                checker.load_cases()

    def test_input_context_and_array_precision_are_observed_independently(self):
        expected = {
            "unknown-input": ("interval year", "1 year"),
            "known-text-input": ("interval year", "00:00:00"),
            "known-interval-input": ("interval year", "00:00:00"),
            "array-element-input": ("interval year[]", "{00:00:00,00:00:00}"),
            "array-equal-modifiers": ("interval year[]", '{"1 year","2 years"}'),
            "array-different-modifiers": ("interval[]", '{"1 year","2 mons"}'),
            "array-cast": ("interval year[]", '{"1 year","2 years"}'),
            "coalesce-different-modifiers": ("interval", "2 years"),
            "nullif-left-modifiers": ("interval hour", "02:00:00"),
            "date-arithmetic": ("timestamp", "2024-02-29 00:00:00"),
        }
        for shape, (type_, value) in expected.items():
            row = self.case(shape)
            self.assertEqual((row["output_columns"][0]["type"], row["expected_value"]), (type_, value))
        for shape in ("array-index", "array-slice", "nullif-left-modifiers", "null-binding"):
            self.assertIs(self.case(shape)["output_columns"][0]["nullable"], True)

    def test_native_typmod_matrix_distinguishes_absent_zero_two_six_and_array_oids(self):
        sql, expected = checker.typmod_script()
        self.assertEqual(len(expected), 50)
        self.assertEqual(sql.count("CREATE TEMP VIEW interval_descriptor"), 50)
        self.assertEqual(sql.count("DROP VIEW interval_descriptor"), 50)
        self.assertIn("a.atttypmod", sql)
        self.assertIn("pg_catalog.format_type(a.atttypid, a.atttypmod)", sql)
        self.assertTrue(sql.endswith("ROLLBACK;"))
        observations = {}
        for index, row in enumerate(expected):
            number, name, oid, typmod, display = row.split("|")
            self.assertEqual((number, name), (str(index), "v"))
            self.assertEqual(oid, "interval[]" if display.endswith("[]") else "interval")
            self.assertNotIn(display, observations)
            observations[display] = int(typmod)
        for fields, mask in MASKS.items():
            for array in ("", "[]"):
                self.assertEqual(observations["interval " + fields + array], (mask << 16) | 65535)
                if fields.endswith("second"):
                    for precision in (0, 2, 6):
                        self.assertEqual(observations[f"interval {fields}({precision}){array}"],
                                         (mask << 16) | precision)
                    self.assertNotEqual(observations["interval " + fields + array],
                                        observations[f"interval {fields}(6){array}"])

    def test_prepare_parameter_modifiers_are_erased_until_an_explicit_cast(self):
        extra = checker.parameter_cases()
        self.assertEqual(len(extra), 8)
        for plain, casted in zip(extra[::2], extra[1::2]):
            self.assertEqual(plain["sql"], "SELECT $1 AS v;")
            self.assertEqual(plain["parameter_types"], casted["parameter_types"])
            self.assertEqual(plain["parameter_values"], casted["parameter_values"])
            base = "interval[]" if plain["parameter_types"].endswith("[]") else "interval"
            self.assertEqual(plain["output_columns"][0]["type"], base)
            self.assertEqual(plain["postgres_display_type"], base)
            self.assertEqual(casted["output_columns"][0]["type"], casted["parameter_types"])
            self.assertNotEqual(plain["expected_value"], casted["expected_value"])
        self.assertEqual(extra[-2]["expected_value"], "{00:00:01.235,NULL}")
        self.assertEqual(extra[-1]["expected_value"], "{00:00:01.24,NULL}")

    def test_parameter_order_reuse_anonymous_and_sql_null_remain_real_bindings(self):
        for shape in ("reordered", "repeated", "anonymous-known-text", "null-binding"):
            row = self.case(shape)
            scripts = [checker.database_script([row], [row["sql"]])[0],
                       checker.null_script([row], [row["sql"]])[0],
                       checker.describe_script([row], [row["sql"]])[0]]
            for sql in scripts:
                self.assertIn("PREPARE ", sql)
                self.assertNotIn("CAST(? AS", sql)
                self.assertNotIn("(text?)", sql)
                if shape == "reordered":
                    self.assertEqual(sql.count("CAST($2 AS INTERVAL YEAR) > CAST($1 AS INTERVAL MONTH)"), 2)
                    self.assertIn("(2 months, 1 year)", sql.replace("'", ""))
                elif shape == "repeated":
                    self.assertEqual(sql.count("CAST($1 AS INTERVAL SECOND(2))"), 4)
                    self.assertIn("(1.235)", sql.replace("'", ""))
                elif shape == "anonymous-known-text":
                    self.assertEqual(sql.count("CAST($1 AS INTERVAL DAY)"), 2)
                    self.assertIn("(90)", sql.replace("'", ""))
                else:
                    self.assertIn("(NULL)", sql)

    def test_exact_contract_metadata_and_parameter_declaration_cannot_be_weakened(self):
        row = self.case("parameter-explicit-cast")
        report = {
            "status": "valid", "assurance": "declarative", "profile": assurance.PROFILES["contract"],
            "evidence": "declarative-derivation", "catalogUnchanged": True, "typePrecision": "exact",
            "outputColumns": deepcopy(row["output_columns"]),
        }
        good = subprocess.CompletedProcess([], 0, json.dumps(report), "")
        with patch.object(assurance, "invoke", return_value=good) as invoke:
            checker.validity(row)
        self.assertEqual(invoke.call_args.args[0],
                         ["--assurance", "contract", "--param-types", "interval year", row["sql"]])
        bad_reports = []
        for field, value in (("type", "interval"), ("type", "interval year(6)"),
                             ("name", "interval"), ("nullable", True), ("nullable", 0)):
            bad = deepcopy(report)
            bad["outputColumns"][0][field] = value
            bad_reports.append(bad)
        for field, value in (("evidence", "checker-acceptance"), ("typePrecision", "family"),
                             ("catalogUnchanged", False), ("profile", "wrong-profile"),
                             ("status", "checked"), ("assurance", "executable")):
            bad = deepcopy(report)
            bad[field] = value
            bad_reports.append(bad)
        bad = deepcopy(report)
        del bad["outputColumns"]
        bad_reports.append(bad)
        for bad in bad_reports:
            with self.subTest(report=bad), patch.object(assurance, "invoke",
                    return_value=subprocess.CompletedProcess([], 0, json.dumps(bad), "")), self.assertRaises(AssertionError):
                checker.validity(row)

    def test_native_interval_values_oids_and_null_bits_are_exact(self):
        row = self.case("repeated")
        sql, expected = checker.database_script([row], [row["sql"]])
        checker.validate_results(checker.parse_results(
            transcript("exact_types", ["00:00:02.48", "interval"])), expected)
        for value, oid in (("00:00:02.47", "interval"), ("2.48", "interval"),
                           ("00:00:02.48", "interval second(2)"), (None, "interval"),
                           ("NULL", "interval"), ("00:00:02.48", "text")):
            with self.subTest(value=value, oid=oid), self.assertRaises(AssertionError):
                checker.validate_results(checker.parse_results(transcript("exact_types", [value, oid])), expected)
        self.assertIn("SET LOCAL intervalstyle = 'postgres'", sql)
        self.assertIn("SET LOCAL statement_timeout = '5s'", sql)
        self.assertTrue(sql.endswith("ROLLBACK;"))

    def test_runtime_conversion_errors_are_distinct_from_success_timeout_and_overflow(self):
        rows = checker.runtime_cases()
        self.assertEqual([row["sqlstate"] for row in rows], ["22007", "22015", "22007", "22007"])
        sql, expected = checker.error_script(rows, [row["sql"] for row in rows])
        self.assertEqual(len(expected), 8)
        self.assertEqual(sql.count("RETURN SQLSTATE"), 8)
        self.assertEqual(sql.count("RETURN ''unexpected-success''"), 8)
        self.assertEqual(sql.count("PREPARE pagination_parameters (TEXT)"), 8)
        self.assertIn("CAST($1 AS interval second(2)[])", sql)
        self.assertTrue(sql.endswith("ROLLBACK;"))

    def test_prepared_result_labels_retain_postgresql_weak_name_rules(self):
        rows = checker.label_cases()
        self.assertEqual([(r["output_columns"][0]["name"], r["postgres_display_type"]) for r in rows], [
            ("interval", "interval year"), ("interval", "interval day"), ("text", "text"),
            ("case", "interval year"), ("coalesce", "interval year"), ("array", "interval year"),
            ("interval", "interval"), ("?column?", "interval"),
        ])
        sql, wanted = checker.describe_script(rows, [r["sql"] for r in rows])
        self.assertEqual(len(wanted), 16)
        self.assertEqual(sql.count("\\gdesc"), 16)
        self.assertNotIn("RETURNS TABLE", sql)
        self.assertIn("text|text", wanted)
        self.assertIn("case|interval year", wanted)

    def test_missing_canonical_entries_fail_before_zip_truncation(self):
        row = self.case()
        for function in (checker.database_script, checker.null_script, checker.describe_script):
            with self.subTest(function=function.__name__), self.assertRaises(AssertionError):
                function([row], [])
        with self.assertRaises(AssertionError):
            checker.error_script(checker.runtime_cases(), [])

    def test_sqlite_rejection_requires_paired_exit_status_and_known_feature(self):
        allowed = [(1, "invalid", "input.parse")] + [
            (3, "unsupported", "coverage.sqlite." + code) for code in
            ("PostgreSQL-type", "array-type", "array-constructor", "array-subscript", "extract")]
        for code, status, diagnostic in allowed:
            result = subprocess.CompletedProcess([], code, json.dumps({
                "status": status, "diagnostic": {"code": diagnostic}}), "")
            with patch.object(checker, "invoke", return_value=result) as invoke:
                checker.reject_sqlite(self.case())
            self.assertEqual(invoke.call_args.kwargs["stdin"], self.case()["sqlite_input"])
        for code, status, diagnostic in (
                (0, "rendered", "coverage.sqlite.PostgreSQL-type"),
                (1, "unsupported", "coverage.sqlite.PostgreSQL-type"),
                (3, "invalid", "input.parse"), (3, "unsupported", "input.parse"),
                (3, "unsupported", "coverage.sqlite.function"), (4, "inconclusive", "resource.depth")):
            result = subprocess.CompletedProcess([], code, json.dumps({
                "status": status, "diagnostic": {"code": diagnostic}}), "")
            with self.subTest(code=code, status=status), patch.object(checker, "invoke", return_value=result), \
                    self.assertRaises(AssertionError):
                checker.reject_sqlite(self.case())

    def exercise_main(self, *, values=None, nulls=None, errors=None, metadata=None, typmods=None):
        row, extra, error, label = (self.case(), checker.parameter_cases()[0],
                                    checker.runtime_cases()[0], checker.label_cases()[0])
        source = [{"sql": "SELECT INTERVAL '1' DAY /* never_execute_source */;",
                   "observed_syntax": {"interval_fields": [{"fields": "day", "mask": 8, "precision": None}]}}]
        values = (transcript("exact_types", ["1 year", "interval"]) +
                  transcript("exact_types", [extra["expected_value"], "interval"], 2)) if values is None else values
        nulls = (transcript("extract_null", ["false"]) +
                 transcript("extract_null", ["false"], 2)) if nulls is None else nulls
        errors = transcript("extract_error", ["22007"]) if errors is None else errors
        metadata = "v|interval year\n" * 2 + "v|interval\n" * 2 + "interval|interval year\n" * 2 if metadata is None else metadata
        typmods = "\n".join(checker.typmod_script()[1]) + "\n" if typmods is None else typmods
        results = [subprocess.CompletedProcess(["psql"], 0, text, "") for text in
                   (values, nulls, errors, metadata, typmods, "16.15\n")]
        with patch.object(checker, "load_cases", return_value=([row], source)), \
                patch.object(checker, "parameter_cases", return_value=[extra]), \
                patch.object(checker, "runtime_cases", return_value=[error]), \
                patch.object(checker, "label_cases", return_value=[label]), \
                patch.object(checker, "validity") as validity, \
                patch.object(checker, "assert_report") as certificates, \
                patch.object(checker, "replay", side_effect=lambda profile, sql: {"sql": sql}) as replay, \
                patch.object(checker, "reject_sqlite"), patch.object(checker, "boundaries", return_value=0), \
                patch.object(checker, "connection", return_value=nullcontext(["psql"])), \
                patch.object(checker, "run", side_effect=results) as run, \
                patch("sys.argv", ["check_interval_fields_cli.py", "--dsn", "unused"]), \
                redirect_stdout(io.StringIO()):
            checker.main()
            return run.call_args_list, validity.call_args_list, certificates.call_args_list, replay.call_args_list

    def test_pipeline_certifies_sources_with_exact_modifiers_but_never_executes_them(self):
        calls, validity, certificates, replays = self.exercise_main()
        self.assertEqual(len(calls), 6)
        for call in calls[:5]:
            self.assertIn("ON_ERROR_STOP=1", call.args[0])
            self.assertEqual(call.kwargs["timeout"], 120)
            self.assertNotIn("never_execute_source", call.kwargs["input"])
        self.assertEqual(len(validity), 4)
        self.assertEqual(len(certificates), 1)
        self.assertEqual(certificates[0].args[1:], ("valid", "contract", (("interval", "interval day", False),)))
        self.assertEqual(sum("never_execute_source" in call.args[1] for call in replays), 2)

    def test_pipeline_rejects_missing_duplicate_wrong_values_oids_and_null_bits(self):
        extra = transcript("exact_types", [checker.parameter_cases()[0]["expected_value"], "interval"], 2)
        good = transcript("exact_types", ["1 year", "interval"]) + extra
        for values in ("", extra, good + good, transcript("exact_types", ["1 year 2 mons", "interval"]) + extra,
                       transcript("exact_types", [None, "interval"]) + extra,
                       transcript("exact_types", ["1 year", "text"]) + extra):
            with self.subTest(values=values), self.assertRaises((AssertionError, ValueError)):
                self.exercise_main(values=values)
        good = transcript("extract_null", ["false"]) + transcript("extract_null", ["false"], 2)
        for nulls in ("", good + good, transcript("extract_null", ["false"]),
                      transcript("extract_null", ["true"]) + transcript("extract_null", ["false"], 2),
                      transcript("extract_null", [None]) + transcript("extract_null", ["false"], 2)):
            with self.subTest(nulls=nulls), self.assertRaises((AssertionError, ValueError)):
                self.exercise_main(nulls=nulls)

    def test_pipeline_rejects_missing_reordered_renamed_or_precision_erased_descriptors(self):
        for metadata in ("", "v|interval year\n" * 2 + "v|interval\n" * 2,
                         "v|interval\n" * 4 + "interval|interval year\n" * 2,
                         "v|interval year(6)\n" * 2 + "v|interval\n" * 2 + "interval|interval year\n" * 2,
                         "v|interval year\n" * 2 + "v|interval\n" * 2 + "renamed|interval year\n" * 2,
                         "interval|interval year\n" * 2 + "v|interval year\n" * 2 + "v|interval\n" * 2):
            with self.subTest(metadata=metadata), self.assertRaises(AssertionError):
                self.exercise_main(metadata=metadata)

    def test_pipeline_requires_raw_typmod_precision_and_array_oid_evidence(self):
        good = checker.typmod_script()[1]
        bad = [[], good[:-1], good + good[:1], list(reversed(good))]
        for field, value in ((1, "renamed"), (2, "text"), (3, "-1"), (4, "interval")):
            changed = good[:]
            columns = changed[0].split("|")
            columns[field] = value
            changed[0] = "|".join(columns)
            bad.append(changed)
        changed = good[:]
        i = next(i for i, row in enumerate(good) if row.endswith("|interval second"))
        six = next(row for row in good if row.endswith("|interval second(6)")).split("|")[3]
        columns = changed[i].split("|")
        columns[3] = six
        changed[i] = "|".join(columns)
        bad.append(changed)
        for rows in bad:
            with self.subTest(rows=rows[:2]), self.assertRaises(AssertionError):
                self.exercise_main(typmods="\n".join(rows) + "\n")

    def test_pipeline_requires_exact_runtime_error_not_success_timeout_or_different_sqlstate(self):
        good = transcript("extract_error", ["22007"])
        for errors in ("", good + good, transcript("extract_error", ["unexpected-success"]),
                       transcript("extract_error", ["57014"]), transcript("extract_error", ["22015"]),
                       transcript("extract_error", [None])):
            with self.subTest(errors=errors), self.assertRaises((AssertionError, ValueError)):
                self.exercise_main(errors=errors)

    def test_boundaries_keep_oversized_precision_unsupported_and_illegal_ranges_unparsed(self):
        good = subprocess.CompletedProcess([], 1, json.dumps({
            "status": "invalid", "diagnostic": {"code": "input.parse"}}), "")
        with patch.object(checker, "assert_report") as report, patch.object(checker, "invoke", return_value=good) as invoke:
            self.assertEqual(checker.boundaries(), 20)
        self.assertEqual([sum(call.args[1] == status for call in report.call_args_list)
                          for status in ("invalid", "unsupported")], [3, 5])
        self.assertEqual(len(invoke.call_args_list), 12)
        self.assertTrue(any("SECOND(7)" in call.args[0][-1] and call.args[1] == "unsupported"
                            for call in report.call_args_list))
        bad = subprocess.CompletedProcess([], 3, json.dumps({
            "status": "unsupported", "diagnostic": {"code": "input.parse"}}), "")
        with patch.object(checker, "assert_report"), patch.object(checker, "invoke", return_value=bad), \
                self.assertRaises(AssertionError):
            checker.boundaries()


if __name__ == "__main__":
    unittest.main()
