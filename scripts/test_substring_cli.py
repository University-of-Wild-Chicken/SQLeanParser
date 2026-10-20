"""SUBSTRING bindings, native evidence, and the downloaded-source boundary."""
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
import check_substring_cli as checker
from check_postgresql_cli import NULL, marker
from generate_substring_examples import cases


def transcript(category, values, index=1):
    def field(value):
        return NULL if value is None else '"' + value.replace('"', '""') + '"'
    result = []
    for form in ("source", "postgres"):
        result += [marker(category, index, True, form),
                   '"value","type"' if len(values) == 2 else '"observation"',
                   ",".join(map(field, values))]
    return "\n".join(result) + "\n"


class SubstringCliTests(unittest.TestCase):
    @staticmethod
    def case(shape="from"):
        return next(row for row in cases() if row["shape"] == shape)

    def fixtures(self, rows=None, source=None, signatures=None):
        temporary = tempfile.TemporaryDirectory()
        self.addCleanup(temporary.cleanup)
        directory = Path(temporary.name)
        if rows is not None:
            (directory / "synthetic.json").write_text(json.dumps(rows))
        if source is not None:
            (directory / "concrete.jsonl").write_text("".join(json.dumps(row) + "\n" for row in source))
        if signatures is not None:
            (directory / "function_signatures.json").write_text(json.dumps(signatures))
        return directory

    def test_fifty_authored_and_fifty_unchanged_sources_are_closed(self):
        rows, source = checker.load_cases()
        self.assertEqual(rows, cases())
        self.assertEqual((len(rows), len(source)), (50, 50))
        self.assertEqual(sum(row["expected_value"] is None for row in rows), 5)
        for row in source:
            self.assertEqual(row["raw_sql"], row["sql"])
            self.assertEqual(row["transformations"], [])
            self.assertIs(row["observed_syntax"]["source_free"], True)
            self.assertIsNone(row["parameter_types"])

    def test_loader_rejects_wrong_counts_identity_schema_and_parameter_order(self):
        original_rows, original_source = checker.load_cases()
        for mutation in ("missing", "source_missing", "duplicate_id", "duplicate_sql", "source_duplicate",
                         "type", "name", "nullable", "arity", "oid", "display", "value", "null_nonnull",
                         "kind", "sqlite", "scope", "source_types", "rewrite", "raw",
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
            elif mutation in {"type", "name", "nullable"}:
                row["output_columns"][0][mutation] = {"type": "int", "name": "wrong", "nullable": 0}[mutation]
            elif mutation == "arity":
                row["output_columns"] *= 2
            elif mutation in {"oid", "display"}:
                row[{"oid": "postgres_type", "display": "postgres_display_type"}[mutation]] = "bytea"
            elif mutation == "value":
                row["expected_value"] = 1
            elif mutation == "null_nonnull":
                row["expected_value"] = None
            elif mutation == "kind":
                row["source_kind"] = "engine-regression"
            elif mutation == "sqlite":
                row["sqlite_supported"] = True
            elif mutation == "scope":
                source[0]["observed_syntax"]["source_free"] = 1
            elif mutation == "source_types":
                source[0]["parameter_types"] = ""
            elif mutation == "rewrite":
                source[0]["transformations"] = ["changed"]
            elif mutation == "raw":
                source[0]["raw_sql"] += " "
            else:
                row = next(row for row in rows if row["shape"] == "numbered-reordered")
                if mutation == "extra_binding":
                    row["parameter_values"].append("unused")
                elif mutation == "missing_binding":
                    row["parameter_values"].pop()
                else:
                    row["sqlite_input"] = "SELECT SUBSTRING(?3 FOR ?2 FROM ?1) AS v;"
            with self.subTest(mutation=mutation), patch.object(checker, "FIXTURES",
                    self.fixtures(rows, source)), self.assertRaises(AssertionError):
                checker.load_cases()

    def test_six_native_declarations_require_exact_signature_strictness_and_scalar_return(self):
        declarations = json.loads((checker.FIXTURES / "function_signatures.json").read_text())
        expected_signatures = {
            (("text", "integer"), "text"), (("text", "integer", "integer"), "text"),
            (("bytea", "integer"), "bytea"), (("bytea", "integer", "integer"), "bytea"),
            (("text", "text"), "text"), (("text", "text", "text"), "text")}
        self.assertEqual({(tuple(row["inputs"]), row["output"]) for row in declarations}, expected_signatures)
        sql, expected = checker.function_script()
        self.assertEqual(expected, [f"{index}|t" for index in range(6)])
        for predicate in ("p.pronamespace='pg_catalog'::regnamespace", "p.proname='substring'",
                          "p.proisstrict", "p.provolatile='i'", "p.prokind='f'", "NOT p.proretset"):
            self.assertEqual(sql.count(predicate), 6)
        for mutation in ("missing", "duplicate", "output", "input", "name"):
            rows = deepcopy(declarations)
            if mutation == "missing":
                rows.pop()
            elif mutation == "duplicate":
                rows[1] = deepcopy(rows[0])
            elif mutation == "output":
                rows[0]["output"] = "bytea"
            elif mutation == "input":
                rows[0]["inputs"][1] = "bigint"
            else:
                rows[0]["name"] = "substr"
            with self.subTest(mutation=mutation), patch.object(checker, "FIXTURES",
                    self.fixtures(signatures=rows)), self.assertRaises(AssertionError):
                checker.function_script()

    def test_reversed_anonymous_and_reordered_numbered_bindings_keep_source_order(self):
        expectations = {
            "anonymous": ("SUBSTRING($1 FROM $2 FOR $3)", "(abcdef, 2, 3)"),
            "anonymous-reversed": ("SUBSTRING($1 FOR $2 FROM $3)", "(abcdef, 3, 2)"),
            "numbered-reordered": ("SUBSTRING($3 FOR $1 FROM $2)", "(3, 2, abcdef)"),
            "numbered-repeated": ("SUBSTRING($1 FROM $2 FOR $2)", "(abcdef, 2)"),
            "nullable-binding": ("SUBSTRING($1 FROM $2)", "(NULL, 2)"),
        }
        for shape, (sql_expression, binding) in expectations.items():
            row = self.case(shape)
            for function in (checker.database_script, checker.null_script, checker.describe_script):
                script, _ = function([row], [row["sql"]])
                with self.subTest(shape=shape, observer=function.__name__):
                    self.assertEqual(script.count(sql_expression), 2)
                    self.assertIn(binding, script.replace("'", ""))
                    self.assertIn("PREPARE ", script)
                    self.assertNotIn("SUBSTRING(?", script)
                    self.assertNotIn("(text?,", script)

    def test_native_text_characters_bytea_bytes_empty_and_sql_null_are_distinct(self):
        expected = {
            "unicode-characters": ("é🙂界", "text"), "bytea-zero-byte": ("\\x0102", "bytea"),
            "bytea-empty": ("\\x", "bytea"), "zero-length": ("", "text"),
            "regex-no-match": (None, "text"), "char-padding-conversion": ("bc", "text"),
            "regex-first-capture": ("a", "text"), "for-rounded-numeric": ("abc", "text"),
        }
        for shape, (value, oid) in expected.items():
            row = self.case(shape)
            self.assertEqual((row["expected_value"], row["postgres_type"]), (value, oid))
            _, wanted = checker.database_script([row], [row["sql"]])
            checker.validate_results(checker.parse_results(transcript("exact_types", [value, oid])), wanted)
        row = self.case("bytea-zero-byte")
        script, wanted = checker.database_script([row], [row["sql"]])
        for value, oid in (("\\x000102ff", "bytea"), ("\\x0102", "text"), ("", "bytea"),
                           ("\\x", "bytea"), (None, "bytea"), ("NULL", "bytea")):
            with self.subTest(value=value, oid=oid), self.assertRaises(AssertionError):
                checker.validate_results(checker.parse_results(transcript("exact_types", [value, oid])), wanted)
        self.assertIn("SET LOCAL bytea_output = 'hex'", script)
        self.assertIn("SET LOCAL statement_timeout = '5s'", script)
        self.assertTrue(script.endswith("ROLLBACK;"))

    def test_numeric_and_regex_nullability_and_null_shortcuts_are_kept_separate(self):
        for shape in ("from", "bytea-from", "for-boolean-true"):
            self.assertIs(self.case(shape)["output_columns"][0]["nullable"], False)
        for shape in ("regex-whole-match", "similar-capture", "regex-no-match",
                      "for-json-number", "nullable-binding"):
            self.assertIs(self.case(shape)["output_columns"][0]["nullable"], True)
        shortcuts = checker.null_shortcuts()
        self.assertEqual(len(shortcuts), 4)
        self.assertEqual([row["postgres_type"] for row in shortcuts], ["text", "text", "bytea", "text"])
        for row in shortcuts:
            self.assertIsNone(row["expected_value"])
            self.assertIs(row["output_columns"][0]["nullable"], True)
        self.assertIn("FROM '['", shortcuts[0]["sql"])
        self.assertIn("ESCAPE 'xx'", shortcuts[1]["sql"])
        self.assertIn("FOR -1", shortcuts[2]["sql"])

    def test_contract_requires_exact_schema_parameter_environment_and_derivation_evidence(self):
        row = self.case("anonymous-reversed")
        report = {"status": "valid", "assurance": "declarative",
                  "profile": assurance.PROFILES["contract"], "evidence": "declarative-derivation",
                  "catalogUnchanged": True, "typePrecision": "exact",
                  "outputColumns": deepcopy(row["output_columns"])}
        with patch.object(assurance, "invoke", return_value=subprocess.CompletedProcess(
                [], 0, json.dumps(report), "")) as invoke:
            checker.validity(row)
        self.assertEqual(invoke.call_args.args[0], [
            "--assurance", "contract", "--param-types", "text,int,int", row["sql"]])
        bad_reports = []
        for field, value in (("name", "substring"), ("type", "bytea"), ("nullable", True), ("nullable", 0)):
            bad = deepcopy(report)
            bad["outputColumns"][0][field] = value
            bad_reports.append(bad)
        for field, value in (("profile", "wrong"), ("evidence", "checker-acceptance"),
                             ("catalogUnchanged", False), ("typePrecision", "family"),
                             ("assurance", "executable"), ("status", "unsupported"),
                             ("outputColumns", None)):
            bad = deepcopy(report)
            bad[field] = value
            bad_reports.append(bad)
        for bad in bad_reports:
            with self.subTest(report=bad), patch.object(assurance, "invoke",
                    return_value=subprocess.CompletedProcess([], 0, json.dumps(bad), "")), self.assertRaises(AssertionError):
                checker.validity(row)

    def test_runtime_errors_bind_bad_values_and_require_exact_sqlstates(self):
        rows = checker.runtime_cases()
        self.assertEqual([row["sqlstate"] for row in rows],
                         ["22011", "2201B", "22025", "2201B", "22P02", "22003", "22023", "22023"])
        sql, wanted = checker.error_script(rows, [row["sql"] for row in rows])
        self.assertEqual(len(wanted), 16)
        self.assertEqual(sql.count("RETURN SQLSTATE"), 16)
        self.assertEqual(sql.count("RETURN ''unexpected-success''"), 16)
        self.assertIn("SUBSTRING($1 FROM 1 FOR $2)", sql)
        self.assertIn("SUBSTRING($1 FOR CAST($2 AS JSONB))", sql)
        self.assertTrue(sql.endswith("ROLLBACK;"))
        for function, population in ((checker.database_script, [self.case()]),
                                     (checker.null_script, checker.null_shortcuts()),
                                     (checker.describe_script, checker.label_cases()),
                                     (checker.error_script, rows)):
            with self.subTest(observer=function.__name__), self.assertRaises(AssertionError):
                function(population, [])

    def test_prepared_labels_keep_substring_name_and_exact_varchar_modifier(self):
        rows = checker.label_cases()
        self.assertEqual([(row["output_columns"][0]["name"], row["postgres_display_type"]) for row in rows],
                         [("substring", "text")] * 5 + [("substring", "character varying(2)"),
                                                        ("substring", "text"), ("coalesce", "text")])
        sql, wanted = checker.describe_script(rows, [row["sql"] for row in rows])
        self.assertEqual(len(wanted), 16)
        self.assertEqual(sql.count("\\gdesc"), 16)
        self.assertEqual(wanted.count("substring|character varying(2)"), 2)

    def test_sqlite_rejection_requires_consistent_status_exit_and_known_code(self):
        allowed = [(1, "invalid", "input.parse"),
                   (3, "unsupported", "coverage.sqlite.substring"),
                   (3, "unsupported", "coverage.sqlite.scalar-function-signatures")]
        for code, status, diagnostic in allowed:
            result = subprocess.CompletedProcess([], code, json.dumps({
                "status": status, "diagnostic": {"code": diagnostic}}), "")
            with patch.object(checker, "invoke", return_value=result) as invoke:
                checker.reject_sqlite(self.case())
            self.assertEqual(invoke.call_args.kwargs["stdin"], self.case()["sqlite_input"])
        for code, status, diagnostic in (
                (0, "rendered", "coverage.sqlite.substring"), (1, "unsupported", "coverage.sqlite.substring"),
                (3, "invalid", "input.parse"), (3, "unsupported", "input.parse"),
                (3, "unsupported", "coverage.sqlite.other"), (4, "inconclusive", "resource.depth")):
            result = subprocess.CompletedProcess([], code, json.dumps({
                "status": status, "diagnostic": {"code": diagnostic}}), "")
            with self.subTest(code=code, status=status), patch.object(checker, "invoke", return_value=result), \
                    self.assertRaises(AssertionError):
                checker.reject_sqlite(self.case())

    def exercise_main(self, *, values=None, nulls=None, errors=None, descriptors=None, functions=None):
        row, shortcut, error, label = (self.case(), checker.null_shortcuts()[0],
                                      checker.runtime_cases()[0], checker.label_cases()[0])
        source = [{"sql": "SELECT substring('never_execute_source' FROM 2);"}]
        values = (transcript("exact_types", ["bcdef", "text"]) +
                  transcript("exact_types", [None, "text"], 2)) if values is None else values
        nulls = (transcript("extract_null", ["false"]) +
                 transcript("extract_null", ["true"], 2)) if nulls is None else nulls
        errors = transcript("extract_error", ["22011"]) if errors is None else errors
        descriptors = "v|text\n" * 4 + "substring|text\n" * 2 if descriptors is None else descriptors
        functions = "\n".join(f"{i}|t" for i in range(6)) + "\n" if functions is None else functions
        results = [subprocess.CompletedProcess([], 0, text, "") for text in
                   (values, nulls, errors, descriptors, functions, "16.15\n")]
        with patch.object(checker, "load_cases", return_value=([row], source)), \
                patch.object(checker, "null_shortcuts", return_value=[shortcut]), \
                patch.object(checker, "runtime_cases", return_value=[error]), \
                patch.object(checker, "label_cases", return_value=[label]), \
                patch.object(checker, "validity") as validity, \
                patch.object(checker, "assert_report") as certificates, \
                patch.object(checker, "replay", side_effect=lambda profile, sql: {"sql": sql}) as replay, \
                patch.object(checker, "reject_sqlite"), patch.object(checker, "boundaries", return_value=0), \
                patch.object(checker, "connection", return_value=nullcontext(["psql"])), \
                patch.object(checker, "run", side_effect=results) as run, \
                patch("sys.argv", ["check_substring_cli.py", "--dsn", "unused"]), redirect_stdout(io.StringIO()):
            checker.main()
            return run.call_args_list, validity.call_args_list, certificates.call_args_list, replay.call_args_list

    def test_main_certifies_and_renders_external_sources_but_never_executes_them(self):
        calls, validity, certificates, replays = self.exercise_main()
        self.assertEqual((len(calls), len(validity), len(certificates)), (6, 4, 1))
        self.assertEqual(certificates[0].args[1:], ("valid", "contract"))
        self.assertEqual(sum("never_execute_source" in call.args[1] for call in replays), 2)
        for call in calls[:5]:
            self.assertIn("ON_ERROR_STOP=1", call.args[0])
            self.assertEqual(call.kwargs["timeout"], 120)
            self.assertNotIn("never_execute_source", call.kwargs["input"])

    def test_main_rejects_missing_duplicate_corrupted_values_and_null_bits(self):
        extra = transcript("exact_types", [None, "text"], 2)
        good = transcript("exact_types", ["bcdef", "text"]) + extra
        for values in ("", extra, good + good, transcript("exact_types", ["bcd", "text"]) + extra,
                       transcript("exact_types", ["bcdef", "bytea"]) + extra,
                       transcript("exact_types", [None, "text"]) + extra):
            with self.subTest(values=values), self.assertRaises((AssertionError, ValueError)):
                self.exercise_main(values=values)
        for first, second in (("true", "true"), ("false", "false"), (None, "true"), ("false", None)):
            with self.subTest(first=first, second=second), self.assertRaises(AssertionError):
                self.exercise_main(nulls=transcript("extract_null", [first]) +
                                   transcript("extract_null", [second], 2))
        with self.assertRaises(AssertionError):
            self.exercise_main(nulls="")

    def test_main_rejects_missing_wrong_labels_and_native_declarations(self):
        for descriptors in ("", "v|text\n" * 4, "v|bytea\n" * 4 + "substring|text\n" * 2,
                            "v|text\n" * 4 + "renamed|text\n" * 2,
                            "substring|text\n" * 2 + "v|text\n" * 4):
            with self.subTest(descriptors=descriptors), self.assertRaises(AssertionError):
                self.exercise_main(descriptors=descriptors)
        good = [f"{i}|t" for i in range(6)]
        for lines in ([], good[:-1], good + good[:1], list(reversed(good)),
                      ["0|f", *good[1:]], ["0|true", *good[1:]]):
            with self.subTest(lines=lines), self.assertRaises(AssertionError):
                self.exercise_main(functions="\n".join(lines) + "\n")

    def test_main_rejects_runtime_success_timeout_wrong_error_and_missing_observation(self):
        good = transcript("extract_error", ["22011"])
        for errors in ("", good + good, transcript("extract_error", ["unexpected-success"]),
                       transcript("extract_error", ["57014"]), transcript("extract_error", ["2201B"]),
                       transcript("extract_error", [None])):
            with self.subTest(errors=errors), self.assertRaises((AssertionError, ValueError)):
                self.exercise_main(errors=errors)

    def test_boundaries_separate_static_coverage_and_syntax_failure(self):
        good = subprocess.CompletedProcess([], 1, json.dumps({
            "status": "invalid", "diagnostic": {"code": "input.parse"}}), "")
        with patch.object(checker, "assert_report") as report, patch.object(checker, "invoke", return_value=good) as invoke:
            self.assertEqual(checker.boundaries(), 23)
        self.assertEqual([sum(call.args[1] == status for call in report.call_args_list)
                          for status in ("invalid", "unsupported")], [10, 3])
        self.assertEqual(len(invoke.call_args_list), 10)
        bad = subprocess.CompletedProcess([], 3, json.dumps({
            "status": "unsupported", "diagnostic": {"code": "input.parse"}}), "")
        with patch.object(checker, "assert_report"), patch.object(checker, "invoke", return_value=bad), \
                self.assertRaises(AssertionError):
            checker.boundaries()


if __name__ == "__main__":
    unittest.main()
