"""Evidence-integrity checks for the 87 authored PostgreSQL label observations."""
import hashlib
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

ROOT = Path(__file__).resolve().parents[1]
LABELS = ROOT / "fixtures/array_subscripts/labels.json"
CAPTURE_SHA256 = "d219e4a8fd06e779bd0f1fb1edc15b093e3ffa4ccb04841fda27a67d4c512a83"


class ArraySubscriptLabelFixtureTests(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        cls.rows = json.loads(LABELS.read_text())
        cls.by_sql = {row["sql"]: row for row in cls.rows}

    def test_capture_count_uniqueness_and_original_bytes_are_frozen(self):
        self.assertEqual(len(self.rows), 87)
        self.assertEqual(len(self.by_sql), 87)
        self.assertEqual(hashlib.sha256(LABELS.read_bytes()).hexdigest(), CAPTURE_SHA256)
        for row in self.rows:
            self.assertEqual(set(row), {"sql", "name", "type"})
            self.assertTrue(all(type(value) is str and value for value in row.values()))
            self.assertNotIn("parameter_values", row)

    def test_type_alias_pairs_keep_postgresql_generated_names_and_modifiers(self):
        aliases = [
            ("SMALLINT", "int2", "smallint"), ("INT2", "int2", "smallint"),
            ("INT", "int4", "integer"), ("INTEGER", "int4", "integer"), ("INT4", "int4", "integer"),
            ("BIGINT", "int8", "bigint"), ("INT8", "int8", "bigint"), ("TEXT", "text", "text"),
            ("VARCHAR(5)", "varchar", "character varying(5)"),
            ("CHARACTER VARYING(5)", "varchar", "character varying(5)"),
            ("CHAR(5)", "bpchar", "character(5)"), ("CHARACTER(5)", "bpchar", "character(5)"),
            ("BOOL", "bool", "boolean"), ("BOOLEAN", "bool", "boolean"),
            ("REAL", "float4", "real"), ("FLOAT4", "float4", "real"),
            ("DOUBLE PRECISION", "float8", "double precision"),
            ("FLOAT8", "float8", "double precision"), ("FLOAT", "float8", "double precision"),
            ("NUMERIC(6,2)", "numeric", "numeric(6,2)"), ("DECIMAL(6,2)", "numeric", "numeric(6,2)"),
            ("DATE", "date", "date"), ("TIME(2)", "time", "time(2) without time zone"),
            ("TIME(2) WITHOUT TIME ZONE", "time", "time(2) without time zone"),
            ("TIME(2) WITH TIME ZONE", "timetz", "time(2) with time zone"),
            ("TIMETZ(2)", "timetz", "time(2) with time zone"),
            ("TIMESTAMP(3)", "timestamp", "timestamp(3) without time zone"),
            ("TIMESTAMP(3) WITHOUT TIME ZONE", "timestamp", "timestamp(3) without time zone"),
            ("TIMESTAMP(3) WITH TIME ZONE", "timestamptz", "timestamp(3) with time zone"),
            ("TIMESTAMPTZ(3)", "timestamptz", "timestamp(3) with time zone"),
            ("INTERVAL(2)", "interval", "interval(2)"), ("UUID", "uuid", "uuid"),
            ("JSON", "json", "json"), ("JSONB", "jsonb", "jsonb"), ("BYTEA", "bytea", "bytea"),
        ]
        self.assertEqual(len(aliases), 35)
        expected = []
        for declaration, name, type_ in aliases:
            for sql in (f"SELECT NULL::{declaration}", f"SELECT (NULL::{declaration}[])[1]"):
                expected.append({"sql": sql, "name": name, "type": type_})
        self.assertEqual(self.rows[:70], expected)

    def test_case_and_cast_label_strengths_are_not_replaced_by_type_names(self):
        cases = {
            "SELECT (CAST(NULL::INTEGER AS NUMERIC))": ("numeric", "numeric"),
            "SELECT (CAST(ARRAY[1,2] AS BIGINT[]))[1]": ("array", "bigint"),
            "SELECT (CAST(ARRAY[1,2] AS BIGINT[]))[1:2]": ("array", "bigint[]"),
            "SELECT a::BIGINT FROM (SELECT 1 AS a) d": ("a", "bigint"),
            "SELECT CASE WHEN TRUE THEN 1 ELSE 2 END": ("case", "integer"),
            "SELECT CASE WHEN TRUE THEN 1 ELSE 2::BIGINT END": ("case", "bigint"),
            "SELECT (CASE WHEN TRUE THEN 1 ELSE 2 END)::BIGINT": ("int8", "bigint"),
            "SELECT CASE WHEN TRUE THEN 1 ELSE COALESCE(2,3) END": ("coalesce", "integer"),
            "SELECT (CASE WHEN TRUE THEN ARRAY[1] ELSE a END)[1] FROM (SELECT ARRAY[2] AS a) d":
                ("a", "integer"),
            "SELECT ((ARRAY[[1,2],[3,4]])[1:1])[1][2]": ("array", "integer"),
        }
        for sql, wanted in cases.items():
            with self.subTest(sql=sql):
                self.assertEqual((self.by_sql[sql]["name"], self.by_sql[sql]["type"]), wanted)


class ArraySubscriptLabelProtocolTests(unittest.TestCase):
    def temporary_labels(self, rows):
        temporary = tempfile.TemporaryDirectory()
        self.addCleanup(temporary.cleanup)
        directory = Path(temporary.name)
        (directory / "labels.json").write_text(json.dumps(rows))
        return directory

    def test_exact_two_named_gaps_leave_85_unmodified_label_observations(self):
        rows = json.loads(LABELS.read_text())
        supported = checker.label_cases()
        gaps = {"SELECT NULL::FLOAT", "SELECT (NULL::FLOAT[])[1]"}
        self.assertEqual(checker.LABEL_SYNTAX_GAPS, gaps)
        expected = [row for row in rows if row["sql"] not in gaps]
        self.assertEqual(len(supported), 85)
        for case, row in zip(supported, expected):
            self.assertEqual(case["sql"], row["sql"])
            self.assertEqual(case["output_columns"], [{"name": row["name"]}])
            self.assertEqual(case["postgres_display_type"], row["type"])
            self.assertEqual(case["parameter_types"], "")
            self.assertEqual(case["parameter_values"], [])
            self.assertNotIn("expected_value", case)

    def test_fixture_loader_rejects_lost_duplicates_fields_and_named_gaps(self):
        rows = json.loads(LABELS.read_text())
        missing_name = deepcopy(rows)
        missing_name[0].pop("name")
        absent_gap = deepcopy(rows)
        next(row for row in absent_gap if row["sql"] == "SELECT NULL::FLOAT")["sql"] = "SELECT NULL::REAL AS renamed"
        for changed in (rows[:-1], rows + rows[:1], rows[:-1] + rows[:1], missing_name, absent_gap):
            with self.subTest(count=len(changed)), \
                    patch.object(checker, "FIXTURES", self.temporary_labels(changed)), \
                    self.assertRaises(AssertionError):
                checker.label_cases()

    def test_validity_name_check_requires_one_column_and_preserves_assurance_call(self):
        case = next(row for row in checker.label_cases()
                    if row["sql"] == "SELECT NULL::CHAR(5)")
        report = {"outputColumns": [{"name": "bpchar", "type": "char(5)", "nullable": True}]}
        with patch.object(checker, "assert_report", return_value=report) as check:
            self.assertEqual(checker.label_validity(case), report)
        check.assert_called_once_with(["--assurance", "contract", case["sql"]], "valid", "contract")
        bad = [{}, {"outputColumns": None}, {"outputColumns": {}}, {"outputColumns": []},
               {"outputColumns": [{}, {}]}, {"outputColumns": [{}]},
               {"outputColumns": [{"name": "char"}]}, {"outputColumns": [{"name": "bpchar[]"}]}]
        for changed in bad:
            with self.subTest(report=changed), patch.object(checker, "assert_report", return_value=changed), \
                    self.assertRaises((AssertionError, KeyError)):
                checker.label_validity(case)

    def test_all_270_native_descriptors_include_source_and_rendered_names_and_modifiers(self):
        rows, _ = checker.load_cases()
        labels = checker.label_cases()
        cases = rows + labels
        script, expected = checker.describe_script(cases, [case["sql"] for case in cases])
        self.assertEqual(len(expected), 270)
        self.assertEqual(script.count("\\gdesc"), 270)
        self.assertEqual(expected[100:], [
            f"{case['output_columns'][0]['name']}|{case['postgres_display_type']}"
            for case in labels for _ in range(2)
        ])
        self.assertIn("bpchar|character(5)", expected)
        self.assertIn("numeric|numeric(6,2)", expected)
        self.assertIn("timestamp|timestamp(3) without time zone", expected)
        with self.assertRaisesRegex(AssertionError, "missing canonical"):
            checker.describe_script(cases, [case["sql"] for case in cases[:-1]])

    def test_descriptor_comparison_rejects_missing_renamed_reordered_duplicate_and_wrong_type(self):
        expected = ["int4|integer", "bpchar|character(5)", "numeric|numeric(6,2)"]
        self.assertEqual(checker.validate_descriptors(list(expected), expected), 3)
        bad = [
            expected[:-1], expected + expected[:1], list(reversed(expected)),
            expected[:2] + expected[1:2],
            ["integer|integer", *expected[1:]],
            [expected[0], "bpchar|character", expected[2]],
            [expected[0], expected[1], "numeric|numeric(7,3)"],
            [expected[0], expected[1], "numeric|numeric(6,2) "],
        ]
        for actual in bad:
            with self.subTest(actual=actual), self.assertRaises(AssertionError):
                checker.validate_descriptors(actual, expected)

    def test_float_gaps_require_named_parse_failure_and_cannot_silently_skip(self):
        with patch.object(checker, "assert_report"), patch.object(checker, "parse_failure") as parse:
            checker.boundaries()
        tested = {call.args[0] for call in parse.call_args_list}
        self.assertTrue({"SELECT NULL::FLOAT", "SELECT (NULL::FLOAT[])[1]"} <= tested)
        good = {"status": "invalid", "diagnostic": {"code": "input.parse"}}
        process = subprocess.CompletedProcess([], 1, json.dumps(good), "")
        with patch.object(checker, "invoke", return_value=process):
            checker.parse_failure("SELECT NULL::FLOAT")
        for code, report in ((0, good), (3, {"status": "unsupported", "diagnostic": {"code": "input.parse"}}),
                             (1, {"status": "invalid", "diagnostic": {"code": "other"}})):
            process = subprocess.CompletedProcess([], code, json.dumps(report), "")
            with self.subTest(code=code, report=report), \
                    patch.object(checker, "invoke", return_value=process), self.assertRaises(AssertionError):
                checker.parse_failure("SELECT NULL::FLOAT")

    def exercise_main(self, metadata):
        rows, _ = checker.load_cases()
        row = rows[0]
        label = next(case for case in checker.label_cases() if case["sql"] == "SELECT NULL::CHAR(5)")
        def field(value):
            return NULL if value is None else '"' + value.replace('"', '""') + '"'
        values = "\n".join(
            line for form in ("source", "postgres") for line in (
                checker.marker("exact_types", 1, True, form), '"value","type"',
                ",".join(map(field, [row["expected_value"], row["postgres_type"]]))
            )) + "\n"
        responses = [subprocess.CompletedProcess([], 0, text, "")
                     for text in (values, metadata, "", "16.15\n")]
        with patch.object(checker, "load_cases", return_value=([row], [])), \
                patch.object(checker, "label_cases", return_value=[label]), \
                patch.object(checker, "runtime_cases", return_value=[]), \
                patch.object(checker, "validity"), patch.object(checker, "label_validity") as labels, \
                patch.object(checker, "reject_sqlite"), patch.object(checker, "boundaries", return_value=0), \
                patch.object(checker, "replay", side_effect=lambda _, sql: {"sql": sql}), \
                patch.object(checker, "connection", return_value=nullcontext(["psql"])), \
                patch.object(checker, "run", side_effect=responses) as native, \
                patch("sys.argv", ["checker", "--dsn", "postgresql://unused"]), redirect_stdout(io.StringIO()):
            checker.main()
        labels.assert_called_once_with(label)
        self.assertEqual(len(native.call_args_list), 4)
        for call in native.call_args_list[:3]:
            self.assertIn("ON_ERROR_STOP=1", call.args[0])
            self.assertEqual(call.kwargs["timeout"], 120)

    def test_main_rejects_missing_or_changed_label_descriptors(self):
        rows, _ = checker.load_cases()
        prefix = (f"v|{rows[0]['postgres_display_type']}\n") * 2
        self.exercise_main(prefix + "bpchar|character(5)\nbpchar|character(5)\n")
        for tail in ("", "bpchar|character(5)\n", "char|character(5)\nchar|character(5)\n",
                     "bpchar|character\nbpchar|character\n",
                     "bpchar|character(5)\nbpchar|character(5)\nextra|integer\n"):
            with self.subTest(tail=tail), self.assertRaises(AssertionError):
                self.exercise_main(prefix + tail)


if __name__ == "__main__":
    unittest.main()
