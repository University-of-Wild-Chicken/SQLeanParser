"""Evidence-integrity tests for scalar concatenation and distinct dialect oracles."""
from contextlib import nullcontext, redirect_stdout
from copy import deepcopy
import io
import json
from pathlib import Path
import subprocess
import tempfile
import unittest
from unittest.mock import patch

import check_concatenation_cli as checker
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


class ConcatenationCliTests(unittest.TestCase):
    def fixture_directory(self, rows=None, concrete=None, operators=None):
        directory = tempfile.TemporaryDirectory()
        self.addCleanup(directory.cleanup)
        root = Path(directory.name)
        if rows is not None:
            (root / "synthetic.json").write_text(json.dumps(rows))
        if concrete is not None:
            (root / "concrete.jsonl").write_text("".join(json.dumps(row) + "\n" for row in concrete))
        if operators is not None:
            (root / "operator_signatures.json").write_text(json.dumps(operators))
        return root

    @staticmethod
    def null_case():
        return {
            "id": "null", "sql": "SELECT $1 || $2 AS v;",
            "sqlite_input": "SELECT ?1 || ?2 AS v;", "sqlite_sql": "SELECT ?1 || ?2 AS v;",
            "sqlite_supported": True, "sqlite_value": None,
            "parameter_types": "text?,text", "parameter_values": [None, "x"],
            "output_columns": [{"name": "v", "type": "text", "nullable": True}],
            "postgres_type": "text", "postgres_display_type": "text", "expected_value": None,
        }

    def test_populations_cover_three_outputs_and_distinct_nullable_contracts(self):
        rows, source = checker.load_cases()
        self.assertEqual((len(rows), len(source)), (50, 50))
        self.assertEqual({row["output_columns"][0]["type"] for row in rows}, {"text", "jsonb", "bytea"})
        self.assertEqual({row["output_columns"][0]["nullable"] for row in rows}, {True, False})
        self.assertEqual(sum(row["sqlite_supported"] for row in rows), 25)
        self.assertEqual(sum(row["sqlite_sql"] is not None for row in rows), 15)
        by_shape = {row["shape"]: row for row in rows}
        self.assertEqual(by_shape["jsonb-json-null"]["expected_value"], "[null, 1]")
        self.assertFalse(by_shape["jsonb-json-null"]["output_columns"][0]["nullable"])
        self.assertIsNone(by_shape["jsonb-sql-null"]["expected_value"])
        self.assertTrue(by_shape["jsonb-sql-null"]["output_columns"][0]["nullable"])
        self.assertEqual(by_shape["bytea"]["expected_value"], r"\x61626364")
        self.assertEqual(by_shape["precedence"]["expected_value"], "x7")
        self.assertEqual(by_shape["precedence"]["sqlite_value"], 6)

    def test_loader_rejects_missing_duplicate_metadata_and_parameter_mismatches(self):
        rows, source = checker.load_cases()
        bad = [(rows[:-1], source), (rows, source[:-1])]
        for key in ("id", "sql"):
            changed = deepcopy(rows)
            changed[1][key] = changed[0][key]
            bad.append((changed, source))
        for key, value in (("name", "wrong"), ("type", "integer"), ("nullable", 1)):
            changed = deepcopy(rows)
            changed[0]["output_columns"][0][key] = value
            bad.append((changed, source))
        for mutation in ("arity", "values", "input_slots", "source_slots", "supported", "portable"):
            changed = deepcopy(rows)
            bound = next(row for row in changed if row["parameter_values"] and row["sqlite_sql"])
            if mutation == "arity":
                changed[0]["output_columns"].append(changed[0]["output_columns"][0])
            elif mutation == "values":
                bound["parameter_values"].append("unexpected")
            elif mutation in {"input_slots", "source_slots"}:
                bound["sqlite_input" if mutation == "input_slots" else "sqlite_sql"] = "SELECT ?99 || ?1 AS v;"
            elif mutation == "supported":
                next(row for row in changed if not row["sqlite_supported"])["sqlite_supported"] = True
            else:
                next(row for row in changed if row["sqlite_sql"])["sqlite_sql"] = None
            bad.append((changed, source))
        for changed, concrete in bad:
            with self.subTest(size=len(changed)), \
                    patch.object(checker, "FIXTURES", self.fixture_directory(changed, concrete)), \
                    self.assertRaises(AssertionError):
                checker.load_cases()

    def test_five_native_operators_have_exact_primitive_and_polymorphic_catalog_inputs(self):
        script, expected = checker.operator_script()
        self.assertEqual(expected, [f"{i}|t" for i in range(5)])
        signatures = json.loads((checker.FIXTURES / "operator_signatures.json").read_text())
        self.assertEqual({(row["left"], row["right"], row["output"], row["function"]) for row in signatures}, {
            ("text", "text", "text", "textcat"),
            ("text", "anynonarray", "text", "textanycat"),
            ("anynonarray", "text", "text", "anytextcat"),
            ("jsonb", "jsonb", "jsonb", "jsonb_concat"),
            ("bytea", "bytea", "bytea", "byteacat"),
        })
        for line, row in zip(script.splitlines(), signatures):
            for clause in (
                    "o.oprnamespace='pg_catalog'::regnamespace", "o.oprname='||'",
                    f"o.oprleft='{row['left']}'::regtype", f"o.oprright='{row['right']}'::regtype",
                    f"o.oprresult='{row['output']}'::regtype", f"p.prorettype='{row['output']}'::regtype",
                    f"p.proargtypes[0]='{row['left']}'::regtype",
                    f"p.proargtypes[1]='{row['right']}'::regtype",
                    f"p.proname='{row['function']}'", "p.pronamespace='pg_catalog'::regnamespace",
                    "p.proisstrict", "NOT p.proretset", "p.pronargs=2", "p.prokind='f'"):
                self.assertIn(clause, line)
        # Catalog strictness is established separately from case-specific nullable output.
        self.assertNotIn("nullable", script)

    def test_operator_manifest_cannot_omit_duplicate_or_change_a_family(self):
        rows = json.loads((checker.FIXTURES / "operator_signatures.json").read_text())
        bad = [rows[:-1], rows + rows[:1], rows[:-1] + rows[:1]]
        for key, value in (("left", "anyarray"), ("output", "boolean"),
                           ("function", "concat"), ("operator", "+")):
            changed = deepcopy(rows)
            changed[0][key] = value
            bad.append(changed)
        for changed in bad:
            with self.subTest(changed=changed[0]), \
                    patch.object(checker, "FIXTURES", self.fixture_directory(operators=changed)), \
                    self.assertRaises(AssertionError):
                checker.operator_script()

    def test_prepared_bindings_and_result_descriptors_remain_separate(self):
        row = self.null_case()
        script, expected = checker.database_script([row], [row["sql"]])
        self.assertIn("PREPARE exact_type_parameters (text,text)", script)
        self.assertIn("SELECT $1 || $2 AS v", script)
        self.assertIn("EXECUTE exact_type_parameters (NULL, ''''x'''')", script)
        self.assertTrue(all(value == (2, [[None, "text"]]) for value in expected.values()))
        description, metadata = checker.describe_script([row], [row["sql"]])
        self.assertIn("PREPARE array_description (text,text)", description)
        self.assertIn("EXECUTE array_description(NULL, 'x')", description)
        self.assertEqual(description.count("\\gdesc"), 2)
        self.assertNotIn("RETURNS TABLE", description)
        self.assertEqual(metadata, ["v|text", "v|text"])
        with patch("check_array_types_cli.assert_report") as report:
            checker.validity(row)
        self.assertEqual(report.call_args.args[0],
                         ["--assurance", "contract", "--param-types", "text?,text", row["sql"]])
        self.assertEqual(report.call_args.args[3], (("v", "text", True),))

    def test_sql_null_json_null_and_text_null_do_not_share_a_result_oracle(self):
        row = self.null_case()
        _, expected = checker.database_script([row], [row["sql"]])
        good = checker.parse_results(transcript("exact_types", 1, [None, "text"]))
        self.assertEqual(checker.validate_results(good, expected), 2)
        for value in ("null", "NULL", "[null, 1]", NULL, ""):
            actual = checker.parse_results(transcript("exact_types", 1, [value, "text"]))
            with self.subTest(value=value), self.assertRaises(AssertionError):
                checker.validate_results(actual, expected)
        expected = {"json": (2, [["[null, 1]", "jsonb"]])}
        for actual in ({"json": (2, [[None, "jsonb"]])}, {"json": (2, [["[null, 1]", "text"]])}):
            with self.subTest(actual=actual), self.assertRaises(AssertionError):
                checker.validate_results(actual, expected)

    def test_exact_text_jsonb_and_bytea_outputs_cannot_substitute_for_each_other(self):
        expected = {name: (2, [[value, name]]) for name, value in (
            ("text", r"\x61"), ("bytea", r"\x61"), ("jsonb", '{"a": 1}'))}
        self.assertEqual(checker.validate_results(deepcopy(expected), expected), 3)
        for field, value in ((0, "a"), (1, "text")):
            actual = deepcopy(expected)
            actual["bytea"][1][0][field] = value
            with self.subTest(field=field), self.assertRaises(AssertionError):
                checker.validate_results(actual, expected)

    def test_sqlite_precedence_is_an_independent_integer_result(self):
        rows, _ = checker.load_cases()
        row = next(row for row in rows if row["shape"] == "precedence")
        canonical = "SELECT (('x' || 1) + (2 * 3)) AS v;"
        self.assertEqual(checker.sqlite_observations([row], [canonical]), 2)
        for wrong_value in ("x7", "6", None):
            wrong = dict(row, sqlite_value=wrong_value)
            with self.subTest(value=wrong_value), self.assertRaises(AssertionError):
                checker.sqlite_observations([wrong], [canonical])
        with self.assertRaises(AssertionError):
            checker.sqlite_observations([row], ["SELECT ('x' || (1 + (2 * 3))) AS v;"])

    def test_sqlite_jsonb_binding_is_text_concatenation_without_postgresql_merge(self):
        rows, _ = checker.load_cases()
        row = next(row for row in rows if row["shape"] == "jsonb-binding")
        canonical = """SELECT (?1 || '{"b":2}') AS v;"""
        self.assertEqual(checker.sqlite_observations([row], [canonical]), 2)
        self.assertEqual(row["sqlite_value"], '{"a":1}{"b":2}')
        wrong = dict(row, sqlite_value=row["expected_value"])
        with self.assertRaises(AssertionError):
            checker.sqlite_observations([wrong], [canonical])

    def test_numbered_and_anonymous_bindings_keep_order_identity_and_repetition(self):
        row = dict(self.null_case(), parameter_types="int,text", parameter_values=[1, "x"],
                   sqlite_sql=None, sqlite_value="x1x")
        canonical = "SELECT (?2 || ?1) || ?2 AS v;"
        self.assertEqual(checker.sqlite_bindings(canonical, [1, "x"]), {"1": 1, "2": "x"})
        self.assertEqual(checker.sqlite_observations([row], [canonical]), 1)
        with self.assertRaises(AssertionError):
            checker.sqlite_observations([row], ["SELECT (?1 || ?2) || ?1 AS v;"])
        row.update(sql="SELECT ? || ? || ? AS v;", parameter_types="text,text,text",
                   parameter_values=["left", "middle", "right"])
        script, _ = checker.describe_script([row], [row["sql"]])
        self.assertIn("SELECT $1 || $2 || $3 AS v;", script)
        self.assertIn("EXECUTE array_description('left', 'middle', 'right')", script)

    def test_missing_rendering_wrong_label_extra_rows_or_excluded_success_fail(self):
        row = self.null_case()
        self.assertEqual(checker.sqlite_observations([row], [row["sqlite_sql"]]), 2)
        for canonical in (None, "SELECT ?1 || ?2 AS wrong;",
                          "SELECT ?1 || ?2 AS v UNION ALL SELECT NULL;"):
            with self.subTest(canonical=canonical), self.assertRaises(AssertionError):
                checker.sqlite_observations([row], [canonical])
        with self.assertRaises(AssertionError):
            checker.sqlite_observations([row], [])
        excluded = dict(row, sqlite_supported=False, sqlite_sql=None)
        self.assertEqual(checker.sqlite_observations([excluded], [None]), 0)
        with self.assertRaises(AssertionError):
            checker.sqlite_observations([excluded], [row["sqlite_sql"]])

    def test_sqlite_replay_uses_dialect_input_and_requires_paired_rejection_evidence(self):
        row = self.null_case()
        with patch.object(checker, "replay", return_value={"sql": "rendered"}) as replay:
            self.assertEqual(checker.sqlite_render(row), "rendered")
        replay.assert_called_once_with("sqlite", row["sqlite_input"])
        row["sqlite_supported"] = False
        for code, status, diagnostic in ((1, "invalid", "input.parse"),
                                        (3, "unsupported", "coverage.sqlite.type")):
            result = subprocess.CompletedProcess([], code, json.dumps({
                "status": status, "diagnostic": {"code": diagnostic}}), "")
            with patch.object(checker, "invoke", return_value=result) as invoke:
                self.assertIsNone(checker.sqlite_render(row))
            self.assertEqual(invoke.call_args.kwargs["stdin"], row["sqlite_input"])
        for code, status, diagnostic in ((0, "rendered", "input.parse"),
                                         (1, "invalid", "coverage.sqlite.type"),
                                         (3, "unsupported", "input.parse"),
                                         (3, "unsupported", "resource.depth")):
            result = subprocess.CompletedProcess([], code, json.dumps({
                "status": status, "diagnostic": {"code": diagnostic}}), "")
            with self.subTest(diagnostic=diagnostic), \
                    patch.object(checker, "invoke", return_value=result), self.assertRaises(AssertionError):
                checker.sqlite_render(row)

    def test_absent_canonical_evidence_cannot_be_silently_zipped(self):
        for function, rows in ((checker.database_script, [self.null_case()]),
                               (checker.describe_script, [self.null_case()]),
                               (checker.error_script, checker.runtime_cases())):
            with self.subTest(function=function.__name__), self.assertRaises(AssertionError):
                function(rows, [])

    def test_runtime_success_is_distinct_from_nonnullable_static_result(self):
        rows = checker.runtime_cases()
        self.assertEqual([row["sqlstate"] for row in rows], ["22P02", "22023", "22P02", "22003", "22012"])
        self.assertTrue(all(not row["output_columns"][0]["nullable"] for row in rows))
        script, expected = checker.error_script(rows, [row["sql"] for row in rows])
        self.assertEqual(len(expected), 10)
        self.assertEqual(script.count("RETURN ''unexpected-success''"), 10)
        self.assertEqual(script.count("RETURN SQLSTATE"), 10)
        for index, row in enumerate(rows, 1):
            for form in ("source", "postgres"):
                self.assertEqual(expected[checker.marker("concatenation_error", index, True, form)],
                                 (1, [[row["sqlstate"]]]))

    def exercise_main(self, *, values=None, metadata=None, operators=None, errors=None):
        row = self.null_case()
        concrete = {"sql": "SELECT secret || secret FROM never_execute_concrete;"}
        runtime, label = checker.runtime_cases()[0], checker.label_cases()[3]
        values = transcript("exact_types", 1, [None, "text"]) if values is None else values
        metadata = "v|text\n" * 2 + "?column?|jsonb\n" * 2 if metadata is None else metadata
        operators = "\n".join(f"{i}|t" for i in range(5)) + "\n" if operators is None else operators
        errors = transcript("concatenation_error", 1, ["22P02"]) if errors is None else errors
        results = [subprocess.CompletedProcess(["psql"], 0, stdout, "") for stdout in
                   (values, metadata, operators, errors, "16.15\n")]
        with patch.object(checker, "load_cases", return_value=([row], [concrete])), \
                patch.object(checker, "runtime_cases", return_value=[runtime]), \
                patch.object(checker, "label_cases", return_value=[label]), \
                patch.object(checker, "validity") as validity, \
                patch.object(checker, "replay", side_effect=lambda mode, sql: {"sql": sql}) as replay, \
                patch.object(checker, "sqlite_render", return_value=row["sqlite_sql"]), \
                patch.object(checker, "boundaries", return_value=0), \
                patch.object(checker, "connection", return_value=nullcontext(["psql"])), \
                patch.object(checker, "run", side_effect=results) as run, \
                patch("sys.argv", ["check_concatenation_cli.py", "--dsn", "unused"]), \
                redirect_stdout(io.StringIO()):
            checker.main()
            return run.call_args_list, validity.call_args_list, replay.call_args_list

    def test_pipeline_executes_only_authored_queries_with_fail_fast_native_commands(self):
        calls, validity, replays = self.exercise_main()
        self.assertEqual(len(calls), 5)
        for call in calls[:4]:
            self.assertIn("ON_ERROR_STOP=1", call.args[0])
            self.assertEqual(call.kwargs["timeout"], 120)
            self.assertNotIn("never_execute_concrete", call.kwargs["input"])
        self.assertEqual(len(validity), 3)
        self.assertEqual(sum("never_execute_concrete" in call.args[1] for call in replays), 2)

    def test_pipeline_rejects_missing_renamed_or_wrong_type_result_descriptors(self):
        for metadata in ("", "v|text\n" * 2 + "?column?|jsonb\n",
                         "v|text\n" * 2 + "?column?|text\n" * 2,
                         "wrong|text\n" * 2 + "?column?|jsonb\n" * 2):
            with self.subTest(metadata=metadata), self.assertRaises(AssertionError):
                self.exercise_main(metadata=metadata)

    def test_pipeline_rejects_missing_false_duplicate_and_reordered_catalog_evidence(self):
        expected = [f"{i}|t" for i in range(5)]
        for lines in ([], expected[:-1], ["0|f"] + expected[1:], expected + expected[:1],
                      [expected[1], expected[0]] + expected[2:]):
            with self.subTest(lines=lines), self.assertRaises(AssertionError):
                self.exercise_main(operators="\n".join(lines) + "\n")

    def test_pipeline_rejects_wrong_value_oid_or_missing_null_evidence(self):
        for values in ("", transcript("exact_types", 1, ["null", "text"]),
                       transcript("exact_types", 1, [None, "jsonb"])):
            with self.subTest(values=values), self.assertRaises(AssertionError):
                self.exercise_main(values=values)

    def test_pipeline_rejects_wrong_error_or_unexpected_success(self):
        for state in ("unexpected-success", "00000", "57014", "22023"):
            with self.subTest(state=state), self.assertRaises(AssertionError):
                self.exercise_main(errors=transcript("concatenation_error", 1, [state]))
        with self.assertRaises(AssertionError):
            self.exercise_main(errors="")

    def test_wrong_result_arity_count_extra_case_and_duplicate_markers_fail(self):
        expected = {"case": (2, [[None, "text"]])}
        for actual in ({}, {**expected, "extra": expected["case"]}, {"case": (1, [[None]])},
                       {"case": (2, [[None, "text"], [None, "text"]])}):
            with self.subTest(actual=actual), self.assertRaises(AssertionError):
                checker.validate_results(actual, expected)
        output = transcript("exact_types", 1, [None, "text"])
        with self.assertRaisesRegex(ValueError, "Duplicate case marker"):
            checker.parse_results(output + output)

    def test_parser_and_semantic_boundaries_keep_their_exact_classifications(self):
        good = subprocess.CompletedProcess([], 1, json.dumps({
            "status": "invalid", "diagnostic": {"code": "input.parse"}}), "")
        with patch.object(checker, "assert_report", return_value={"outputCollations": ["default"]}) as reports, \
                patch.object(checker, "invoke", return_value=good) as invoke:
            self.assertEqual(checker.boundaries(), 17)
        self.assertEqual(len(invoke.call_args_list), 3)
        self.assertTrue(all(call.args[0][:2] == ["--render-assurance", "identity"]
                            for call in invoke.call_args_list))
        self.assertEqual(sum(call.args[1] == "invalid" for call in reports.call_args_list), 8)
        self.assertEqual(sum(call.args[1] == "unsupported" for call in reports.call_args_list), 1)
        self.assertEqual(sum(call.args[1] == "valid" for call in reports.call_args_list), 4)
        for code, status, diagnostic in ((0, "rendered", "input.parse"),
                                         (1, "invalid", "resource.depth"),
                                         (3, "unsupported", "input.parse")):
            result = subprocess.CompletedProcess([], code, json.dumps({
                "status": status, "diagnostic": {"code": diagnostic}}), "")
            with self.subTest(status=status), patch.object(checker, "assert_report", return_value={"outputCollations": ["default"]}), \
                    patch.object(checker, "invoke", return_value=result), self.assertRaises(AssertionError):
                checker.boundaries()


if __name__ == "__main__":
    unittest.main()
