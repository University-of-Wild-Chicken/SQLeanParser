"""Fail-closed evidence for stateful SQL92 unknown-target resolution."""
from collections import Counter
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
import check_set_order_sequences as checker


class SetOrderSequenceTests(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        cls.rows = checker.load_cases()

    def test_fixed_native_sequence_anchors_and_exact_unknown_metadata(self):
        self.assertEqual(len(self.rows), 80)
        self.assertEqual(Counter(r["expected_status"] for r in self.rows),
                         {"valid": 60, "invalid": 20})
        failed = {"1,x", "2,x", "x,x", "1,x,2", "2,x,1"}
        for row in self.rows:
            unknown = row["expression_kind"] in {"unknown-null", "unknown-string"}
            valid = not (unknown and row["order_sql"] in failed)
            self.assertEqual(row["expected_status"], "valid" if valid else "invalid")
            self.assertEqual(row["postgres_sqlstate"], "00000" if valid else "42702")
            self.assertEqual(row["diagnostic"], None if valid else "ambiguous_output")
            self.assertIs(type(row["set_operand"]), bool)
            self.assertEqual(row["source_kind"], "synthetic")
            self.assertEqual(row["sql"].startswith("("), row["set_operand"])
            if valid:
                nullable = row["set_operand"] or row["expression_kind"] in {"unknown-null", "known-text"}
                type_ = "int32" if row["expression_kind"] == "known-integer" else "text"
                self.assertEqual(row["output_columns"], [
                    {"name": "x", "type": type_, "nullable": nullable}] * 2)
                self.assertEqual(row["postgres_columns"],
                                 [["x", "integer" if type_ == "int32" else "text"]] * 2)
            else:
                self.assertIsNone(row["output_columns"])
                self.assertIsNone(row["postgres_columns"])

    def test_registry_rejects_missing_reordered_and_relabelled_evidence(self):
        for mutation in ("missing", "order", "duplicate", "sql", "source_kind",
                         "expected_status", "postgres_sqlstate", "diagnostic",
                         "output_columns", "postgres_columns", "set_operand"):
            rows = deepcopy(self.rows)
            if mutation == "missing":
                rows.pop()
            elif mutation == "order":
                rows.reverse()
            elif mutation == "duplicate":
                rows[1] = deepcopy(rows[0])
            else:
                rows[0][mutation] = "changed"
            with tempfile.TemporaryDirectory() as directory:
                fixture = Path(directory) / "cases.json"
                fixture.write_text(json.dumps(rows))
                with self.subTest(mutation=mutation), patch.object(checker, "FIXTURE", fixture), \
                        self.assertRaises(AssertionError):
                    checker.load_cases()

    def test_static_checker_passes_literal_queries_and_exact_ordered_outputs(self):
        for row in self.rows:
            with patch.object(checker, "assert_report", return_value={
                    "diagnostic": {"code": row["diagnostic"]}}) as report:
                checker.static_check(row)
            expected = None if row["output_columns"] is None else tuple(
                (c["name"], c["type"], c["nullable"]) for c in row["output_columns"])
            report.assert_called_once_with(["--assurance", "contract", row["sql"]],
                                           row["expected_status"], "contract", expected)
        rejected = next(r for r in self.rows if r["expected_status"] == "invalid")
        with patch.object(checker, "assert_report", return_value={"diagnostic": {"code": "wrong"}}), \
                self.assertRaises(AssertionError):
            checker.static_check(rejected)

    def test_exact_certificate_and_rejection_protocol_cannot_be_substituted(self):
        for row in (self.rows[0], self.rows[2], self.rows[41]):
            valid = row["expected_status"] == "valid"
            good = {"status": row["expected_status"], "assurance": "declarative",
                    "profile": assurance.PROFILES["contract"],
                    "evidence": "declarative-derivation" if valid else "none"}
            if valid:
                good.update(catalogUnchanged=True, typePrecision="exact",
                            outputColumns=deepcopy(row["output_columns"]))
            else:
                good["diagnostic"] = {"code": row["diagnostic"], "message": "duplicate sort label"}
            mutations = [None, "exit", "status", "profile", "evidence"]
            mutations += ["name", "type", "nullable", "missing_column", "catalog", "precision"] \
                if valid else ["diagnostic", "message", "output"]
            for mutation in mutations:
                report = deepcopy(good)
                code = assurance.EXIT_CODES[row["expected_status"]]
                if mutation == "exit":
                    code = 4
                elif mutation in {"status", "profile", "evidence"}:
                    report[mutation] = "wrong"
                elif mutation in {"name", "type"}:
                    report["outputColumns"][0][mutation] = "wrong"
                elif mutation == "nullable":
                    report["outputColumns"][0]["nullable"] = int(report["outputColumns"][0]["nullable"])
                elif mutation == "missing_column":
                    report["outputColumns"].pop()
                elif mutation == "catalog":
                    report["catalogUnchanged"] = False
                elif mutation == "precision":
                    report["typePrecision"] = "family"
                elif mutation == "diagnostic":
                    report["diagnostic"]["code"] = "order_constant"
                elif mutation == "message":
                    del report["diagnostic"]["message"]
                elif mutation == "output":
                    report["outputColumns"] = []
                with self.subTest(id=row["id"], mutation=mutation), patch.object(
                        assurance, "invoke", return_value=subprocess.CompletedProcess(
                            [], code, json.dumps(report), "")):
                    if mutation is None:
                        checker.static_check(row)
                    else:
                        with self.assertRaises(AssertionError):
                            checker.static_check(row)

    def test_native_script_only_prepares_and_describes_fixed_authored_queries(self):
        canonical = [r["sql"] + " /* canonical */" for r in self.rows]
        script, expected = checker.native_script(self.rows, canonical)
        self.assertEqual(len(expected), 520)
        self.assertEqual(script.count(" || pg_temp.sequence_analysis("), 160)
        self.assertEqual(script.count("PREPARE descriptor_probe AS "), 120)
        self.assertEqual(script.count("EXECUTE descriptor_probe\\gdesc"), 120)
        self.assertNotIn("EXECUTE descriptor_probe;", script)
        self.assertNotIn("EXPLAIN", script)
        self.assertIn("SET LOCAL statement_timeout = '5s';", script)
        self.assertTrue(script.startswith("BEGIN;\n") and script.endswith("ROLLBACK;"))
        calls = [line for line in script.splitlines() if " || pg_temp.sequence_analysis(" in line]
        for index, row in enumerate(self.rows):
            for offset, layout in enumerate(("source", "canonical")):
                sql = row["sql"] if layout == "source" else canonical[index]
                self.assertEqual(calls[index * 2 + offset],
                                 "SELECT " + checker.sql_literal(f"analysis:{row['id']}:{layout}:") +
                                 " || pg_temp.sequence_analysis(" + checker.sql_literal(sql) + ");")
        with self.assertRaises(AssertionError):
            checker.native_script(self.rows, canonical[:-1])

    def test_native_markers_states_labels_types_and_completeness_are_exact(self):
        _, expected = checker.native_script(self.rows, [r["sql"] for r in self.rows])
        checker.validate_native("\n".join(expected) + "\n", expected)
        for change in ("missing", "extra", "order", "id", "state", "name", "type", "spacing"):
            observed = expected.copy()
            if change == "missing":
                observed.pop()
            elif change == "extra":
                observed.append("x|text")
            elif change == "order":
                observed[0], observed[1] = observed[1], observed[0]
            elif change == "id":
                observed[0] = observed[0].replace("001", "002")
            elif change == "state":
                observed[0] = observed[0].replace("00000", "42702")
            elif change == "name":
                observed[-1] = "changed|text"
            elif change == "type":
                observed[-1] = "x|integer"
            else:
                observed[0] += " "
            with self.subTest(change=change), self.assertRaises(AssertionError):
                checker.validate_native("\n".join(observed) + "\n", expected)

    def exercise_main(self, *, mutation=None, fail_static=False, fail_renderer=False, version="160015"):
        canonical = [r["sql"] + " /* canonical */" for r in self.rows]
        _, expected = checker.native_script(self.rows, canonical)
        if mutation == "missing":
            expected.pop()
        elif mutation == "state":
            expected[0] = expected[0].replace("00000", "42702")
        elif mutation == "descriptor":
            expected[-1] = "x|integer"
        def rendering(mode, sql):
            if fail_renderer:
                raise AssertionError("missing structural certificate")
            return {"sql": sql + " /* canonical */" if mode == "postgres" else sql}
        output = io.StringIO()
        with patch.object(checker, "static_check",
                          side_effect=AssertionError("wrong typing evidence") if fail_static else None) as static, \
                patch.object(checker, "replay", side_effect=rendering) as replay, \
                patch.object(checker, "connection", return_value=nullcontext(["psql"])) as connection, \
                patch.object(checker, "run", side_effect=[
                    subprocess.CompletedProcess([], 0, version + "\n", ""),
                    subprocess.CompletedProcess([], 0, "\n".join(expected) + "\n", "")]) as run, \
                patch("sys.argv", ["check_set_order_sequences.py", "--local-bin", "/native"]), \
                redirect_stdout(output):
            try:
                checker.main()
            except AssertionError:
                if fail_static or fail_renderer:
                    connection.assert_not_called()
                    run.assert_not_called()
                raise
        return output.getvalue(), static, replay, run

    def test_main_requires_all_static_and_renderer_evidence_before_native_analysis(self):
        output, static, replay, run = self.exercise_main()
        self.assertEqual([c.args[0] for c in static.call_args_list], self.rows)
        self.assertEqual([c.args for c in replay.call_args_list],
                         [(mode, r["sql"]) for r in self.rows for mode in ("identity", "postgres")])
        self.assertEqual(len(run.call_args_list), 2)
        self.assertEqual(run.call_args_list[1].kwargs["timeout"], 120)
        self.assertIn("80 authored sort sequences", output)
        self.assertIn("160 source/canonical PREPARE outcomes", output)
        self.assertIn("120 prepared result descriptions", output)
        self.assertIn("no query values or downloaded source SQL are executed", output)

    def test_main_fails_on_incomplete_wrong_or_wrong_version_native_evidence(self):
        for options in ({"mutation": "missing"}, {"mutation": "state"},
                        {"mutation": "descriptor"}, {"fail_static": True},
                        {"fail_renderer": True}, {"version": "170007"}):
            with self.subTest(options=options), self.assertRaises(AssertionError):
                self.exercise_main(**options)


if __name__ == "__main__":
    unittest.main()
