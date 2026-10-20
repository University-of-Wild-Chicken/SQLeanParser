"""Frozen SQL92 cases and fail-closed analysis-only observation protocols."""
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
import check_ordering_constants_cli as checker


class OrderingConstantsCliTests(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        cls.rows = checker.load_cases()

    def case(self, expression):
        return next(r for r in self.rows if r["sql"] == "SELECT 11 AS x,22 AS y ORDER BY " + expression)

    def test_frozen_population_and_independent_sql92_anchors(self):
        self.assertEqual(len(self.rows), 108)
        self.assertEqual(Counter(r["expected_status"] for r in self.rows),
                         {"valid": 59, "invalid": 45, "unsupported": 4})
        self.assertTrue(all(r["source_kind"] == "synthetic" for r in self.rows))
        anchors = {
            "0": ("invalid", "42P10", "order_position"),
            "-0": ("invalid", "42P10", "order_position"),
            "+0": ("valid", "00000", None),
            "-(-2)": ("valid", "00000", None),
            "-(-3)": ("invalid", "42P10", "order_position"),
            "-(+1)": ("valid", "00000", None),
            "((NULL))": ("invalid", "42601", "order_constant"),
            "TRUE": ("invalid", "42601", "order_constant"),
            "'1'": ("invalid", "42601", "order_constant"),
            "1.0": ("invalid", "42601", "order_constant"),
            "+1.0": ("valid", "00000", None),
            "2147483647": ("invalid", "42P10", "order_position"),
            "2147483648": ("invalid", "42601", "order_constant"),
            "-2147483648": ("invalid", "42601", "order_constant"),
            "-(-2147483648)": ("invalid", "42601", "order_constant"),
            "+2147483648": ("valid", "00000", None),
            "NULL::INTEGER": ("valid", "00000", None),
            "-1.0::NUMERIC": ("valid", "00000", None),
            "ROW(1,2)": ("unsupported", "00000", None),
            "-'1'": ("unsupported", "42725", None),
            "+'1'": ("unsupported", "00000", None),
        }
        for expression, expected in anchors.items():
            row = self.case(expression)
            self.assertEqual(tuple(row[k] for k in
                             ("expected_status", "postgres_sqlstate", "diagnostic")), expected)
        declared = [r for r in self.rows if r["parameter_types"]]
        self.assertEqual([(r["sql"], r["parameter_types"]) for r in declared],
                         [("SELECT 11 AS x,22 AS y ORDER BY $1", "int")])

    def test_digest_rejects_missing_reordered_or_corrupted_registry(self):
        for mutation in ("missing", "duplicate", "order", "id", "sql", "source_kind",
                         "parameter_types", "expected_status", "postgres_sqlstate",
                         "diagnostic", "extra"):
            rows = deepcopy(self.rows)
            if mutation == "missing":
                rows.pop()
            elif mutation == "duplicate":
                rows[1] = deepcopy(rows[0])
            elif mutation == "order":
                rows.reverse()
            elif mutation == "extra":
                rows[0]["runtime_validity"] = True
            else:
                rows[0][mutation] = "corrupted"
            with tempfile.TemporaryDirectory() as directory:
                fixture = Path(directory) / "cases.json"
                fixture.write_text(json.dumps(rows))
                with self.subTest(mutation=mutation), patch.object(checker, "FIXTURE", fixture), \
                        self.assertRaises(AssertionError):
                    checker.load_cases()
        # Formatting is immaterial; exact decoded metadata is the hashed input.
        with tempfile.TemporaryDirectory() as directory:
            fixture = Path(directory) / "cases.json"
            fixture.write_text(json.dumps(self.rows, separators=(",", ":")))
            with patch.object(checker, "FIXTURE", fixture):
                self.assertEqual(checker.load_cases(), self.rows)

    def test_static_calls_preserve_exact_queries_declarations_and_output_positions(self):
        for row in self.rows:
            with patch.object(checker, "assert_report", return_value={
                    "diagnostic": {"code": row["diagnostic"]}}) as report:
                checker.static_check(row)
            arguments = ["--assurance", "contract"]
            if row["parameter_types"]:
                arguments += ["--param-types", row["parameter_types"]]
            columns = (("x", "int32", False), ("y", "int32", False)) \
                if row["expected_status"] == "valid" else None
            report.assert_called_once_with(
                [*arguments, row["sql"]], row["expected_status"], "contract", columns)

    def test_static_reports_require_exact_status_evidence_metadata_and_diagnostic(self):
        for expression in ("+0", "0", "NULL", "ROW(1,2)"):
            row = self.case(expression)
            status = row["expected_status"]
            good = {"status": status, "assurance": "declarative",
                    "profile": assurance.PROFILES["contract"],
                    "evidence": "declarative-derivation" if status == "valid" else "none"}
            if status == "valid":
                good.update(catalogUnchanged=True, typePrecision="exact", outputColumns=[
                    {"name": name, "type": "int32", "nullable": False} for name in ("x", "y")])
            else:
                good["diagnostic"] = {"code": row["diagnostic"] or "row_value",
                                      "message": "explicit classification"}
            mutations = [None, "exit", "status", "assurance", "profile", "evidence"]
            mutations += (["column_name", "column_type", "column_order", "column_nullable", "precision"]
                          if status == "valid" else ["missing_diagnostic", "missing_message", "output"])
            if row["diagnostic"]:
                mutations.append("wrong_diagnostic")
            for mutation in mutations:
                report, exit_code = deepcopy(good), assurance.EXIT_CODES[status]
                if mutation == "exit":
                    exit_code = 4
                elif mutation in {"status", "assurance", "profile", "evidence"}:
                    report[mutation] = "wrong"
                elif mutation == "column_name":
                    report["outputColumns"][0]["name"] = "renamed"
                elif mutation == "column_type":
                    report["outputColumns"][0]["type"] = "text"
                elif mutation == "column_order":
                    report["outputColumns"].reverse()
                elif mutation == "column_nullable":
                    report["outputColumns"][0]["nullable"] = 0
                elif mutation == "precision":
                    report["typePrecision"] = "family"
                elif mutation == "missing_diagnostic":
                    del report["diagnostic"]
                elif mutation == "missing_message":
                    del report["diagnostic"]["message"]
                elif mutation == "wrong_diagnostic":
                    report["diagnostic"]["code"] = "operator_signature"
                elif mutation == "output":
                    report["outputColumns"] = []
                with self.subTest(expression=expression, mutation=mutation), patch.object(
                        assurance, "invoke", return_value=subprocess.CompletedProcess(
                            [], exit_code, json.dumps(report), "")):
                    if mutation is None:
                        checker.static_check(row)
                    else:
                        with self.assertRaises(AssertionError):
                            checker.static_check(row)

    def test_analysis_script_has_exact_pairs_preserves_tokens_and_only_prepares(self):
        canonical = [r["sql"] + " /* canonical */" for r in self.rows]
        script, expected = checker.analysis_script(self.rows, canonical)
        self.assertEqual(expected, [r["postgres_sqlstate"] for r in self.rows for _ in range(2)])
        self.assertEqual(len(expected), 216)
        calls = [line for line in script.splitlines()
                 if line.startswith("SELECT pg_temp.sort_analysis(")]
        self.assertEqual(len(calls), 216)
        for index, row in enumerate(self.rows):
            declarations = " (" + row["parameter_types"] + ")" if row["parameter_types"] else ""
            for offset, sql in enumerate((row["sql"], canonical[index])):
                self.assertEqual(calls[2 * index + offset], "SELECT pg_temp.sort_analysis(" +
                                 checker.sql_literal(sql) + "," + checker.sql_literal(declarations) + ");")
        self.assertIn("EXECUTE 'PREPARE sort_probe' || declarations || ' AS ' || q", script)
        self.assertIn("DEALLOCATE sort_probe; RETURN '00000'", script)
        self.assertIn("SET LOCAL statement_timeout = '5s';", script)
        self.assertNotIn("EXECUTE sort_probe", script)
        self.assertNotIn("EXPLAIN", script)
        self.assertTrue(script.startswith("BEGIN;\n") and script.endswith("ROLLBACK;"))
        with self.assertRaises(AssertionError):
            checker.analysis_script(self.rows, canonical[:-1])
        marker = deepcopy(self.case("$1"))
        marker["sql"] = "SELECT 11 AS x,22 AS y ORDER BY ? /* ? and $9 are comments */"
        observed, _ = checker.analysis_script([marker], [marker["sql"]])
        self.assertEqual(observed.count("ORDER BY $1 /* ? and $9 are comments */"), 2)
        self.assertEqual(observed.count(",' (int)');"), 2)

    def test_native_validation_rejects_missing_extra_reordered_and_wrong_sqlstates(self):
        _, expected = checker.analysis_script(self.rows, [r["sql"] for r in self.rows])
        checker.validate_analysis("\n".join(expected) + "\n", expected)
        reordered = expected.copy()
        reordered[0], reordered[4] = reordered[4], reordered[0]
        wrong = expected.copy()
        wrong[4] = "00000"
        for observed in (expected[:-1], expected + ["00000"], reordered, wrong,
                         [""] + expected, [" " + expected[0]] + expected[1:],
                         ["42P10 " if x == "42P10" else x for x in expected]):
            with self.subTest(observed=observed[:5]), self.assertRaises(AssertionError):
                checker.validate_analysis("\n".join(observed) + "\n", expected)

    def exercise_main(self, outcomes=None, *, static_error=False, renderer_error=False):
        expected = [r["postgres_sqlstate"] for r in self.rows for _ in range(2)]
        observed = expected if outcomes is None else outcomes
        def rendering(mode, sql):
            if renderer_error:
                raise AssertionError("missing renderer certificate")
            return {"sql": sql + " /* canonical */" if mode == "postgres" else sql}
        output = io.StringIO()
        with patch.object(checker, "static_check",
                          side_effect=AssertionError("wrong static evidence") if static_error else None) as static, \
                patch.object(checker, "replay", side_effect=rendering) as replay, \
                patch.object(checker, "connection", return_value=nullcontext(["psql"])) as connection, \
                patch.object(checker, "run", side_effect=[
                    subprocess.CompletedProcess([], 0, "\n".join(observed) + "\n", ""),
                    subprocess.CompletedProcess([], 0, "16.15\n", "")]) as run, \
                patch("sys.argv", ["check_ordering_constants_cli.py", "--local-bin", "/native"]), \
                redirect_stdout(output):
            try:
                checker.main()
            except AssertionError:
                if static_error or renderer_error:
                    connection.assert_not_called()
                    run.assert_not_called()
                raise
        return output.getvalue(), static, replay, run

    def test_main_checks_all_authored_static_and_renderer_evidence_before_analysis(self):
        output, static, replay, run = self.exercise_main()
        self.assertEqual([c.args[0] for c in static.call_args_list], self.rows)
        self.assertEqual([c.args for c in replay.call_args_list],
                         [(mode, r["sql"]) for r in self.rows for mode in ("identity", "postgres")])
        self.assertEqual(len(run.call_args_list), 2)
        self.assertEqual(run.call_args_list[0].kwargs["timeout"], 120)
        script = run.call_args_list[0].kwargs["input"]
        self.assertEqual(script.count("SELECT pg_temp.sort_analysis("), 216)
        self.assertEqual(script.count("/* canonical */"), 108)
        self.assertIn("108 authored ORDER BY boundaries", output)
        self.assertIn("216 source/canonical PREPARE outcomes", output)
        self.assertIn("no downloaded SQL is executed", output)

    def test_main_fails_on_missing_or_wrong_native_or_prior_certificate_evidence(self):
        expected = [r["postgres_sqlstate"] for r in self.rows for _ in range(2)]
        wrong = expected.copy()
        wrong[0] = "42P10"
        for observed in (expected[:-1], expected + ["00000"], wrong):
            with self.subTest(observed=observed[:4]), self.assertRaises(AssertionError):
                self.exercise_main(observed)
        for flag in ("static_error", "renderer_error"):
            with self.subTest(flag=flag), self.assertRaises(AssertionError):
                self.exercise_main(**{flag: True})


if __name__ == "__main__":
    unittest.main()
