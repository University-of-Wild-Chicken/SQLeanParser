"""Independent recursion boundaries and analysis-only protocol mutations."""
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
import check_recursive_boundaries as checker


class RecursiveBoundaryTests(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        cls.rows = checker.load_cases()
        cls.by_id = {r["id"]: r for r in cls.rows}

    def test_fixed_85_authored_cases_keep_analysis_and_profile_classifications_separate(self):
        self.assertEqual(len(self.rows), 85)
        self.assertEqual(Counter(r["expected_status"] for r in self.rows),
                         {"valid": 40, "invalid": 24, "unsupported": 21})
        for row in self.rows:
            self.assertEqual(row["source_kind"], "synthetic")
            self.assertEqual(row["postgres_columns"] is not None, row["postgres_sqlstate"] == "00000")
            self.assertEqual(row["output_columns"] is not None, row["expected_status"] == "valid")
            if row["output_columns"] and row["actual_recursion"]:
                self.assertTrue(all(c["nullable"] is True for c in row["output_columns"]))
        self.assertEqual(sum(r["expected_status"] == "unsupported" and
                             r["postgres_sqlstate"] == "00000" for r in self.rows), 5)
        self.assertEqual(sum(r["postgres_columns"] is not None for r in self.rows), 45)

    def test_anchor_modifiers_scope_and_collation_have_independent_exact_anchors(self):
        anchors = {
            "recursive-boundary-unknown-null-int": ("invalid", "42804", "recursive_type"),
            "recursive-boundary-numeric-equal": ("valid", "00000", None),
            "recursive-boundary-numeric-diff": ("invalid", "42804", "recursive_type"),
            "recursive-boundary-numeric-unmod-left": ("valid", "00000", None),
            "recursive-boundary-outer-INTERSECT": ("invalid", "42P19", "recursive_shape"),
            "recursive-boundary-two-ref": ("invalid", "42P19", "recursive_reference"),
            "recursive-boundary-unused-second-ref": ("invalid", "42P19", "recursive_reference"),
            "recursive-boundary-left-nullable": ("invalid", "42P19", "recursive_reference"),
            "recursive-boundary-scalar-sublink": ("unsupported", "42P19", "subquery"),
            "recursive-boundary-forward": ("unsupported", "00000", "recursive_dependency"),
            "recursive-boundary-step-group": ("unsupported", "00000", "group_by"),
            "recursive-boundary-step-order": ("valid", "00000", None),
            "recursive-wrapper-1": ("invalid", "0A000", "recursive_modifiers"),
            "recursive-collation-text-name-text-recursive":
                ("unsupported", "42P21", "recursive_collation"),
            "recursive-collation-name-text-text-recursive":
                ("unsupported", "00000", "recursive_collation"),
            "recursive-collation-text-name-text-ordinary": ("valid", "00000", None),
        }
        for id_, expected in anchors.items():
            self.assertEqual(tuple(self.by_id[id_][k] for k in
                             ("expected_status", "postgres_sqlstate", "diagnostic")), expected)
        self.assertEqual(self.by_id["recursive-boundary-numeric-equal"]["output_columns"],
                         [{"name": "x", "type": "numeric(8,2)", "nullable": True}])
        self.assertEqual(self.by_id["recursive-boundary-numeric-unmod-left"]["output_columns"],
                         [{"name": "x", "type": "numeric", "nullable": True}])
        self.assertEqual(self.by_id["recursive-boundary-inner-shadow"]["output_columns"],
                         [{"name": "x", "type": "int32", "nullable": False}])
        self.assertEqual([c["name"] for c in self.by_id["recursive-boundary-prefix-alias"]["output_columns"]],
                         ["x", "b"])
        self.assertEqual([c["name"] for c in self.by_id["recursive-boundary-duplicate-output"]["output_columns"]],
                         ["x", "x"])
        # Ordinary UNION still propagates CURRENT_SCHEMA's possible SQL NULL;
        # only the actually recursive branches force every output nullable.
        self.assertFalse(self.by_id["recursive-collation-text-current-schema-ordinary"]["actual_recursion"])
        self.assertEqual(
            self.by_id["recursive-collation-text-current-schema-ordinary"]["output_columns"],
            [{"name": "x", "type": "text", "nullable": True}])
        self.assertEqual(
            self.by_id["recursive-collation-text-current-catalog-ordinary"]["output_columns"],
            [{"name": "x", "type": "text", "nullable": False}])

    def test_registry_rejects_missing_reordered_and_reclassified_inputs(self):
        for mutation in ("missing", "order", "duplicate", "sql", "source_kind", "expected_status",
                         "postgres_sqlstate", "diagnostic", "output_columns", "postgres_columns",
                         "actual_recursion", "collation_class"):
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

    def test_exact_static_reports_require_status_diagnostics_and_nullable_metadata(self):
        for id_ in ("recursive-boundary-numeric-equal", "recursive-boundary-numeric-diff",
                    "recursive-collation-name-text-text-recursive"):
            row = self.by_id[id_]
            valid = row["expected_status"] == "valid"
            good = {"status": row["expected_status"], "assurance": "declarative",
                    "profile": assurance.PROFILES["contract"],
                    "evidence": "declarative-derivation" if valid else "none"}
            if valid:
                good.update(catalogUnchanged=True, typePrecision="exact",
                            outputColumns=deepcopy(row["output_columns"]))
            else:
                good["diagnostic"] = {"code": row["diagnostic"], "message": "explicit boundary"}
            mutations = [None, "exit", "status", "profile", "evidence"]
            mutations += ["name", "type", "nullable", "arity", "precision"] if valid else ["diagnostic", "output"]
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
                    report["outputColumns"][0]["nullable"] = 1
                elif mutation == "arity":
                    report["outputColumns"].pop()
                elif mutation == "precision":
                    report["typePrecision"] = "family"
                elif mutation == "diagnostic":
                    report["diagnostic"]["code"] = "wrong"
                elif mutation == "output":
                    report["outputColumns"] = []
                with self.subTest(id=id_, mutation=mutation), patch.object(
                        assurance, "invoke", return_value=subprocess.CompletedProcess(
                            [], code, json.dumps(report), "")):
                    if mutation is None:
                        checker.static_check(row)
                    else:
                        with self.assertRaises(AssertionError):
                            checker.static_check(row)

    def test_native_script_never_executes_a_recursive_query_and_describes_unsupported_successes(self):
        canonical = [r["sql"] + " /* canonical */" for r in self.rows]
        script, expected = checker.native_script(self.rows, canonical)
        self.assertEqual(len(expected), 354)
        self.assertEqual(script.count(" || pg_temp.recursive_analysis("), 170)
        self.assertEqual(script.count("PREPARE recursive_descriptor AS "), 90)
        self.assertEqual(script.count("EXECUTE recursive_descriptor\\gdesc"), 90)
        self.assertNotIn("EXECUTE recursive_descriptor;", script)
        self.assertNotIn("EXPLAIN", script)
        self.assertNotIn("CREATE VIEW", script)
        self.assertTrue(script.startswith("BEGIN;\n") and script.endswith("ROLLBACK;"))
        self.assertIn("SET LOCAL statement_timeout = '5s';", script)
        for row in self.rows:
            for layout in ("source", "canonical"):
                tag = f"description:{row['id']}:{layout}"
                self.assertEqual(tag in expected, row["postgres_columns"] is not None)
        with self.assertRaises(AssertionError):
            checker.native_script(self.rows, canonical[:-1])

    def test_native_evidence_is_strict_for_markers_states_order_labels_and_modifiers(self):
        _, expected = checker.native_script(self.rows, [r["sql"] for r in self.rows])
        checker.validate_native("\n".join(expected) + "\n", expected)
        for mutation in ("missing", "extra", "order", "state", "label", "modifier", "spacing"):
            observed = expected.copy()
            if mutation == "missing":
                observed.pop()
            elif mutation == "extra":
                observed.append("x|text")
            elif mutation == "order":
                observed[0], observed[1] = observed[1], observed[0]
            elif mutation == "state":
                observed[0] = observed[0].replace("42804", "00000")
            elif mutation == "label":
                observed[-1] = "renamed|text[]"
            elif mutation == "modifier":
                i = observed.index("x|numeric(8,2)")
                observed[i] = "x|numeric"
            else:
                observed[0] += " "
            with self.subTest(mutation=mutation), self.assertRaises(AssertionError):
                checker.validate_native("\n".join(observed) + "\n", expected)

    def exercise_main(self, *, failure=None):
        canonical = [r["sql"] + " /* canonical */" for r in self.rows]
        _, expected = checker.native_script(self.rows, canonical)
        if failure == "missing":
            expected.pop()
        elif failure == "metadata":
            expected[-1] = "x|integer"
        def rendering(mode, sql):
            if failure == "renderer":
                raise AssertionError("missing rendering evidence")
            return {"sql": sql + " /* canonical */" if mode == "postgres" else sql}
        output = io.StringIO()
        with patch.object(checker, "static_check",
                          side_effect=AssertionError("wrong static evidence") if failure == "static" else None) as static, \
                patch.object(checker, "replay", side_effect=rendering) as replay, \
                patch.object(checker, "connection", return_value=nullcontext(["psql"])) as connection, \
                patch.object(checker, "run", side_effect=[
                    subprocess.CompletedProcess([], 0, "170007\n" if failure == "version" else "160015\n", ""),
                    subprocess.CompletedProcess([], 0, "\n".join(expected) + "\n", "")]) as run, \
                patch("sys.argv", ["check_recursive_boundaries.py", "--local-bin", "/native"]), \
                redirect_stdout(output):
            try:
                checker.main()
            except AssertionError:
                if failure in {"static", "renderer"}:
                    connection.assert_not_called()
                    run.assert_not_called()
                raise
        return output.getvalue(), static, replay, run

    def test_main_checks_all_static_and_renderer_certificates_before_prepare(self):
        output, static, replay, run = self.exercise_main()
        self.assertEqual([c.args[0] for c in static.call_args_list], self.rows)
        self.assertEqual([c.args for c in replay.call_args_list],
                         [(mode, r["sql"]) for r in self.rows for mode in ("identity", "postgres")])
        self.assertEqual(len(run.call_args_list), 2)
        self.assertEqual(run.call_args_list[1].kwargs["timeout"], 120)
        self.assertIn("85 authored recursive boundaries", output)
        self.assertIn("170 source/canonical PREPARE outcomes", output)
        self.assertIn("90 prepared result descriptions", output)

    def test_main_fails_on_missing_evidence_or_wrong_engine_version(self):
        for failure in ("missing", "metadata", "static", "renderer", "version"):
            with self.subTest(failure=failure), self.assertRaises(AssertionError):
                self.exercise_main(failure=failure)


if __name__ == "__main__":
    unittest.main()
