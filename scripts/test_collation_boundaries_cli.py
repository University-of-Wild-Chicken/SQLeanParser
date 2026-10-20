"""Independent collation boundary registry and analysis-protocol mutations."""
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
import check_collation_boundaries_cli as checker


class CollationBoundaryTests(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        cls.fixture = checker.load_cases()
        cls.rows = cls.fixture["cases"]
        cls.by_id = {r["id"].removeprefix("collation-boundary-"): r for r in cls.rows}

    def test_frozen_authored_registry_separates_prepare_view_and_static_evidence(self):
        self.assertEqual(len(self.rows), 121)
        self.assertEqual(len(self.fixture["snapshot_cases"]), 10)
        for key in ("implicit-conflict", "implicit-array", "scope-conflict-erasure",
                    "cte-conflict-erasure", "set-all-implicit"):
            row = self.by_id[key]
            self.assertEqual((row["postgres_prepare"], row["postgres_view"]), ("00000", "42P22"))
            self.assertEqual(row["expected_status"], "valid")
            self.assertIsNone(row["output_columns"][0]["collation"])
        anomaly = self.by_id["set-unknown-noncollatable"]
        self.assertEqual((anomaly["postgres_prepare"], anomaly["postgres_view"]), ("00000", "42804"))
        self.assertEqual(anomaly["output_columns"], [
            {"name": "v", "type": "int32", "nullable": False, "collation": "C"}])
        self.assertIsNone(anomaly["postgres_columns"])
        self.assertEqual(self.by_id["implicit-sort"]["postgres_prepare"], "42P21")
        self.assertEqual(self.by_id["scope-conflict-erasure"]["postgres_prepare"], "00000")

    def test_pairwise_case_in_and_contextual_array_boundaries_remain_distinct(self):
        good = ("case-condition-conflict", "case-condition-distinct-result",
                "row-pairwise", "row-pairwise-distinct", "row-null-separate",
                "between-pairwise", "between-vars-pairwise", "in-vars-pairwise",
                "in-mixed-pairwise", "in-single", "array-context-erases", "subscript-bound-erases")
        bad = ("row-pair-conflict", "between-pair-conflict", "in-array-conflict",
               "in-mixed-array-conflict", "outer-cannot-repair-child")
        self.assertTrue(all(self.by_id[k]["postgres_prepare"] == "00000" for k in good))
        self.assertTrue(all(self.by_id[k]["postgres_prepare"] == "42P21" for k in bad))
        self.assertEqual(self.by_id["case-condition-only"]["output_columns"][0]["collation"], "default")
        self.assertEqual(self.by_id["case-condition-distinct-result"]["output_columns"][0]["collation"],
                         "POSIX")
        self.assertIsNone(self.by_id["array-context-erases"]["output_columns"][0]["collation"])
        self.assertEqual(self.by_id["subscript-bound-erases"]["output_columns"][0]["collation"], "C")

    def test_implicit_context_values_and_casts_are_not_replaced_by_text_defaults(self):
        expected = {
            "plain-current-user": ("name", False, "C"),
            "plain-current-schema": ("name", True, "C"),
            "plain-system-user": ("text", True, "default"),
            "plain-name-array-cast": ("text[]", False, "C"),
            "plain-numeric-erasure": ("text", False, "default"),
            "cast-keeps": ("text", False, "C"),
            "plain-unknown": ("text", False, "default"),
            "set-wrapper-text": ("text", False, "C"),
            "set-wrapper-identity-cast": ("text", False, "C"),
            "set-wrapper-changing-cast": ("text", False, "default"),
        }
        for key, column in expected.items():
            actual = self.by_id[key]["output_columns"][0]
            self.assertEqual(tuple(actual[f] for f in ("type", "nullable", "collation")), column)
        self.assertEqual(self.by_id["unknown-arithmetic-one"]["postgres_columns"][0]["type"], "integer")
        self.assertEqual(self.by_id["unknown-arithmetic-both"]["postgres_prepare"], "42725")
        self.assertEqual(self.by_id["unknown-boolean"]["postgres_columns"][0]["type"], "boolean")

    def test_snapshot_lookup_is_encoding_specific_and_visibility_is_an_explicit_premise(self):
        rows = {r["environment"]: r for r in self.fixture["snapshot_cases"]}
        for key in ("current-after-fallback", "current-before-fallback",
                    "qualified-hidden", "hidden-foreign-with-current"):
            self.assertEqual(rows[key]["output_columns"][0]["collation"], "custom:current")
        self.assertEqual(rows["fallback-after-foreign"]["output_columns"][0]["collation"],
                         "custom:fallback")
        for key in ("duplicate-visible", "duplicate-id", "duplicate-qualified"):
            self.assertEqual((rows[key]["expected_status"], rows[key]["diagnostic"]),
                             ("invalid", "invalid_collation_environment"))
        for key in ("foreign-only", "qualified-foreign-only"):
            self.assertEqual((rows[key]["expected_status"], rows[key]["diagnostic"]),
                             ("unsupported", "collation_environment"))
        first = self.by_id["lookup-unqualified"]
        shadow = self.by_id["lookup-shadow"]
        self.assertEqual(first["sql"], shadow["sql"])
        self.assertNotEqual(first["output_columns"], shadow["output_columns"])
        self.assertEqual(first["output_columns"][0]["collation"], "custom:probe_choice")
        self.assertEqual(shadow["output_columns"][0]["collation"], "custom:alt_choice")

    def test_unknown_sort_matching_tracks_each_resolution_and_collation_identity(self):
        for key in ("sort-wrapper-distinct", "sort-wrapper-ordinal", "sort-wrapper-name",
                    "sort-wrapper-expression", "sort-null-wrapper-expression",
                    "sort-wrapper-qualified-equivalence",
                    "sort-set-sequential-expression-twice",
                    "sort-set-sequential-position-expression"):
            row = self.by_id[key]
            self.assertEqual((row["expected_status"], row["diagnostic"],
                              row["postgres_prepare"]),
                             ("invalid", "set_common_type", "42804"))
        for key in ("sort-duplicate-expression-name", "sort-duplicate-name-twice",
                    "sort-null-duplicate-position-name",
                    "sort-distinct-duplicate-name-twice",
                    "sort-sequential-expression-position"):
            row = self.by_id[key]
            self.assertEqual((row["expected_status"], row["diagnostic"],
                              row["postgres_prepare"]),
                             ("invalid", "ambiguous_output", "42702"))
        for key in ("sort-duplicate-name", "sort-duplicate-name-position-name",
                    "sort-null-duplicate-both-positions",
                    "sort-duplicate-qualified-equivalence",
                    "sort-sequential-expression-twice",
                    "sort-sequential-position-expression",
                    "sort-sequential-name-expression"):
            row = self.by_id[key]
            self.assertEqual((row["expected_status"], row["postgres_prepare"],
                              row["postgres_view"]), ("valid", "00000", "42701"))
            self.assertEqual([c["name"] for c in row["output_columns"]], ["x", "x"])
        for key in ("sort-wrapper-different-literal", "sort-wrapper-different-identity",
                    "sort-set-single-expression-control"):
            row = self.by_id[key]
            self.assertEqual((row["expected_status"], row["postgres_prepare"],
                              row["postgres_view"]), ("valid", "00000", "42804"))
            self.assertEqual(row["output_columns"][-1]["type"], "int32")
        self.assertEqual(self.by_id["sort-set-sequential-text-control"]["postgres_columns"], [
            {"name": name, "type": "text",
             "collation": {"schema": "pg_catalog", "name": "C", "encoding": None}}
            for name in ("x", "y")])

    def test_hash_guard_rejects_reclassification_metadata_bool_alias_and_input_changes(self):
        mutations = [
            lambda f: f["cases"].pop(),
            lambda f: f["cases"].reverse(),
            lambda f: f["cases"][0].update(sql="SELECT 1"),
            lambda f: f["cases"][0].update(source_kind="downloaded"),
            lambda f: f["cases"][0].update(postgres_prepare="42P21"),
            lambda f: f["cases"][0]["output_columns"][0].update(nullable=0),
            lambda f: f["cases"][0]["output_columns"][0].update(collation="POSIX"),
            lambda f: f["snapshot_cases"].pop(),
            lambda f: f["environments"]["standard"]["collations"]["entries"][0].update(
                exposeUnqualified=1),
        ]
        for mutate in mutations:
            fixture = deepcopy(self.fixture)
            mutate(fixture)
            with tempfile.TemporaryDirectory() as directory:
                path = Path(directory) / "boundaries.json"
                path.write_text(json.dumps(fixture))
                with patch.object(checker, "FIXTURE", path), self.assertRaises(AssertionError):
                    checker.load_cases()

    def test_static_protocol_requires_exact_status_diagnostic_and_output_identities(self):
        for key in ("plain-current-schema", "explicit-conflict", "lookup-missing"):
            row = self.by_id[key]
            valid = row["expected_status"] == "valid"
            report = {"status": row["expected_status"], "assurance": "declarative",
                      "profile": assurance.PROFILES["contract"],
                      "evidence": "declarative-derivation" if valid else "none"}
            if valid:
                report.update(outputColumns=[
                    {k: c[k] for k in ("name", "type", "nullable")} for c in row["output_columns"]],
                    outputCollations=[c["collation"] for c in row["output_columns"]],
                    typePrecision="exact", catalogUnchanged=True)
            else:
                report["diagnostic"] = {"code": row["diagnostic"], "message": "explicit boundary"}
            mutations = [None, "status", "exit", "evidence"]
            mutations += ["missing", "collation", "arity", "nullable"] if valid else ["diagnostic", "output"]
            for mutation in mutations:
                actual = deepcopy(report)
                code = assurance.EXIT_CODES[row["expected_status"]]
                if mutation == "exit":
                    code = 4
                elif mutation in {"status", "evidence"}:
                    actual[mutation] = "wrong"
                elif mutation == "missing":
                    actual.pop("outputCollations")
                elif mutation == "collation":
                    actual["outputCollations"][0] = "POSIX"
                elif mutation == "arity":
                    actual["outputCollations"].append("C")
                elif mutation == "nullable":
                    actual["outputColumns"][0]["nullable"] = 1
                elif mutation == "diagnostic":
                    actual["diagnostic"]["code"] = "wrong"
                elif mutation == "output":
                    actual["outputCollations"] = []
                with self.subTest(key=key, mutation=mutation), patch.object(
                    assurance, "invoke", return_value=subprocess.CompletedProcess(
                        [], code, json.dumps(actual), "")):
                    if mutation is None:
                        checker.static_check(row, "schema.json")
                    else:
                        with self.assertRaises(AssertionError):
                            checker.static_check(row, "schema.json")

    def test_analysis_script_never_executes_inputs_or_uses_metadata_only_environments(self):
        canonical = [r["sql"] + " /* canonical */" for r in self.rows]
        script, expected = checker.native_script(self.fixture, canonical)
        self.assertEqual(len(expected), 244)
        self.assertEqual(script.count("'observation',pg_temp.collation_boundary_analysis("), 242)
        self.assertIn("EXECUTE 'PREPARE collation_boundary AS '||q", script)
        self.assertIn("EXECUTE 'CREATE TEMP VIEW collation_boundary_view AS '||q", script)
        self.assertNotIn("EXECUTE collation_boundary;", script)
        self.assertNotIn("EXPLAIN", script)
        self.assertNotIn("INSERT INTO", script)
        self.assertNotIn("encoding_probe", script)
        self.assertTrue(script.startswith("BEGIN;") and script.endswith("ROLLBACK;"))
        self.assertEqual(sum(e.get("observation", {}).get("view") == "42P22" for e in expected), 14)
        self.assertEqual(sum(e.get("observation", {}).get("columns") is not None
                             for e in expected if "observation" in e), 114)
        with self.assertRaises(AssertionError):
            checker.native_script(self.fixture, canonical[:-1])
        source_script, source_expected = checker.native_script(self.fixture)
        self.assertEqual(len(source_expected), 123)
        self.assertNotIn(" /* canonical */", source_script)
        with self.assertRaises(AssertionError):
            checker.native_path("current-after-fallback")

    def test_native_protocol_rejects_missing_duplicate_reordered_and_wrong_evidence(self):
        _, expected = checker.native_script(self.fixture, [r["sql"] for r in self.rows])
        checker.validate_native("\n".join(map(json.dumps, expected)) + "\n", expected)
        mutations = [
            lambda e: e.pop(),
            lambda e: e.append(deepcopy(e[-1])),
            lambda e: e.reverse(),
            lambda e: e[2]["observation"].update(prepare="42P21"),
            lambda e: e[2]["observation"].update(view=None),
            lambda e: e[2]["observation"]["columns"][0].update(type="name"),
            lambda e: e[2]["observation"]["columns"][0]["collation"].update(name="POSIX"),
            lambda e: e[0]["entries"][0].update(exposeUnqualified=1),
            lambda e: e[1]["entries"][3].update(exposeUnqualified=True),
            lambda e: e[2].update(form="canonical"),
        ]
        for mutate in mutations:
            changed = deepcopy(expected)
            mutate(changed)
            with self.assertRaises(AssertionError):
                checker.validate_native("\n".join(map(json.dumps, changed)), expected)

    def test_source_only_main_still_requires_every_native_observation_and_pg16(self):
        _, expected = checker.native_script(self.fixture)
        for mutation in (None, "missing", "version"):
            actual = deepcopy(expected)
            if mutation == "missing":
                actual.pop()
            responses = [
                subprocess.CompletedProcess([], 0, "170001\n" if mutation == "version" else "160015\n", ""),
                subprocess.CompletedProcess([], 0, "\n".join(map(json.dumps, actual)) + "\n", ""),
            ]
            with self.subTest(mutation=mutation), patch("sys.argv", [
                "check", "--local-bin", "/owned/postgres16", "--source-only"
            ]), patch.object(checker, "connection", return_value=nullcontext(["psql"])), \
                    patch.object(checker, "run", side_effect=responses), \
                    patch.object(checker, "static_check") as static, \
                    patch.object(checker, "replay") as replay, redirect_stdout(io.StringIO()):
                if mutation is None:
                    checker.main()
                else:
                    with self.assertRaises(AssertionError):
                        checker.main()
                static.assert_not_called()
                replay.assert_not_called()


if __name__ == "__main__":
    unittest.main()
