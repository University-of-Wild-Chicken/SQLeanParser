"""Offline provenance and population checks for closed incremental sources."""
from copy import deepcopy
import json
import unittest

from extract_factor_corpus import (
    CONDITIONAL_FORMS, JOIN_KINDS, LOCK_POLICIES, LOCK_STRENGTHS, MERGED_FACTORS,
    POPULATIONS, ROOT, extract, merged_join_kinds, render, validate_join_tree, validate_population,
)


class FactorExtractionTests(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        cls.manifests = {
            factor: json.loads((ROOT / "fixtures" / factor / "concrete_sources.json").read_text())
            for factor in POPULATIONS
        }
        cls.records = {factor: extract(manifest, factor)
                       for factor, manifest in cls.manifests.items()}

    def test_both_closed_fifty_statement_populations_reproduce(self):
        for factor, rows in self.records.items():
            with self.subTest(factor=factor):
                self.assertEqual(len(rows), 50)
                self.assertEqual(render(rows),
                                 (ROOT / "fixtures" / factor / "concrete.jsonl").read_text())
                for source, count in POPULATIONS[factor].items():
                    self.assertEqual(sum(row["source"] == source for row in rows), count)

    def test_factor_forms_and_function_diversity_are_explicit(self):
        rows = self.records["conditional"]
        self.assertEqual({form for row in rows
                          for form in row["observed_syntax"]["conditional_forms"]},
                         CONDITIONAL_FORMS)
        self.assertEqual(len({name for row in self.records["functions"]
                              for name in row["observed_syntax"]["function_names"]}), 40)
        self.assertTrue(all(not row["observed_syntax"]["conditional_forms"]
                            for row in self.records["functions"]))

    def test_locking_forms_and_of_target_order_are_retained(self):
        locks = [lock for row in self.records["locking"]
                 for lock in row["observed_syntax"]["locking_clauses"]]
        self.assertEqual({lock["strength"] for lock in locks}, LOCK_STRENGTHS)
        self.assertEqual({lock["wait_policy"] for lock in locks}, LOCK_POLICIES)
        self.assertIn(["pgss_a", "pgss_b"], [lock["targets"] for lock in locks])
        self.assertIn(["pgss_b", "pgss_a"], [lock["targets"] for lock in locks])
        rows = self.records["locking"]
        self.assertTrue(any("FOR UPDATE LIMIT 1" in row["sql"] for row in rows))
        self.assertTrue(any("OFFSET 100 LIMIT 10 FOR UPDATE" in row["sql"] for row in rows))
        self.assertEqual(sum(row["source_kind"] == "application-constant" for row in rows), 23)

    def test_losing_lock_strength_policy_or_target_shape_fails(self):
        for field, old, replacement in (("strength", "key-share", "share"),
                                         ("wait_policy", "nowait", "default")):
            rows = deepcopy(self.records["locking"])
            for row in rows:
                for lock in row["observed_syntax"]["locking_clauses"]:
                    if lock[field] == old:
                        lock[field] = replacement
            with self.subTest(field=field), self.assertRaisesRegex(ValueError, "four locking strengths"):
                validate_population(rows, "locking")
        rows = deepcopy(self.records["locking"])
        rows[0]["observed_syntax"]["locking_clauses"][0]["targets"] = "table_name"
        with self.assertRaisesRegex(ValueError, "invalid locking observation"):
            validate_population(rows, "locking")

    def test_join_population_retains_five_kinds_nested_order_and_aliases(self):
        rows = self.records["join_contract"]
        observed = set()
        for row in rows:
            observed.update(validate_join_tree(row["observed_syntax"]["join_tree"]))
        self.assertEqual(observed, JOIN_KINDS)
        ordered = [row for row in rows if "join_clauses_order/" in row["source_file"]]
        self.assertEqual(len(ordered), 4)
        tree = ordered[0]["observed_syntax"]["join_tree"]
        self.assertEqual(tree["kind"], "inner")
        self.assertEqual(tree["left"]["kind"], "left")
        self.assertEqual(tree["left"]["left"], {"kind": "table", "name": "a", "alias": None})
        self.assertEqual(tree["right"], {"kind": "table", "name": "c", "alias": None})
        app = next(row for row in rows if row["source"] == "hatchet")
        self.assertEqual(app["observed_syntax"]["join_tree"]["left"],
                         {"kind": "table", "name": "Worker", "alias": "w"})
        self.assertEqual(app["source_kind"], "application-constant")

    def test_join_observer_rejects_unsupported_conditions_and_non_table_leaves(self):
        table = {"kind": "table", "name": "t", "alias": None}
        valid = {"kind": "left", "condition": "on", "left": table, "right": table}
        bad = [
            table, ["left", table, table], {**valid, "kind": "natural"},
            {**valid, "kind": ["left"]}, {**valid, "condition": "using"},
            {**valid, "condition": "none"}, {**valid, "kind": "cross"},
            {**valid, "left": {"kind": "derived", "query": "SELECT 1"}},
            {**valid, "left": {**table, "alias": ""}},
            {**valid, "left": {**table, "name": ""}},
            {**valid, "left": {**table, "columns": ["x"]}},
        ]
        for tree in bad:
            with self.subTest(tree=tree), self.assertRaisesRegex(ValueError, "base-table join"):
                validate_join_tree(tree)
        self.assertEqual(validate_join_tree({**valid, "kind": "cross", "condition": "none"}),
                         {"cross"})

    def test_losing_entire_join_kind_fails_closed(self):
        rows = deepcopy(self.records["join_contract"])

        def erase_right(tree):
            if tree["kind"] != "table":
                if tree["kind"] == "right":
                    tree["kind"] = "left"
                erase_right(tree["left"])
                erase_right(tree["right"])

        for row in rows:
            erase_right(row["observed_syntax"]["join_tree"])
        with self.assertRaisesRegex(ValueError, "all five base-table join kinds"):
            validate_population(rows, "join_contract")

    def test_join_source_slice_cannot_be_replaced_by_a_query_fragment(self):
        manifest = deepcopy(self.manifests["join_contract"])
        selection = next(row for row in manifest["selections"]
                         if row["selector"]["kind"] == "sql_slice")
        selection["selector"]["end"] -= 1
        with self.assertRaisesRegex(ValueError, "complete statement"):
            extract(manifest, "join_contract")

    def test_merged_populations_cover_four_kinds_and_retain_sqlite_origin(self):
        for factor, condition in MERGED_FACTORS.items():
            rows = self.records[factor]
            kinds = set()
            for row in rows:
                tree = row["observed_syntax"]["join_tree"]
                validate_join_tree(tree, allow_merged=True)
                self.assertTrue(merged_join_kinds(tree, condition))
                kinds.update(merged_join_kinds(tree, condition))
                if row["source"] == "sqlite":
                    self.assertEqual(row["source_kind"], "engine-regression")
                    self.assertEqual(row["source_dialect"], "sqlite")
                    self.assertEqual(row["license"], "Public Domain")
                    self.assertEqual(row["extraction"], "tcl_sql_statement")
                    self.assertIn(row["tcl_command"],
                                  {"execsql", "catchsql", "do_execsql_test", "do_catchsql_test"})
                    self.assertNotIn("joinB.test", row["source_file"])
                    self.assertNotIn("joinC.test", row["source_file"])
            self.assertEqual(kinds, JOIN_KINDS - {"cross"})

    def test_using_columns_keep_order_and_reject_empty_duplicate_or_wrong_shapes(self):
        table = {"kind": "table", "name": "t", "alias": None}
        tree = {"kind": "full", "condition": "using", "columns": ["z", "a"],
                "left": table, "right": table}
        self.assertEqual(validate_join_tree(tree, allow_merged=True), {"full"})
        self.assertEqual(tree["columns"], ["z", "a"])
        with self.assertRaisesRegex(ValueError, "base-table join"):
            validate_join_tree(tree)
        for columns in ([], ["a", "a"], "", ["a", None], [""]):
            with self.subTest(columns=columns), self.assertRaisesRegex(ValueError, "USING columns"):
                validate_join_tree({**tree, "columns": columns}, allow_merged=True)
        for bad in ({**tree, "kind": "cross"}, {**tree, "condition": "natural"},
                    {key: value for key, value in tree.items() if key != "columns"}):
            with self.assertRaisesRegex(ValueError, "base-table join"):
                validate_join_tree(bad, allow_merged=True)

    def test_merged_factor_and_kind_cannot_disappear_from_metadata(self):
        for factor, condition in MERGED_FACTORS.items():
            rows = deepcopy(self.records[factor])

            def alter(tree, all_conditions):
                if tree["kind"] == "table":
                    return
                if tree["condition"] == condition:
                    if all_conditions:
                        tree["condition"] = "on"
                        tree.pop("columns", None)
                    elif tree["kind"] == "right":
                        tree["kind"] = "left"
                alter(tree["left"], all_conditions)
                alter(tree["right"], all_conditions)

            alter(rows[0]["observed_syntax"]["join_tree"], True)
            with self.subTest(factor=factor), self.assertRaisesRegex(ValueError, "factor is absent"):
                validate_population(rows, factor)
            rows = deepcopy(self.records[factor])
            for row in rows:
                alter(row["observed_syntax"]["join_tree"], False)
            with self.assertRaisesRegex(ValueError, "all four merged join kinds"):
                validate_population(rows, factor)

    def test_pinned_tcl_argument_and_statement_bounds_are_required(self):
        for field in ("block_start", "block_end", "start", "end"):
            manifest = deepcopy(self.manifests["natural_contract"])
            selection = next(row for row in manifest["selections"] if row["source"] == "sqlite")
            selection["selector"][field] += 1
            with self.subTest(field=field), self.assertRaisesRegex(ValueError, "pinned complete"):
                extract(manifest, "natural_contract")

    def test_queries_retain_original_bytes_and_no_invented_bindings(self):
        from observe_named_argument_source import INTERFACE_CASES

        for rows in self.records.values():
            for row in rows:
                self.assertEqual(row["sql"], row["raw_sql"])
                self.assertEqual(row["transformations"], [])
                declaration = INTERFACE_CASES.get(row["id"])
                if declaration:
                    self.assertEqual(row["parameter_types"], declaration[4])
                    self.assertEqual(row["parameter_type_provenance"]["go_type"], declaration[3])
                    self.assertEqual(row["parameter_type_provenance"]["method"], declaration[0])
                else:
                    self.assertIsNone(row["parameter_types"])
                    self.assertNotIn("parameter_type_provenance", row)
                self.assertNotIn("parameter_values", row)
                self.assertEqual(row["application_schema_validity"], "not-claimed")
                self.assertIn(f'/blob/{row["commit"]}/{row["source_file"]}', row["source_url"])
                self.assertTrue(row["source_url"].endswith(f'#L{row["line"]}'))
                if row["source"] == "hatchet":
                    self.assertEqual(row["source_kind"], "application-constant")
                    self.assertTrue(row["sql"].startswith("-- name:"))

    def test_missing_and_duplicate_statements_cannot_inflate_population(self):
        for factor, rows in self.records.items():
            with self.subTest(factor=factor), self.assertRaisesRegex(ValueError, "expected 50"):
                validate_population(rows[:-1], factor)
            duplicate = deepcopy(rows)
            duplicate[1]["sql"] = duplicate[0]["sql"]
            with self.assertRaisesRegex(ValueError, "duplicate factor sql"):
                validate_population(duplicate, factor)
            duplicate[1]["sql"] = "\n" + duplicate[0]["sql"].upper() + " "
            with self.assertRaisesRegex(ValueError, "case/whitespace duplicate"):
                validate_population(duplicate, factor)

    def test_rewrites_fake_bindings_and_missing_slots_fail(self):
        for field, value, error in (
            ("raw_sql", "SELECT fabricated();", "text was changed"),
            ("transformations", ["invented renamed variant"], "text was changed"),
            ("parameter_types", "int", "must not invent"),
            ("observed_parameter_slots", [999], "parameter-slot"),
            ("factor", "conditional", "identity changed"),
        ):
            rows = deepcopy(self.records["functions"])
            rows[0][field] = value
            with self.subTest(field=field), self.assertRaisesRegex(ValueError, error):
                validate_population(rows, "functions")

    def test_malformed_or_missing_observations_fail(self):
        for observation, error in (
            ({"function_names": ["lower"]}, "unexpected factor observation"),
            ({"function_names": ["lower", "lower"], "conditional_forms": []},
             "sorted unique list"),
            ({"function_names": ["lower"], "conditional_forms": ["unknown"]},
             "unknown conditional form"),
            ({"function_names": [], "conditional_forms": []}, "factor is missing"),
        ):
            rows = deepcopy(self.records["functions"])
            rows[0]["observed_syntax"] = observation
            with self.subTest(observation=observation), self.assertRaisesRegex(ValueError, error):
                validate_population(rows, "functions")

    def test_losing_an_entire_conditional_form_fails(self):
        rows = deepcopy(self.records["conditional"])
        for row in rows:
            row["observed_syntax"]["conditional_forms"] = [
                "coalesce" if form == "least" else form
                for form in row["observed_syntax"]["conditional_forms"]
            ]
        with self.assertRaisesRegex(ValueError, "all six conditional forms"):
            validate_population(rows, "conditional")

    def test_replacing_diverse_calls_with_one_name_fails(self):
        rows = deepcopy(self.records["functions"])
        for row in rows:
            row["observed_syntax"]["function_names"] = ["lower"]
        with self.assertRaisesRegex(ValueError, "twenty distinct"):
            validate_population(rows, "functions")

    def test_cross_factor_manifest_is_not_accepted(self):
        with self.assertRaisesRegex(ValueError, "unexpected factor source manifest"):
            extract(self.manifests["conditional"], "functions")

    def test_source_license_revision_and_selected_hashes_are_checked(self):
        for target in ("source", "license", "revision", "selection"):
            manifest = deepcopy(self.manifests["functions"])
            metadata = manifest["sources"]["hatchet"]
            if target == "source":
                metadata["files"][0]["sha256"] = "0" * 64
            elif target == "license":
                metadata["license_sha256"] = "0" * 64
            elif target == "revision":
                metadata["commit"] = "main"
            else:
                manifest["selections"][0]["sql_sha256"] = "0" * 64
            with self.subTest(target=target), self.assertRaises(ValueError):
                extract(manifest, "functions")

    def test_complete_source_statement_boundaries_are_enforced(self):
        manifest = deepcopy(self.manifests["functions"])
        selection = next(row for row in manifest["selections"]
                         if row["selector"]["kind"] == "sql_slice")
        selection["selector"]["end"] -= 1
        with self.assertRaisesRegex(ValueError, "complete statement"):
            extract(manifest, "functions")


if __name__ == "__main__":
    unittest.main()
