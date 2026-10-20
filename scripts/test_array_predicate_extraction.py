"""Closed source inventories and syntax-only array-predicate observations."""
from collections import Counter
from copy import deepcopy
import json
import unittest

from extract_factor_corpus import (
    ROOT, POPULATIONS, extract, observe_array_predicates, render,
    validate_array_predicates, validate_population,
)


def scalar():
    return {"A_Const": {"sval": {"sval": "{1}"}}}


def array():
    return {"A_ArrayExpr": {"elements": [{"A_Const": {"ival": {"ival": 1}}}]}}


def cast(value=None):
    return {"TypeCast": {"arg": scalar() if value is None else value, "typeName": {
        "names": [{"String": {"sval": "pg_catalog"}}, {"String": {"sval": "int4"}}],
        "arrayBounds": [{"Integer": {"ival": -1}}],
    }}}


def predicate(op="&&", left=None, right=None):
    return {"A_Expr": {"kind": "AEXPR_OP", "name": [{"String": {"sval": op}}],
                       "lexpr": array() if left is None else left,
                       "rexpr": array() if right is None else right}}


def query(expr=None, **fields):
    return {"SelectStmt": {"targetList": [predicate() if expr is None else expr], **fields}}


class ArrayPredicateExtractionTests(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        cls.manifests, cls.records = {}, {}
        for factor in ("array_containment", "array_overlap"):
            directory = ROOT / "fixtures" / factor
            cls.manifests[factor] = json.loads((directory / "concrete_sources.json").read_text())
            cls.records[factor] = extract(cls.manifests[factor], factor)

    def test_both_fifty_populations_reproduce_exact_original_bytes(self):
        for factor, rows in self.records.items():
            self.assertEqual(render(rows), (ROOT / "fixtures" / factor / "concrete.jsonl").read_text())
            self.assertEqual(Counter(row["source"] for row in rows), POPULATIONS[factor])
            self.assertEqual(len({row["sql"] for row in rows}), 50)
            for row in rows:
                self.assertEqual(row["raw_sql"], row["sql"])
                self.assertEqual(row["transformations"], [])
                self.assertIsNone(row["parameter_types"])
                self.assertEqual(row["application_schema_validity"], "not-claimed")
                for field in ("expected_value", "parameter_values", "output_columns"):
                    self.assertNotIn(field, row)

    def test_fixed_source_free_populations_and_operator_spellings(self):
        for factor, expected_count, expected_ops in (
                ("array_containment", 6, {"@>": 30, "<@": 20}),
                ("array_overlap", 5, {"&&": 50, "@>": 2})):
            rows = self.records[factor]
            self.assertEqual(sum(row["observed_syntax"]["source_free"] for row in rows), expected_count)
            self.assertEqual(Counter(entry["operator"] for row in rows
                                     for entry in row["observed_syntax"]["array_predicates"]), expected_ops)
            self.assertEqual([row["source"] for row in rows[:expected_count]],
                             ["risingwave"] * 4 + ["rum"] * (expected_count - 4))

    def test_readyset_is_source_available_with_original_bsl_license(self):
        metadata = self.manifests["array_overlap"]["sources"]["readyset"]
        self.assertEqual(metadata["license"], "BUSL-1.1")
        self.assertEqual(metadata["commit"], "a8ca5319d26690303f27d92963fee4c6240445bd")
        license_text = (ROOT / metadata["license_file"]).read_text()
        self.assertIn("Business Source License 1.1", license_text)
        self.assertIn("Four years from the date", license_text)
        self.assertIn("not an Open", license_text)
        rows = [row for row in self.records["array_overlap"] if row["source"] == "readyset"]
        self.assertEqual(Counter(row["extraction"] for row in rows),
                         {"sqllogic_query": 7, "rust_string": 4})

    def test_licensing_notices_and_operator_context_are_hash_checked(self):
        for factor, source, field in (
                ("array_overlap", "yugabyte", "additional_notices"),
                ("array_containment", "rum", "context_files")):
            manifest = deepcopy(self.manifests[factor])
            manifest["sources"][source][field][0]["sha256"] = "0" * 64
            with self.assertRaisesRegex(ValueError, "hash"):
                extract(manifest, factor)

    def test_unknown_bindings_remain_unknown_and_results_are_opaque(self):
        for factor, rows in self.records.items():
            parameter_rows = [row for row in rows if row["observed_parameter_slots"]]
            self.assertEqual(len(parameter_rows), 1 if factor == "array_overlap" else 0)
            if parameter_rows:
                self.assertEqual(parameter_rows[0]["observed_parameter_slots"], [1])
                self.assertEqual(parameter_rows[0]["source"], "sqlc")
                self.assertFalse(parameter_rows[0]["observed_syntax"]["source_free"])
            for row in rows:
                self.assertNotIn("----", row["sql"])
                self.assertNotIn("expected_results", row)

    def test_source_selector_hash_pin_and_population_mutations_fail(self):
        for mutation in ("hash", "selector", "pin", "count"):
            manifest = deepcopy(self.manifests["array_overlap"])
            if mutation == "hash":
                manifest["selections"][0]["sql_sha256"] = "0" * 64
            elif mutation == "selector":
                manifest["selections"][0]["selector"]["start"] += 1
            elif mutation == "pin":
                manifest["sources"]["readyset"]["commit"] = "main"
            else:
                manifest["selections"].pop()
            with self.subTest(mutation=mutation), self.assertRaises(ValueError):
                extract(manifest, "array_overlap")

    def test_duplicate_and_silent_source_scope_changes_fail(self):
        for mutation in ("duplicate", "scope", "operator"):
            rows = deepcopy(self.records["array_overlap"])
            if mutation == "duplicate":
                rows[-1] = deepcopy(rows[-2])
            elif mutation == "scope":
                rows[0]["observed_syntax"]["source_free"] = False
            else:
                rows[0]["observed_syntax"]["array_predicates"][0]["operator"] = "@>"
            with self.subTest(mutation=mutation), self.assertRaises(ValueError):
                validate_population(rows, "array_overlap")

    def test_only_immediate_casts_are_recorded_without_inferred_types(self):
        observed = observe_array_predicates(query(predicate(left=cast(), right=scalar())), "array_overlap")
        node = observed["array_predicates"][0]
        self.assertEqual(node["left"], {"form": "TypeCast", "declared_type": "pg_catalog.int4", "array_rank": 1})
        self.assertEqual(node["right"], {"form": "A_Const", "declared_type": None, "array_rank": None})
        bad = deepcopy(observed["array_predicates"])
        bad[0]["right"]["declared_type"] = "pg_catalog.int4"
        with self.assertRaises(ValueError):
            validate_array_predicates(bad, "array_overlap")

    def test_source_free_does_not_certify_external_columns_or_parameters(self):
        for value in ({"ColumnRef": {"fields": [{"String": {"sval": "a"}}]}},
                      {"ParamRef": {"number": 1}}):
            with self.assertRaisesRegex(ValueError, "external binding"):
                observe_array_predicates(query(predicate(left=value)), "array_overlap")

    def test_hidden_functions_rows_subqueries_and_subscripts_are_excluded(self):
        for kind in ("FuncCall", "SubLink", "RowExpr", "A_Indirection", "RangeSubselect"):
            with self.subTest(kind=kind), self.assertRaises(ValueError):
                observe_array_predicates(query(predicate(left=cast({kind: {}}))), "array_overlap")

    def test_overlap_factor_cannot_be_satisfied_by_containment_alone(self):
        with self.assertRaisesRegex(ValueError, "required"):
            observe_array_predicates(query(predicate("@>")), "array_overlap")
        with self.assertRaises(ValueError):
            observe_array_predicates(query(), "array_containment")

    def test_custom_extension_operators_and_sized_casts_are_not_admitted(self):
        for op in ("%","<=>","@@"):
            with self.subTest(op=op), self.assertRaises(ValueError):
                observe_array_predicates(query(predicate(op)), "array_overlap")
        expr = cast()
        expr["TypeCast"]["typeName"]["arrayBounds"] = [{"Integer": {"ival": 3}}]
        with self.assertRaisesRegex(ValueError, "sized"):
            observe_array_predicates(query(predicate(left=expr)), "array_overlap")


if __name__ == "__main__":
    unittest.main()
