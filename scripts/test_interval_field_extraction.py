"""Every authentic interval-field example must exercise an explicit new range."""
from collections import Counter
from copy import deepcopy
import json
import unittest

from extract_factor_corpus import (
    INTERVAL_FIELD_MASKS, ROOT, extract, observe_interval_fields, render,
    validate_interval_fields, validate_population,
)


def query(mask=7176, precision=None, literal="1 2:03:04"):
    mods = [{"A_Const": {"ival": {"ival": mask}}}]
    if precision is not None:
        mods.append({"A_Const": {"ival": {"ival": precision}}})
    return {"SelectStmt": {
        "op": "SETOP_NONE", "limitOption": "LIMIT_OPTION_DEFAULT",
        "targetList": [{"ResTarget": {"val": {"TypeCast": {
            "location": -1, "arg": {"A_Const": {"sval": {"sval": literal}}},
            "typeName": {"names": [{"String": {"sval": "pg_catalog"}},
                                   {"String": {"sval": "interval"}}], "typmods": mods},
        }}}}],
    }}


def cast(tree):
    return tree["SelectStmt"]["targetList"][0]["ResTarget"]["val"]["TypeCast"]


class IntervalFieldExtractionTests(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        cls.directory = ROOT / "fixtures/interval_fields"
        cls.manifest = json.loads((cls.directory / "concrete_sources.json").read_text())
        cls.records = extract(cls.manifest, "interval_fields")

    def test_fifty_original_statements_reproduce_without_existing_precision_only_forms(self):
        self.assertEqual(render(self.records), (self.directory / "concrete.jsonl").read_text())
        self.assertEqual(Counter(row["source"] for row in self.records), {"postgres": 49, "duckdb": 1})
        self.assertEqual(len({row["sql"] for row in self.records}), 50)
        for row in self.records:
            self.assertEqual(row["raw_sql"], row["sql"])
            self.assertEqual(row["transformations"], [])
            self.assertIsNone(row["parameter_types"])
            self.assertEqual(row["observed_parameter_slots"], [])
            self.assertIs(row["observed_syntax"]["source_free"], True)
            entries = row["observed_syntax"]["interval_fields"]
            self.assertEqual(len(entries), 1)
            self.assertIn(entries[0]["mask"], INTERVAL_FIELD_MASKS)
            self.assertNotEqual(entries[0]["mask"], 32767)
            for field in ("expected_value", "output_columns", "parameter_values"):
                self.assertNotIn(field, row)

    def test_all_thirteen_masks_and_precision_population_are_preserved(self):
        entries = [row["observed_syntax"]["interval_fields"][0] for row in self.records]
        self.assertEqual({entry["mask"] for entry in entries}, set(INTERVAL_FIELD_MASKS))
        self.assertEqual(Counter(entry["precision"] for entry in entries), {None: 38, 2: 12})
        for entry in entries:
            self.assertEqual(entry["fields"], INTERVAL_FIELD_MASKS[entry["mask"]])
            self.assertEqual(entry["form"], "typed-literal")
        self.assertFalse(any("interval(0)" in row["sql"].lower() or "interval(2)" in row["sql"].lower()
                             for row in self.records))

    def test_duckdb_block_is_whole_pinned_mit_source_with_opaque_results(self):
        row = next(row for row in self.records if row["source"] == "duckdb")
        self.assertEqual(row["sql"], "SELECT INTERVAL '90' DAY;\n")
        self.assertEqual(row["extraction"], "sqllogic_query")
        self.assertEqual(row["query_header"], "query T")
        self.assertEqual(row["source_dialect"], "duckdb")
        self.assertEqual(row["source_file"], "test/sql/types/interval/test_interval.test")
        self.assertEqual(row["commit"], "917243df252f114d9c448b1d23f8618f0d683769")
        self.assertEqual(row["license"], "MIT")
        self.assertNotIn("----", row["sql"])
        self.assertNotIn("90 days", row["sql"])

    def test_all_explicit_ranges_are_observed_without_decoding_literal_values(self):
        for mask, fields in INTERVAL_FIELD_MASKS.items():
            observed = observe_interval_fields(query(mask, literal="not an interval"))
            self.assertEqual(observed, {"source_free": True, "interval_fields": [{
                "fields": fields, "mask": mask, "precision": None,
                "literal": "not an interval", "form": "typed-literal"}]})

    def test_precision_none_zero_and_six_are_not_collapsed(self):
        for precision in (None, 0, 6):
            entry = observe_interval_fields(query(4096, precision))["interval_fields"][0]
            self.assertEqual(entry["precision"], precision)
            self.assertEqual(type(entry["precision"]), type(precision))
        zero = query(4096, 0)
        # PostgreSQL JSON can omit the scalar's default-valued ival property.
        cast(zero)["typeName"]["typmods"][1] = {"A_Const": {"ival": {}}}
        self.assertEqual(observe_interval_fields(zero)["interval_fields"][0]["precision"], 0)

    def test_no_qualifier_or_full_range_precision_is_not_counted_as_new_coverage(self):
        for mods in ([], [{"A_Const": {"ival": {"ival": 32767}}}],
                     [{"A_Const": {"ival": {"ival": 32767}}},
                      {"A_Const": {"ival": {"ival": 2}}}]):
            tree = query()
            cast(tree)["typeName"]["typmods"] = mods
            with self.assertRaises(ValueError):
                observe_interval_fields(tree)

    def test_invalid_masks_precisions_and_mismatched_range_labels_fail(self):
        for mask, precision in ((0, None), (12, None), (True, None), (4, 2),
                                 (4096, True), (4096, -1), (4096, 7)):
            with self.subTest(mask=mask, precision=precision), self.assertRaises(ValueError):
                observe_interval_fields(query(mask, precision))
        entries = observe_interval_fields(query())["interval_fields"]
        entries[0]["fields"] = "year to month"
        with self.assertRaises(ValueError):
            validate_interval_fields(entries)

    def test_arrays_catalog_columns_parameters_calls_and_alternate_cast_forms_are_excluded(self):
        for mutation in ("array", "user_type", "column", "parameter", "call", "cast_form"):
            tree = query()
            node = cast(tree)
            if mutation == "array":
                node["typeName"]["arrayBounds"] = [{"Integer": {"ival": -1}}]
            elif mutation == "user_type":
                node["typeName"]["names"][0]["String"]["sval"] = "custom"
            elif mutation == "cast_form":
                node["location"] = 7
            else:
                node["arg"] = {"column": {"ColumnRef": {"fields": []}},
                               "parameter": {"ParamRef": {"number": 1}},
                               "call": {"FuncCall": {}}}[mutation]
            with self.subTest(mutation=mutation), self.assertRaises(ValueError):
                observe_interval_fields(tree)

    def test_query_shape_rejects_aliases_tables_extra_projections_and_sets(self):
        for mutation in ("alias", "table", "projection", "set"):
            tree = query()
            if mutation == "alias":
                tree["SelectStmt"]["targetList"][0]["ResTarget"]["name"] = "v"
            elif mutation == "table":
                tree["SelectStmt"]["fromClause"] = []
            elif mutation == "projection":
                tree["SelectStmt"]["targetList"] *= 2
            else:
                tree["SelectStmt"]["op"] = "SETOP_UNION"
            with self.subTest(mutation=mutation), self.assertRaises(ValueError):
                observe_interval_fields(tree)

    def test_closed_population_detects_duplicate_scope_or_precision_changes(self):
        for mutation in ("duplicate", "scope", "precision", "mask"):
            rows = deepcopy(self.records)
            entry = rows[0]["observed_syntax"]["interval_fields"][0]
            if mutation == "duplicate":
                rows[1] = deepcopy(rows[0])
            elif mutation == "scope":
                rows[0]["observed_syntax"]["source_free"] = False
            elif mutation == "precision":
                entry["precision"] = 2
            else:
                entry["mask"], entry["fields"] = 32767, "all"
            with self.subTest(mutation=mutation), self.assertRaises(ValueError):
                validate_population(rows, "interval_fields")

    def test_selectors_sql_hashes_and_licenses_are_not_advisory(self):
        for mutation in ("selector", "sql_hash", "source_hash", "license_hash"):
            manifest = deepcopy(self.manifest)
            if mutation == "selector":
                manifest["selections"][-1]["selector"]["end"] -= 1
            elif mutation == "sql_hash":
                manifest["selections"][0]["sql_sha256"] = "0" * 64
            elif mutation == "source_hash":
                manifest["sources"]["duckdb"]["files"][0]["sha256"] = "0" * 64
            else:
                manifest["sources"]["duckdb"]["license_sha256"] = "0" * 64
            with self.subTest(mutation=mutation), self.assertRaises(ValueError):
                extract(manifest, "interval_fields")


if __name__ == "__main__":
    unittest.main()
