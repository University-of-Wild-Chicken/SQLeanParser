"""Frozen temporal EXTRACT source queries and finite syntax observations."""
from collections import Counter
from copy import deepcopy
import json
import unittest

from extract_factor_corpus import (
    EXTRACT_SOURCE_FIELDS, ROOT, extract, observe_temporal_extractions, render,
    validate_population, validate_temporal_extractions,
)


def query(field="day", type_name="date", literal="2020-08-11"):
    return {"SelectStmt": {
        "op": "SETOP_NONE", "limitOption": "LIMIT_OPTION_DEFAULT",
        "targetList": [{"ResTarget": {"val": {"FuncCall": {
            "funcname": [{"String": {"sval": "pg_catalog"}}, {"String": {"sval": "extract"}}],
            "funcformat": "COERCE_SQL_SYNTAX",
            "args": [{"A_Const": {"sval": {"sval": field}}},
                     {"TypeCast": {"arg": {"A_Const": {"sval": {"sval": literal}}},
                                   "typeName": {"names": [{"String": {"sval": type_name}}]}}}],
        }}}}],
    }}


def call(tree):
    return tree["SelectStmt"]["targetList"][0]["ResTarget"]["val"]["FuncCall"]


class ExtractExtractionTests(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        cls.directory = ROOT / "fixtures/extract"
        cls.manifest = json.loads((cls.directory / "concrete_sources.json").read_text())
        cls.records = extract(cls.manifest, "extract")

    def test_fifty_whole_originals_reproduce_from_existing_pinned_sources(self):
        self.assertEqual(render(self.records), (self.directory / "concrete.jsonl").read_text())
        self.assertEqual(len({row["sql"] for row in self.records}), 50)
        self.assertEqual(len(self.manifest["sources"]["postgres"]["files"]), 6)
        self.assertEqual(self.manifest["sources"]["postgres"]["commit"],
                         "f0595c3d839debdb140903621c1b44a4f4d86256")
        self.assertEqual(self.manifest["sources"]["postgres"]["license"], "PostgreSQL")
        for row in self.records:
            self.assertEqual(row["source_kind"], "engine-regression")
            self.assertEqual(row["sql"], row["raw_sql"])
            self.assertEqual(row["transformations"], [])
            self.assertEqual(row["observed_parameter_slots"], [])
            self.assertIsNone(row["parameter_types"])
            self.assertIs(row["observed_syntax"]["source_free"], True)
            self.assertEqual(row["observed_syntax"]["function_names"], [])
            self.assertEqual(row["observed_syntax"]["conditional_forms"], [])
            for field in ("expected_value", "expected_null", "output_columns", "parameter_values"):
                self.assertNotIn(field, row)

    def test_fixed_six_types_and_twenty_two_unit_spellings(self):
        entries = [row["observed_syntax"]["temporal_extractions"][0] for row in self.records]
        self.assertEqual(Counter(entry["declared_type"] for entry in entries),
                         {"date": 22, "time": 6, "timetz": 9, "interval": 9,
                          "timestamp": 2, "timestamptz": 2})
        self.assertEqual({entry["field"] for entry in entries}, EXTRACT_SOURCE_FIELDS)
        self.assertEqual([(entry["declared_type"], entry["field"], entry["literal"])
                          for entry in entries if "infinity" in entry["literal"]],
                         [("date", "day", "infinity"), ("date", "epoch", "infinity")])

    def test_observer_records_literal_text_without_evaluating_it(self):
        for literal in ("infinity", "not a valid date", "2020-08-11"):
            observed = observe_temporal_extractions(query(literal=literal))
            self.assertEqual(observed, {"source_free": True, "temporal_extractions": [
                {"field": "day", "declared_type": "date", "literal": literal}]})

    def test_catalog_parameter_and_expression_arguments_are_not_source_free_literals(self):
        for arg in ({"ColumnRef": {"fields": [{"String": {"sval": "d"}}]}},
                    {"ParamRef": {"number": 1}}, {"SQLValueFunction": {"op": "SVFOP_CURRENT_DATE"}},
                    {"FuncCall": {"funcname": [{"String": {"sval": "now"}}]}}):
            tree = query()
            call(tree)["args"][1] = arg
            with self.subTest(arg=arg), self.assertRaises(ValueError):
                observe_temporal_extractions(tree)

    def test_calls_and_arithmetic_hidden_inside_casts_are_rejected(self):
        for arg in ({"A_Expr": {}}, {"FuncCall": {}}, {"SubLink": {}}):
            tree = query()
            call(tree)["args"][1]["TypeCast"]["arg"] = arg
            with self.assertRaises(ValueError):
                observe_temporal_extractions(tree)

    def test_interval_field_qualifiers_type_modifiers_and_arrays_remain_separate(self):
        for key, value in (("typmods", [{"A_Const": {"ival": {"ival": 32767}}}]),
                           ("arrayBounds", [{"Integer": {"ival": -1}}]),
                           ("names", [{"String": {"sval": "custom"}}, {"String": {"sval": "date"}}])):
            tree = query()
            call(tree)["args"][1]["TypeCast"]["typeName"][key] = value
            with self.subTest(key=key), self.assertRaises(ValueError):
                observe_temporal_extractions(tree)

    def test_ordinary_qualified_call_cannot_impersonate_extract_syntax(self):
        for key, value in (("funcformat", "COERCE_EXPLICIT_CALL"),
                           ("funcname", [{"String": {"sval": "extract"}}]),
                           ("over", {}), ("agg_distinct", True)):
            tree = query()
            call(tree)[key] = value
            with self.subTest(key=key), self.assertRaises(ValueError):
                observe_temporal_extractions(tree)

    def test_query_shape_cannot_hide_tables_aliases_grouping_or_additional_projections(self):
        for mutation in ("from", "alias", "group", "projection", "set"):
            tree = query()
            if mutation == "from":
                tree["SelectStmt"]["fromClause"] = [{"RangeVar": {"relname": "dates"}}]
            elif mutation == "alias":
                tree["SelectStmt"]["targetList"][0]["ResTarget"]["name"] = "x"
            elif mutation == "group":
                tree["SelectStmt"]["groupClause"] = []
            elif mutation == "projection":
                tree["SelectStmt"]["targetList"] *= 2
            else:
                tree["SelectStmt"]["op"] = "SETOP_UNION"
            with self.subTest(mutation=mutation), self.assertRaises(ValueError):
                observe_temporal_extractions(tree)

    def test_malformed_field_literal_and_observation_metadata_fail_closed(self):
        for field, value in (("field", []), ("field", "fortnight"),
                             ("declared_type", "jsonb"), ("literal", None)):
            entries = [{"field": "day", "declared_type": "date", "literal": "2020-08-11"}]
            entries[0][field] = value
            with self.subTest(field=field, value=value), self.assertRaises(ValueError):
                validate_temporal_extractions(entries)
        with self.assertRaises(ValueError):
            validate_temporal_extractions([])

    def test_population_changes_cannot_silently_reduce_type_unit_or_infinity_coverage(self):
        for mutation in ("unit", "type", "infinity", "scope", "duplicate"):
            rows = deepcopy(self.records)
            if mutation == "unit":
                rows[0]["observed_syntax"]["temporal_extractions"][0]["field"] = "day"
            elif mutation == "type":
                rows[0]["observed_syntax"]["temporal_extractions"][0]["declared_type"] = "timestamp"
            elif mutation == "infinity":
                entry = next(row["observed_syntax"]["temporal_extractions"][0] for row in rows
                             if row["observed_syntax"]["temporal_extractions"][0]["literal"] == "infinity")
                entry["literal"] = "2000-01-01"
            elif mutation == "scope":
                rows[0]["observed_syntax"]["source_free"] = False
            else:
                rows[-1] = deepcopy(rows[0])
            with self.subTest(mutation=mutation), self.assertRaises(ValueError):
                validate_population(rows, "extract")

    def test_changed_source_selector_sql_hash_and_license_hash_are_rejected(self):
        for mutation in ("selector", "sql", "license"):
            manifest = deepcopy(self.manifest)
            if mutation == "selector":
                manifest["selections"][0]["selector"]["end"] -= 1
            elif mutation == "sql":
                manifest["selections"][0]["sql_sha256"] = "0" * 64
            else:
                manifest["sources"]["postgres"]["license_sha256"] = "0" * 64
            with self.subTest(mutation=mutation), self.assertRaises(ValueError):
                extract(manifest, "extract")


if __name__ == "__main__":
    unittest.main()
