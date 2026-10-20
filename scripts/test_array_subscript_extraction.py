"""Offline source identity and subscript-group boundary tests."""
from collections import Counter
from copy import deepcopy
import json
import unittest

from extract_factor_corpus import (
    ROOT, extract, observe_array_subscripts, render,
    validate_array_subscripts, validate_population,
)
from extract_pagination_corpus import comparison_key


def integer(value=1):
    return {"A_Const": {"ival": {"ival": value}}}


def index(upper=None):
    return {"A_Indices": {"uidx": integer() if upper is None else upper}}


def slice_(lower=None, upper=None):
    return {"A_Indices": {"is_slice": True, **({"lidx": lower} if lower else {}),
                          **({"uidx": upper} if upper else {})}}


def access(*indices, base=None):
    return {"A_Indirection": {"arg": base or {"ColumnRef": {"fields": [{"String": {"sval": "a"}}]}},
                              "indirection": list(indices)}}


def query(*nodes):
    return {"SelectStmt": {"targetList": list(nodes)}}


class ArraySubscriptExtractionTests(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        cls.directory = ROOT / "fixtures/array_subscripts"
        cls.manifest = json.loads((cls.directory / "concrete_sources.json").read_text())
        cls.records = extract(cls.manifest, "array_subscripts")

    def test_fifty_whole_sources_reproduce_without_borrowed_execution_results(self):
        self.assertEqual(render(self.records), (self.directory / "concrete.jsonl").read_text())
        self.assertEqual(Counter(row["source"] for row in self.records), {"postgres": 24, "duckdb": 26})
        self.assertEqual(sum(len(source["files"]) for source in self.manifest["sources"].values()), 5)
        for row in self.records:
            self.assertEqual(row["source_kind"], "engine-regression")
            self.assertEqual(row["raw_sql"], row["sql"])
            self.assertEqual(row["transformations"], [])
            self.assertEqual(row["observed_parameter_slots"], [])
            self.assertIsNone(row["parameter_types"])
            self.assertEqual(row["application_schema_validity"], "not-claimed")
            for field in ("parameter_values", "expected_value", "output_columns"):
                self.assertNotIn(field, row)
            if row["source"] == "duckdb":
                self.assertEqual(row["source_dialect"], "duckdb")
                self.assertEqual(row["extraction"], "sqllogic_query")
                self.assertTrue(row["sql"].endswith("\n"))

    def test_exact_group_and_bound_coverage_excludes_the_seven_dimension_negative(self):
        groups = [group for row in self.records for group in row["observed_syntax"]["array_subscripts"]]
        self.assertEqual(len(groups), 76)
        self.assertEqual(Counter(len(group["dimensions"]) for group in groups), {1: 47, 2: 17, 3: 12})
        self.assertEqual(Counter(group["depth"] for group in groups), {1: 73, 2: 3})
        self.assertEqual(Counter("slice" if dim["slice"] else "element" for group in groups for dim in group["dimensions"]),
                         {"element": 71, "slice": 46})
        self.assertFalse(any("[1][2][3][4][5][6][7]" in row["sql"] for row in self.records))

    def test_existing_domain_and_scalar_subquery_contexts_stay_rendering_only(self):
        domains = [row for row in self.records if row["source_file"].endswith("/domain.sql")]
        subqueries = [row for row in self.records if row["source_file"].endswith("/subselect.sql")]
        self.assertEqual(len(domains), 6)
        self.assertEqual(len(subqueries), 3)
        self.assertTrue(any("(f1[1])[1]" in row["sql"] for row in domains))
        self.assertTrue(all("SELECT ARRAY[1,2,3]" in row["sql"] for row in subqueries))
        self.assertTrue(all(row["application_schema_validity"] == "not-claimed" for row in domains + subqueries))

    def test_queries_are_new_beyond_the_whole_grammar_fixture(self):
        old = {comparison_key(json.loads(line)["sql"]) for line in
               (ROOT / "fixtures/statement_families/concrete.jsonl").read_text().splitlines()}
        self.assertFalse(old.intersection(comparison_key(row["sql"]) for row in self.records))

    def test_grouped_dimensions_are_distinct_from_nested_access(self):
        element = {"slice": False, "lower": False, "upper": True}
        self.assertEqual(observe_array_subscripts(query(access(index(), index()))),
                         [{"depth": 1, "dimensions": [element, element]}])
        self.assertEqual(observe_array_subscripts(query(access(index(), base=access(index())))), [
            {"depth": 1, "dimensions": [element]}, {"depth": 2, "dimensions": [element]},
        ])

    def test_optional_bounds_and_mixed_slice_dimensions_keep_source_shape(self):
        tree = query(access(slice_(), slice_(integer(0)), slice_(upper=integer()),
                            slice_(integer(), integer()), index()))
        self.assertEqual(observe_array_subscripts(tree), [{"depth": 1, "dimensions": [
            {"slice": True, "lower": False, "upper": False},
            {"slice": True, "lower": True, "upper": False},
            {"slice": True, "lower": False, "upper": True},
            {"slice": True, "lower": True, "upper": True},
            {"slice": False, "lower": False, "upper": True},
        ]}])

    def test_null_is_a_present_bound_and_not_an_omitted_bound(self):
        null = {"A_Const": {"isnull": True}}
        self.assertEqual(observe_array_subscripts(query(access(slice_(null, null)))), [
            {"depth": 1, "dimensions": [{"slice": True, "lower": True, "upper": True}]},
        ])

    def test_expression_subquery_is_observed_but_quantified_and_array_subqueries_fail(self):
        scalar = {"SubLink": {"subLinkType": "EXPR_SUBLINK", "subselect": query(integer())}}
        self.assertEqual(len(observe_array_subscripts(query(access(index(), base=scalar)))), 1)
        for kind in ("ANY_SUBLINK", "ALL_SUBLINK", "ARRAY_SUBLINK", "EXISTS_SUBLINK"):
            base = {"SubLink": {"subLinkType": kind, "subselect": query(integer())}}
            with self.subTest(kind=kind), self.assertRaisesRegex(ValueError, "outside"):
                observe_array_subscripts(query(access(index(), base=base)))

    def test_record_fields_rows_and_known_scalar_bases_do_not_enter_population(self):
        bad = [
            query({"A_Indirection": {"arg": integer(), "indirection": [{"String": {"sval": "field"}}]}}),
            query(access(index(), base={"RowExpr": {"args": [integer()]}})),
            query(access(index(), base={"FuncCall": {"funcname": [{"String": {"sval": "now"}}]}})),
            query(access(index(), base={"TypeCast": {"arg": integer(), "typeName": {"names": []}}})),
        ]
        for tree in bad:
            with self.subTest(tree=tree), self.assertRaisesRegex(ValueError, "outside"):
                observe_array_subscripts(tree)

    def test_dimension_limit_and_metadata_shapes_reject_invented_rank_claims(self):
        valid = {"depth": 1, "dimensions": [{"slice": False, "lower": False, "upper": True}]}
        invalid = [[], [{**valid, "depth": True}], [{**valid, "depth": 0}], [{**valid, "rank": 1}],
                   [{**valid, "dimensions": []}], [{**valid, "dimensions": valid["dimensions"] * 7}],
                   [{"depth": 1, "dimensions": [{"slice": 1, "lower": False, "upper": True}]}],
                   [{"depth": 1, "dimensions": [{"slice": False, "lower": False, "upper": False}]}]]
        for groups in invalid:
            with self.subTest(groups=groups), self.assertRaises(ValueError):
                validate_array_subscripts(groups)
        with self.assertRaisesRegex(ValueError, "group"):
            observe_array_subscripts(query(access(*(index() for _ in range(7)))))

    def test_population_cannot_drop_slice_or_nested_group_coverage(self):
        for mutation in ("slice", "depth", "group"):
            records = deepcopy(self.records)
            for row in records:
                for group in row["observed_syntax"]["array_subscripts"]:
                    if mutation == "depth":
                        group["depth"] = 1
                    elif mutation == "slice":
                        group["dimensions"] = [{"slice": False, "lower": False, "upper": True}
                                               for _ in group["dimensions"]]
            if mutation == "group":
                records[0]["observed_syntax"]["array_subscripts"].pop()
            with self.subTest(mutation=mutation), self.assertRaisesRegex(ValueError, "117 dimensions"):
                validate_population(records, "array_subscripts")

    def test_complete_source_block_and_file_hash_identity_are_enforced(self):
        for kind in ("sqllogic_query", "sql_slice"):
            manifest = deepcopy(self.manifest)
            selection = next(row for row in manifest["selections"] if row["selector"]["kind"] == kind)
            selection["selector"]["end"] -= 1
            with self.subTest(kind=kind), self.assertRaisesRegex(ValueError, "complete"):
                extract(manifest, "array_subscripts")
        manifest = deepcopy(self.manifest)
        manifest["sources"]["duckdb"]["files"][0]["sha256"] = "0" * 64
        with self.assertRaisesRegex(ValueError, "hash|digest"):
            extract(manifest, "array_subscripts")


if __name__ == "__main__":
    unittest.main()
