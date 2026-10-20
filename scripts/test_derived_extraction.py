"""Offline checks for the finite non-LATERAL derived-source screen."""
from copy import deepcopy
import json
import unittest

from extract_factor_corpus import (
    ROOT, extract, observe_derived_queries, render, validate_derived_sources,
    validate_population,
)


def column(*parts):
    return {"ColumnRef": {"fields": [{"String": {"sval": part}} for part in parts]}}


def table(name, alias=None):
    return {"RangeVar": {"relname": name, "inh": True,
                         **({"alias": {"aliasname": alias}} if alias else {})}}


def query(targets=None, sources=None, **clauses):
    return {"SelectStmt": {"targetList": targets or [], "fromClause": sources or [], **clauses}}


def derived(child, alias="d", columns=(), **flags):
    return {"RangeSubselect": {"subquery": child,
                              "alias": {"aliasname": alias,
                                        "colnames": [{"String": {"sval": c}} for c in columns]},
                              **flags}}


class DerivedExtractionTests(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        cls.directory = ROOT / "fixtures/derived_contract"
        cls.manifest = json.loads((cls.directory / "concrete_sources.json").read_text())
        cls.records = extract(cls.manifest, "derived_contract")

    def test_fifty_sources_reproduce_without_invented_catalogs_or_rewrites(self):
        self.assertEqual(render(self.records), (self.directory / "concrete.jsonl").read_text())
        self.assertEqual(len(self.records), 50)
        self.assertEqual(sum(row["source"] == "postgres" for row in self.records), 47)
        self.assertEqual(sum(row["source"] == "sqlc" for row in self.records), 3)
        for row in self.records:
            self.assertEqual(row["raw_sql"], row["sql"])
            self.assertEqual(row["transformations"], [])
            self.assertIsNone(row["parameter_types"])
            self.assertEqual(row["application_schema_validity"], "not-claimed")
            self.assertNotIn("parameter_values", row)

    def test_alias_lists_and_three_levels_remain_in_the_population(self):
        sources = [source for row in self.records for source in row["observed_syntax"]["derived_sources"]]
        self.assertEqual(len(sources), 91)
        self.assertEqual({depth: sum(s["query_depth"] == depth for s in sources)
                          for depth in (1, 2, 3)}, {1: 75, 2: 12, 3: 4})
        self.assertEqual(sum(any(s["columns"] for s in row["observed_syntax"]["derived_sources"])
                             for row in self.records), 4)
        self.assertIn(["a", "b", "c"], [s["columns"] for s in sources])
        self.assertTrue(all(s["lateral"] is False for s in sources))

    def test_local_qualified_scopes_and_shadowed_names_are_independent(self):
        child = query([column("same", "id")], [table("inner_table", "same")])
        parent = query([column("same", "id"), column("d", "id")],
                       [table("outer_table", "same"), derived(child)])
        self.assertEqual(observe_derived_queries(parent),
                         [{"alias": "d", "columns": [], "query_depth": 1, "lateral": False}])

    def test_parent_and_sibling_names_cannot_supply_a_child_qualified_reference(self):
        for qualifier in ("outer", "sibling"):
            child = query([column(qualifier, "id")], [table("inner_table")])
            parent = query([], [table("outer"), derived(query(), "sibling"), derived(child)])
            with self.subTest(qualifier=qualifier), self.assertRaisesRegex(ValueError, "own derived-query scope"):
                observe_derived_queries(parent)

    def test_source_free_child_cannot_capture_unqualified_outer_column(self):
        parent = query([], [table("outer"), derived(query([column("outer_id")]))])
        with self.assertRaisesRegex(ValueError, "source-free derived query"):
            observe_derived_queries(parent)
        self.assertEqual(observe_derived_queries(query([], [derived(query())]))[0]["alias"], "d")

    def test_query_depth_and_renaming_order_are_not_flattened(self):
        deepest = query([column("t", "x")], [table("t")])
        middle = query([column("inner", "z")], [derived(deepest, "inner", ["z", "a"])])
        root = query([column("outer", "z")], [derived(middle, "outer")])
        self.assertEqual(observe_derived_queries(root), [
            {"alias": "outer", "columns": [], "query_depth": 1, "lateral": False},
            {"alias": "inner", "columns": ["z", "a"], "query_depth": 2, "lateral": False},
        ])

    def test_lateral_missing_alias_and_expression_subqueries_are_excluded(self):
        malformed = [
            query([], [derived(query(), lateral=True)]),
            query([], [{"RangeSubselect": {"subquery": query()}}]),
            query([{"SubLink": {"subselect": query()}}], [derived(query())]),
            query([{"FuncCall": {"funcname": [{"String": {"sval": "count"}}]}}],
                  [derived(query())]),
            query([], [derived(query([], [], groupClause=[column("x")]))]),
            query([], [derived({"InsertStmt": {}})]),
        ]
        for parsed in malformed:
            with self.subTest(parsed=parsed), self.assertRaises(ValueError):
                observe_derived_queries(parsed)

    def test_additional_source_forms_and_deeper_column_paths_are_not_misclassified(self):
        malformed = [
            query([], [derived(query([], [{"RangeFunction": {}}]))]),
            query([], [derived(query([], [{"RangeVar": {"relname": "t", "schemaname": "s"}}]))]),
            query([], [derived(query([column("schema", "t", "x")], [table("t")]))]),
            query([], [derived(query([], [{"RangeVar": {"relname": "t", "inh": False}}]))]),
            query([], [table("t")]),
        ]
        for parsed in malformed:
            with self.subTest(parsed=parsed), self.assertRaises(ValueError):
                observe_derived_queries(parsed)

    def test_observation_shape_rejects_lateral_boolean_depth_and_bad_aliases(self):
        valid = {"alias": "d", "columns": ["z", "a"], "query_depth": 1, "lateral": False}
        for key, value in (("alias", ""), ("columns", ["x", "x"]), ("columns", ["x", 1]),
                           ("columns", "x"), ("query_depth", 0), ("query_depth", True),
                           ("lateral", 0), ("lateral", True)):
            with self.subTest(key=key, value=value), self.assertRaisesRegex(ValueError, "derived source observation"):
                validate_derived_sources([{**valid, key: value}])
        with self.assertRaisesRegex(ValueError, "factor is absent"):
            validate_derived_sources([])

    def test_coverage_loss_in_alias_lists_or_nesting_fails_closed(self):
        for target in ("aliases", "nesting"):
            rows = deepcopy(self.records)
            for row in rows:
                for source in row["observed_syntax"]["derived_sources"]:
                    if target == "aliases":
                        source["columns"] = []
                    else:
                        source["query_depth"] = min(source["query_depth"], 2)
            with self.subTest(target=target), self.assertRaisesRegex(ValueError, "column aliases and depth-three"):
                validate_population(rows, "derived_contract")


if __name__ == "__main__":
    unittest.main()
