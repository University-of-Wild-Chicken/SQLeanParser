"""Offline source-identity and structural boundary tests for ARRAY constructors."""
from collections import Counter
from copy import deepcopy
import json
import unittest

from extract_factor_corpus import (
    ROOT, extract, observe_array_constructors, render,
    validate_array_constructors, validate_population,
)
from extract_pagination_corpus import comparison_key


def array(*items):
    return {"A_ArrayExpr": {"elements": list(items)}}


def query(*items, **clauses):
    return {"SelectStmt": {"targetList": list(items), **clauses}}


def cast(arg, is_array=True):
    return {"TypeCast": {"arg": arg, "typeName": {
        "names": [{"String": {"sval": "text"}}],
        "arrayBounds": [{"Integer": {"ival": -1}}] if is_array else [],
    }}}


def integer(value):
    return {"A_Const": {"ival": {"ival": value}}}


class ArrayConstructorExtractionTests(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        cls.directory = ROOT / "fixtures/array_constructors"
        cls.manifest = json.loads((cls.directory / "concrete_sources.json").read_text())
        cls.records = extract(cls.manifest, "array_constructors")

    def test_fifty_whole_sources_reproduce_with_no_sql_rewrites_or_execution_bindings(self):
        self.assertEqual(render(self.records), (self.directory / "concrete.jsonl").read_text())
        self.assertEqual(Counter(row["source"] for row in self.records), {"postgres": 49, "sqlc": 1})
        self.assertEqual(sum(len(source["files"]) for source in self.manifest["sources"].values()), 4)
        for row in self.records:
            self.assertEqual(row["raw_sql"], row["sql"])
            self.assertEqual(row["transformations"], [])
            self.assertEqual(row["observed_parameter_slots"], [])
            self.assertIsNone(row["parameter_types"])
            self.assertNotIn("parameter_values", row)
            self.assertEqual(row["application_schema_validity"], "not-claimed")

    def test_nesting_and_typed_empty_coverage_are_pinned(self):
        nodes = [node for row in self.records for node in row["observed_syntax"]["array_constructors"]]
        self.assertEqual(len(nodes), 94)
        self.assertEqual(Counter(node["depth"] for node in nodes),
                         {1: 62, 2: 23, 3: 2, 4: 2, 5: 2, 6: 3})
        empty = [row for row in self.records if any(
            node["length"] == 0 for node in row["observed_syntax"]["array_constructors"])]
        self.assertEqual(len(empty), 1)
        self.assertEqual(empty[0]["sql"], "select array[]::text[];")
        self.assertEqual(empty[0]["observed_syntax"]["array_constructors"],
                         [{"depth": 1, "length": 0, "array_cast_context": True}])
        sql = "\n".join(row["sql"].lower() for row in self.records)
        self.assertIn("array[array[", sql)
        self.assertIn("array[[", sql)

    def test_concrete_queries_are_new_beyond_the_whole_grammar_fixture(self):
        old = {comparison_key(json.loads(line)["sql"]) for line in
               (ROOT / "fixtures/statement_families/concrete.jsonl").read_text().splitlines()}
        self.assertFalse(old.intersection(comparison_key(row["sql"]) for row in self.records))

    def test_constructor_depth_is_not_flattened_across_lists_or_calls(self):
        tree = query(array(array(integer(1), integer(2)), array(integer(3), integer(4))),
                     {"FuncCall": {"args": [array(integer(5))]}})
        self.assertEqual(observe_array_constructors(tree), [
            {"depth": 1, "length": 2, "array_cast_context": False},
            {"depth": 2, "length": 2, "array_cast_context": False},
            {"depth": 2, "length": 2, "array_cast_context": False},
            {"depth": 1, "length": 1, "array_cast_context": False},
        ])

    def test_array_cast_context_flows_into_nested_constructor_members(self):
        tree = query(cast(array(array(), array())))
        self.assertEqual(observe_array_constructors(tree), [
            {"depth": 1, "length": 2, "array_cast_context": True},
            {"depth": 2, "length": 0, "array_cast_context": True},
            {"depth": 2, "length": 0, "array_cast_context": True},
        ])

    def test_cast_context_cannot_leak_through_function_calls_or_scalar_casts(self):
        bad = [
            query(array()),
            query(cast(array(), is_array=False)),
            query(cast({"FuncCall": {"args": [array()]}})),
            query(cast(array({"FuncCall": {"args": [array()]}}))),
        ]
        for tree in bad:
            with self.subTest(tree=tree), self.assertRaisesRegex(ValueError, "constructor observation"):
                observe_array_constructors(tree)

    def test_later_forms_cannot_hide_in_a_constructor(self):
        later = [
            {"A_Indices": {}}, {"A_Indirection": {}}, {"RowExpr": {"args": []}},
            {"SubLink": {"subLinkType": "ARRAY_SUBLINK"}},
            {"SubLink": {"subLinkType": "EXPR_SUBLINK"}},
            {"A_Expr": {"kind": "AEXPR_OP_ANY"}},
            {"A_Expr": {"kind": "AEXPR_OP_ALL"}},
        ]
        for node in later:
            with self.subTest(node=node), self.assertRaisesRegex(ValueError, "later constructor factor"):
                observe_array_constructors(query(array(node)))

    def test_source_query_clauses_are_outside_this_finite_population(self):
        for field in ("fromClause", "withClause", "groupClause", "havingClause",
                      "larg", "rarg", "valuesLists", "lockingClause"):
            with self.subTest(field=field), self.assertRaisesRegex(ValueError, "source-free"):
                observe_array_constructors(query(array(integer(1)), **{field: [integer(1)]}))
        with self.assertRaisesRegex(ValueError, "must be a SELECT"):
            observe_array_constructors({"InsertStmt": array(integer(1))})

    def test_quoted_array_text_does_not_create_an_observation(self):
        with self.assertRaisesRegex(ValueError, "factor is absent"):
            observe_array_constructors(query({"A_Const": {"sval": {"sval": "ARRAY[1]"}}}))

    def test_metadata_shape_rejects_boolean_counts_and_invented_type_ranks(self):
        valid = {"depth": 1, "length": 2, "array_cast_context": False}
        bad = [
            [], [{**valid, "rank": 1}], [{**valid, "depth": True}], [{**valid, "depth": 0}],
            [{**valid, "length": True}], [{**valid, "length": -1}],
            [{**valid, "length": 0}], [{**valid, "array_cast_context": 1}],
        ]
        for nodes in bad:
            with self.subTest(nodes=nodes), self.assertRaises(ValueError):
                validate_array_constructors(nodes)

    def test_population_cannot_lose_empty_or_deep_constructor_coverage(self):
        for field in ("empty", "depth", "node"):
            records = deepcopy(self.records)
            if field == "node":
                records[0]["observed_syntax"]["array_constructors"].append(
                    {"depth": 1, "length": 1, "array_cast_context": False})
            else:
                for row in records:
                    for node in row["observed_syntax"]["array_constructors"]:
                        if field == "depth":
                            node["depth"] = min(node["depth"], 5)
                        elif node["length"] == 0:
                            node["length"] = 1
            with self.subTest(field=field), self.assertRaisesRegex(ValueError, "94 nodes, typed empty"):
                validate_population(records, "array_constructors")

    def test_sql_fragments_and_changed_source_hashes_are_rejected(self):
        manifest = deepcopy(self.manifest)
        selection = next(row for row in manifest["selections"] if row["selector"]["kind"] == "sql_slice")
        selection["selector"]["end"] -= 1
        with self.assertRaisesRegex(ValueError, "complete statement"):
            extract(manifest, "array_constructors")
        manifest = deepcopy(self.manifest)
        manifest["selections"][0]["sql_sha256"] = "0" * 64
        with self.assertRaisesRegex(ValueError, "SQL hash"):
            extract(manifest, "array_constructors")


if __name__ == "__main__":
    unittest.main()
