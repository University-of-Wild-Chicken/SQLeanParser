"""Offline regressions for the closed array-type source population."""
from collections import Counter
from copy import deepcopy
import json
import unittest

from extract_factor_corpus import (
    ARRAY_ELEMENT_FAMILIES, ROOT, extract, observe_array_types, render,
    validate_array_types, validate_population,
)
from extract_pagination_corpus import comparison_key


def array_type(name="int4", bounds=(-1,), modifiers=(), namespace="pg_catalog"):
    names = ([namespace] if namespace is not None else []) + [name]
    return {"typeName": {
        "names": [{"String": {"sval": part}} for part in names],
        "arrayBounds": [{"Integer": {"ival": bound}} for bound in bounds],
        "typmods": [{"A_Const": {"ival": {"ival": value}}} for value in modifiers],
    }}


def query(*nodes):
    return {"SelectStmt": {"targetList": list(nodes)}}


class ArrayTypeExtractionTests(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        cls.directory = ROOT / "fixtures/array_types"
        cls.manifest = json.loads((cls.directory / "concrete_sources.json").read_text())
        cls.records = extract(cls.manifest, "array_types")

    def test_exact_fifty_sources_reproduce_without_rewrites_or_invented_bindings(self):
        self.assertEqual(render(self.records), (self.directory / "concrete.jsonl").read_text())
        self.assertEqual(Counter(row["source"] for row in self.records),
                         {"postgres": 42, "hatchet": 7, "sqlc": 1})
        self.assertEqual(sum(len(source["files"]) for source in self.manifest["sources"].values()), 9)
        for row in self.records:
            self.assertEqual(row["sql"], row["raw_sql"])
            self.assertEqual(row["transformations"], [])
            self.assertIsNone(row["parameter_types"])
            self.assertNotIn("parameter_values", row)
            self.assertEqual(row["application_schema_validity"], "not-claimed")

    def test_all_seven_element_families_and_sixty_five_occurrences_are_retained(self):
        observations = [entry for row in self.records for entry in row["observed_syntax"]["array_types"]]
        self.assertEqual(Counter(entry["element_type"] for entry in observations),
                         {"int4": 21, "text": 15, "float8": 15, "int8": 5,
                          "timestamptz": 4, "uuid": 3, "interval": 2})
        self.assertTrue(all(entry["bounds"] == [None] and not entry["modifiers"]
                            for entry in observations))
        self.assertEqual(sum(bool(row["observed_parameter_slots"]) for row in self.records), 8)

    def test_sources_add_fifty_queries_beyond_the_whole_grammar_fixture(self):
        old = {comparison_key(json.loads(line)["sql"]) for line in
               (ROOT / "fixtures/statement_families/concrete.jsonl").read_text().splitlines()}
        self.assertFalse(old.intersection(comparison_key(row["sql"]) for row in self.records))

    def test_declaration_order_modifiers_and_bounds_are_preserved_as_syntax(self):
        parsed = query(array_type("varchar", (-1, 3), (12,)),
                       array_type("numeric", (0,), (8, 4), namespace=None))
        self.assertEqual(observe_array_types(parsed), [
            {"element_type": "varchar", "modifiers": [12], "bounds": [None, 3]},
            {"element_type": "numeric", "modifiers": [8, 4], "bounds": [0]},
        ])

    def test_brackets_and_any_inside_text_are_not_array_type_nodes(self):
        with self.assertRaisesRegex(ValueError, "factor is absent"):
            observe_array_types(query({"A_Const": {"sval": {"sval": "int[] ARRAY[1] ANY"}}}))
        with self.assertRaisesRegex(ValueError, "must be a SELECT"):
            observe_array_types({"CreateStmt": array_type()})

    def test_constructors_subscripts_rows_and_quantifiers_cannot_hide_under_casts(self):
        later = [
            {"A_ArrayExpr": {"elements": []}},
            {"A_Indices": {"is_slice": True}},
            {"A_Indirection": {"indirection": []}},
            {"RowExpr": {"args": []}},
            {"A_Expr": {"kind": "AEXPR_OP_ANY"}},
            {"A_Expr": {"kind": "AEXPR_OP_ALL"}},
            *[{"SubLink": {"subLinkType": kind}} for kind in
              ("ARRAY_SUBLINK", "ANY_SUBLINK", "ALL_SUBLINK")],
        ]
        for node in later:
            with self.subTest(node=node), self.assertRaisesRegex(ValueError, "later factor"):
                observe_array_types(query({"TypeCast": {**array_type(), "arg": node}}))

    def test_user_defined_or_wrongly_qualified_array_elements_are_excluded(self):
        for node in (array_type("application_enum"), array_type(namespace="application"),
                     array_type(name="jsonb", namespace="pg_catalog.extra")):
            with self.subTest(node=node), self.assertRaisesRegex(ValueError, "built-in"):
                observe_array_types(query(node))

    def test_observer_rejects_noninteger_type_modifiers_and_bounds(self):
        bad_modifier = array_type()
        bad_modifier["typeName"]["typmods"] = [{"A_Const": {"sval": {"sval": "3"}}}]
        bad_bound = array_type()
        bad_bound["typeName"]["arrayBounds"] = [{"String": {"sval": "3"}}]
        for node in (bad_modifier, bad_bound, array_type(bounds=(True,)),
                     array_type(bounds=(-1.0,))):
            with self.subTest(node=node), self.assertRaisesRegex(ValueError, "non-integer"):
                observe_array_types(query(node))

    def test_metadata_shape_rejects_boolean_dimensions_and_invented_fields(self):
        valid = {"element_type": "int4", "modifiers": [], "bounds": [None]}
        malformed = [
            [], [{**valid, "rank": 1}], [{**valid, "element_type": "custom"}],
            [{**valid, "bounds": []}], [{**valid, "bounds": [True]}],
            [{**valid, "bounds": [-2]}], [{**valid, "bounds": "[]"}],
            [{**valid, "modifiers": [True]}], [{**valid, "modifiers": [-1]}],
        ]
        for types in malformed:
            with self.subTest(types=types), self.assertRaises(ValueError):
                validate_array_types(types)

    def test_loss_of_an_element_family_fails_closed(self):
        self.assertEqual(len(ARRAY_ELEMENT_FAMILIES), 7)
        records = deepcopy(self.records)
        for row in records:
            for entry in row["observed_syntax"]["array_types"]:
                if entry["element_type"] == "interval":
                    entry["element_type"] = "text"
        with self.assertRaisesRegex(ValueError, "seven pinned element"):
            validate_population(records, "array_types")

    def test_statement_fragment_and_hash_mutation_are_rejected(self):
        manifest = deepcopy(self.manifest)
        selection = next(row for row in manifest["selections"] if row["selector"]["kind"] == "sql_slice")
        selection["selector"]["end"] -= 1
        with self.assertRaisesRegex(ValueError, "complete statement"):
            extract(manifest, "array_types")
        manifest = deepcopy(self.manifest)
        manifest["selections"][0]["sql_sha256"] = "0" * 64
        with self.assertRaisesRegex(ValueError, "SQL hash"):
            extract(manifest, "array_types")


if __name__ == "__main__":
    unittest.main()
