"""Provenance and finite-source syntax checks for JSON extraction operators."""
from collections import Counter
from copy import deepcopy
import json
import unittest

from extract_factor_corpus import (
    ROOT, extract, observe_json_extractions, render, validate_json_extractions,
    validate_population,
)
from extract_pagination_corpus import comparison_key


def string(value="a"):
    return {"A_Const": {"sval": {"sval": value}}}


def cast(value, name="jsonb"):
    return {"TypeCast": {"arg": value, "typeName": {
        "names": [{"String": {"sval": part}} for part in name.split(".")],
    }}}


def extraction(left=None, right=None, operator="->"):
    return {"A_Expr": {"kind": "AEXPR_OP", "name": [{"String": {"sval": operator}}],
                       "lexpr": cast(string('{"a":1}')) if left is None else left,
                       "rexpr": string() if right is None else right}}


def query(*values):
    return {"SelectStmt": {"targetList": list(values)}}


class JsonExtractionSourcesTests(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        cls.directory = ROOT / "fixtures/json_extraction"
        cls.manifest = json.loads((cls.directory / "concrete_sources.json").read_text())
        cls.records = extract(cls.manifest, "json_extraction")

    def test_fifty_whole_originals_reproduce_from_two_existing_pins(self):
        self.assertEqual(render(self.records), (self.directory / "concrete.jsonl").read_text())
        self.assertEqual(Counter(row["source"] for row in self.records), {"postgres": 50})
        self.assertEqual(Counter(row["source_file"] for row in self.records), {
            "src/test/regress/sql/json.sql": 25, "src/test/regress/sql/jsonb.sql": 25,
        })
        self.assertEqual(len(self.manifest["sources"]["postgres"]["files"]), 2)
        for row in self.records:
            self.assertEqual(row["source_kind"], "engine-regression")
            self.assertEqual(row["sql"], row["raw_sql"])
            self.assertEqual(row["transformations"], [])
            self.assertEqual(row["observed_parameter_slots"], [])
            self.assertIsNone(row["parameter_types"])
            self.assertEqual(row["application_schema_validity"], "not-claimed")
            self.assertEqual(row["observed_syntax"]["function_names"], [])
            self.assertEqual(row["observed_syntax"]["conditional_forms"], [])
            for field in ("expected_value", "parameter_values", "output_columns"):
                self.assertNotIn(field, row)

    def test_all_four_operators_both_declared_types_and_nested_accesses_are_retained(self):
        entries = [entry for row in self.records for entry in row["observed_syntax"]["json_extractions"]]
        self.assertEqual(len(entries), 52)
        self.assertEqual(Counter(entry["operator"] for entry in entries),
                         {"->": 15, "->>": 11, "#>": 12, "#>>": 14})
        self.assertEqual(Counter(entry["left_form"] for entry in entries), {"TypeCast": 50, "A_Expr": 2})
        self.assertEqual(Counter(entry["left_cast"] for entry in entries),
                         {"pg_catalog.json": 25, "jsonb": 25, None: 2})
        self.assertEqual(Counter(entry["right_form"] for entry in entries),
                         {"A_Const": 27, "A_ArrayExpr": 17, "TypeCast": 8})
        self.assertEqual(Counter(entry["right_cast"] for entry in entries),
                         {None: 44, "text": 4, "pg_catalog.int4": 4})

    def test_negative_indexes_typed_nulls_and_array_paths_are_original_source_text(self):
        statements = [row["sql"] for row in self.records]
        self.assertEqual(sum("-> -1" in sql for sql in statements), 2)
        self.assertEqual(sum("null::text" in sql for sql in statements), 4)
        self.assertEqual(sum("null::int" in sql for sql in statements), 4)
        self.assertEqual(sum("array['a', null]" in sql for sql in statements), 4)
        self.assertTrue(any("#> '{c,-1}'" in sql for sql in statements))
        self.assertTrue(any("-> 3 -> 1" in sql for sql in statements))
        self.assertFalse(any(" FROM " in sql.upper() for sql in statements))

    def test_no_whole_grammar_population_duplicate(self):
        old = {comparison_key(json.loads(line)["sql"]) for line in
               (ROOT / "fixtures/statement_families/concrete.jsonl").read_text().splitlines()}
        self.assertFalse(old.intersection(comparison_key(row["sql"]) for row in self.records))

    def test_nested_nodes_keep_preorder_and_do_not_invent_an_intermediate_type(self):
        tree = query(extraction(extraction(), string("value"), "->>"))
        self.assertEqual(observe_json_extractions(tree), [
            {"operator": "->>", "left_form": "A_Expr", "left_cast": None,
             "right_form": "A_Const", "right_cast": None},
            {"operator": "->", "left_form": "TypeCast", "left_cast": "jsonb",
             "right_form": "A_Const", "right_cast": None},
        ])

    def test_null_key_and_array_path_remain_syntax_not_computed_results(self):
        null = {"A_Const": {"isnull": True}}
        array = {"A_ArrayExpr": {"elements": [string(), null]}}
        tree = query(extraction(right=cast(null, "text")),
                     extraction(cast(string("null"), "pg_catalog.json"), array, "#>>"))
        entries = observe_json_extractions(tree)
        self.assertEqual(entries[0]["right_cast"], "text")
        self.assertEqual(entries[1]["right_form"], "A_ArrayExpr")
        self.assertIsNone(entries[1]["right_cast"])
        self.assertTrue(all("result" not in key for entry in entries for key in entry))

    def test_json_literal_error_screen_rejects_malformed_documents_without_sql_execution(self):
        for document in ("{bad}", "[1,]", "NaN", "Infinity", "-Infinity"):
            with self.subTest(document=document), self.assertRaises(ValueError):
                observe_json_extractions(query(extraction(cast(string(document)))))
        for document in ("null", "42", '"foo"', '{"a":[1,null]}'):
            with self.subTest(document=document):
                self.assertEqual(len(observe_json_extractions(query(extraction(cast(string(document)))))), 1)

    def test_source_free_scope_rejects_tables_calls_parameters_rows_and_subqueries(self):
        good = extraction()
        for kind in ("ColumnRef", "ParamRef", "FuncCall", "SubLink", "RowExpr", "A_Indirection", "A_Indices"):
            with self.subTest(kind=kind), self.assertRaisesRegex(ValueError, "outside"):
                observe_json_extractions(query(good, {kind: {"test": True}}))
        tree = query(good)
        tree["SelectStmt"]["fromClause"] = [{"RangeVar": {"relname": "app"}}]
        with self.assertRaisesRegex(ValueError, "source-free"):
            observe_json_extractions(tree)

    def test_foreign_operators_and_schema_qualified_operator_names_are_excluded(self):
        for operator in ("?", "?|", "?&", "@>", "<@", "#-", "+", "||"):
            with self.subTest(operator=operator), self.assertRaisesRegex(ValueError, "another operator"):
                observe_json_extractions(query(extraction(operator=operator)))
        tree = extraction()
        tree["A_Expr"]["name"].insert(0, {"String": {"sval": "pg_catalog"}})
        with self.assertRaisesRegex(ValueError, "another operator"):
            observe_json_extractions(query(tree))

    def test_missing_operands_unknown_declared_types_and_explicit_array_casts_fail(self):
        tree = extraction()
        tree["A_Expr"].pop("rexpr")
        with self.assertRaisesRegex(ValueError, "two expression operands"):
            observe_json_extractions(query(tree))
        with self.assertRaisesRegex(ValueError, "explicit"):
            observe_json_extractions(query(extraction(cast(string("{}"), "text"))))
        array = cast(string("{}"), "text")
        array["TypeCast"]["typeName"]["arrayBounds"] = [{"Integer": {"ival": -1}}]
        with self.assertRaisesRegex(ValueError, "array cast"):
            observe_json_extractions(query(extraction(right=array, operator="#>")))

    def test_metadata_cannot_infer_result_types_or_retype_noncast_operands(self):
        valid = {"operator": "->", "left_form": "TypeCast", "left_cast": "jsonb",
                 "right_form": "A_Const", "right_cast": None}
        invalid = [[], [{**valid, "result_type": "jsonb"}], [{**valid, "operator": ["->"]}],
                   [{**valid, "left_form": True}], [{**valid, "right_cast": "text"}],
                   [{**valid, "left_cast": "custom"}], [{**valid, "right_form": "ParamRef"}]]
        for entries in invalid:
            with self.subTest(entries=entries), self.assertRaises(ValueError):
                validate_json_extractions(entries)

    def test_population_cannot_drop_nested_node_or_change_type_mix(self):
        records = deepcopy(self.records)
        row = next(row for row in records if len(row["observed_syntax"]["json_extractions"]) > 1)
        row["observed_syntax"]["json_extractions"].pop()
        with self.assertRaisesRegex(ValueError, "52 nodes"):
            validate_population(records, "json_extraction")
        records = deepcopy(self.records)
        records[0]["observed_syntax"]["json_extractions"][0]["left_cast"] = "jsonb"
        with self.assertRaisesRegex(ValueError, "52 nodes"):
            validate_population(records, "json_extraction")

    def test_exact_source_hash_and_complete_statement_boundaries_are_enforced(self):
        manifest = deepcopy(self.manifest)
        manifest["selections"][0]["selector"]["end"] -= 1
        with self.assertRaisesRegex(ValueError, "complete"):
            extract(manifest, "json_extraction")
        manifest = deepcopy(self.manifest)
        manifest["selections"][0]["sql_sha256"] = "0" * 64
        with self.assertRaisesRegex(ValueError, "SQL hash"):
            extract(manifest, "json_extraction")


if __name__ == "__main__":
    unittest.main()
