"""Finite containment source selection, provenance, and scope regression checks."""
from collections import Counter
from copy import deepcopy
import json
import unittest

from extract_factor_corpus import (
    ROOT, extract, observe_json_containments, render, validate_json_containments,
    validate_population,
)
from extract_pagination_corpus import comparison_key


def string(value="{}"):
    return {"A_Const": {"sval": {"sval": value}}}


def cast(value=None, name="jsonb"):
    return {"TypeCast": {"arg": string() if value is None else value,
                         "typeName": {"names": [{"String": {"sval": name}}]}}}


def containment(left=None, right=None, operator="@>"):
    return {"A_Expr": {"kind": "AEXPR_OP", "name": [{"String": {"sval": operator}}],
                       "lexpr": cast() if left is None else left,
                       "rexpr": string() if right is None else right}}


def query(*values, table=None):
    result = {"targetList": list(values)}
    if table:
        result["fromClause"] = [{"RangeVar": {"relname": table}}]
    return {"SelectStmt": result}


class JsonContainmentSourcesTests(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        cls.directory = ROOT / "fixtures/json_containment"
        cls.manifest = json.loads((cls.directory / "concrete_sources.json").read_text())
        cls.records = extract(cls.manifest, "json_containment")

    def test_fifty_complete_originals_reproduce_from_one_existing_pin(self):
        self.assertEqual(render(self.records), (self.directory / "concrete.jsonl").read_text())
        self.assertEqual(Counter(row["source"] for row in self.records), {"postgres": 50})
        self.assertEqual({row["source_file"] for row in self.records}, {"src/test/regress/sql/jsonb.sql"})
        self.assertEqual(len(self.manifest["sources"]["postgres"]["files"]), 1)
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

    def test_fixed_literal_ids_are_not_chosen_by_validation_success(self):
        numbers = [139, 140, 141, 142, 143, 145, 146, 147, 148, 149, 150, 151,
                   159, 160, 161, 162, 163, 165, 166, 167, 168, 169, 170, 171, 172,
                   *range(641, 658)]
        self.assertEqual([row["statement_index"] for row in self.records[:42]], numbers)
        self.assertEqual([row["statement_index"] for row in self.records[42:]],
                         [499, 500, 501, 502, 503, 665, 666, 667])
        self.assertEqual([row["observed_syntax"]["source_free"] for row in self.records],
                         [True] * 42 + [False] * 8)

    def test_both_directions_and_explicit_operand_declarations_are_retained(self):
        entries = [entry for row in self.records for entry in row["observed_syntax"]["json_containments"]]
        self.assertEqual(len(entries), 50)
        self.assertEqual(Counter(entry["operator"] for entry in entries), {"@>": 41, "<@": 9})
        self.assertEqual(Counter(entry["left_form"] for entry in entries), {"TypeCast": 42, "ColumnRef": 8})
        self.assertEqual(Counter(entry["right_form"] for entry in entries), {"A_Const": 41, "TypeCast": 9})
        self.assertEqual(Counter(entry["left_cast"] for entry in entries), {"jsonb": 42, None: 8})
        self.assertEqual(Counter(entry["right_cast"] for entry in entries), {"jsonb": 9, None: 41})
        self.assertEqual(sum("count(*)" in row["sql"] for row in self.records), 5)
        self.assertEqual(sum("select * from nestjsonb" in row["sql"] for row in self.records), 3)

    def test_no_whole_grammar_population_duplicate(self):
        old = {comparison_key(json.loads(line)["sql"]) for line in
               (ROOT / "fixtures/statement_families/concrete.jsonl").read_text().splitlines()}
        self.assertFalse(old.intersection(comparison_key(row["sql"]) for row in self.records))

    def test_literal_vs_table_scope_does_not_assign_a_column_type(self):
        literal = observe_json_containments(query(containment()))
        self.assertTrue(literal["source_free"])
        column = {"ColumnRef": {"fields": [{"String": {"sval": "j"}}]}}
        table = observe_json_containments(query(containment(column), table="example"))
        self.assertFalse(table["source_free"])
        self.assertEqual(table["json_containments"], [
            {"operator": "@>", "left_form": "ColumnRef", "left_cast": None,
             "right_form": "A_Const", "right_cast": None}])
        with self.assertRaisesRegex(ValueError, "source-free"):
            observe_json_containments(query(containment(column)))

    def test_both_document_operands_are_screened_without_sql_execution(self):
        for document in ("{bad}", "[1,]", "NaN", "Infinity", "-Infinity"):
            for side in ("left", "right"):
                with self.subTest(document=document, side=side), self.assertRaises(ValueError):
                    observe_json_containments(query(containment(**{
                        side: cast(string(document)) if side == "left" else string(document)})))
        for document in ("null", "42", '"foo"', '{"a":[1,null]}'):
            self.assertTrue(observe_json_containments(query(containment(right=string(document))))["source_free"])

    def test_arrays_ranges_json_and_missing_operands_do_not_masquerade_as_jsonb(self):
        for name in ("int4", "int4range", "json", "custom"):
            with self.subTest(name=name), self.assertRaisesRegex(ValueError, "explicit"):
                observe_json_containments(query(containment(cast(name=name))))
        array = cast()
        array["TypeCast"]["typeName"]["arrayBounds"] = [{"Integer": {"ival": -1}}]
        with self.assertRaisesRegex(ValueError, "array cast"):
            observe_json_containments(query(containment(array)))
        missing = containment()
        missing["A_Expr"].pop("rexpr")
        with self.assertRaisesRegex(ValueError, "two expression operands"):
            observe_json_containments(query(missing))

    def test_other_and_qualified_operators_are_not_selected_by_spelling_suffix(self):
        for operator in ("?", "?|", "?&", "->", "#>", "#-", "+", "||"):
            with self.subTest(operator=operator), self.assertRaisesRegex(ValueError, "another operator"):
                observe_json_containments(query(containment(operator=operator)))
        qualified = containment()
        qualified["A_Expr"]["name"].insert(0, {"String": {"sval": "custom"}})
        with self.assertRaisesRegex(ValueError, "another operator"):
            observe_json_containments(query(qualified))

    def test_hidden_later_dependencies_and_source_free_calls_are_excluded(self):
        for kind in ("ParamRef", "SubLink", "RowExpr", "A_ArrayExpr", "A_Indirection", "A_Indices"):
            with self.subTest(kind=kind), self.assertRaisesRegex(ValueError, "outside"):
                observe_json_containments(query(containment(), {kind: {"test": True}}))
        count = {"FuncCall": {"funcname": [{"String": {"sval": "count"}}], "agg_star": True}}
        with self.assertRaisesRegex(ValueError, "call"):
            observe_json_containments(query(containment(), count))
        self.assertFalse(observe_json_containments(query(containment(), count, table="t"))["source_free"])
        count["FuncCall"]["funcname"][0]["String"]["sval"] = "custom"
        with self.assertRaisesRegex(ValueError, "call"):
            observe_json_containments(query(containment(), count, table="t"))

    def test_ctes_sets_derived_and_qualified_tables_are_outside_this_finite_screen(self):
        for key in ("withClause", "larg", "rarg", "valuesLists"):
            tree = query(containment())
            tree["SelectStmt"][key] = {"present": True}
            with self.subTest(key=key), self.assertRaisesRegex(ValueError, "outside"):
                observe_json_containments(tree)
        for source in ({"RangeSubselect": {}}, {"RangeVar": {"relname": "t", "schemaname": "app"}}):
            tree = query(containment())
            tree["SelectStmt"]["fromClause"] = [source]
            with self.assertRaisesRegex(ValueError, "outside"):
                observe_json_containments(tree)
        tree = query(containment(), table="t")
        tree["SelectStmt"]["fromClause"] *= 2
        with self.assertRaisesRegex(ValueError, "multiple tables"):
            observe_json_containments(tree)

    def test_metadata_cannot_infer_results_or_retype_untyped_operands(self):
        valid = {"operator": "@>", "left_form": "TypeCast", "left_cast": "jsonb",
                 "right_form": "A_Const", "right_cast": None}
        for invalid in ([], [{**valid, "result_type": "boolean"}], [{**valid, "operator": ["@>"]}],
                        [{**valid, "left_form": True}], [{**valid, "right_cast": "jsonb"}],
                        [{**valid, "left_cast": "json"}], [{**valid, "right_form": "ParamRef"}]):
            with self.subTest(invalid=invalid), self.assertRaises(ValueError):
                validate_json_containments(invalid)

    def test_population_rejects_forged_scope_changed_operator_and_missing_node(self):
        for value in (False, 1, "true"):
            records = deepcopy(self.records)
            records[0]["observed_syntax"]["source_free"] = value
            with self.subTest(value=value), self.assertRaises(ValueError):
                validate_population(records, "json_containment")
        records = deepcopy(self.records)
        records[0]["observed_syntax"]["json_containments"][0]["operator"] = "<@"
        with self.assertRaisesRegex(ValueError, "50 nodes"):
            validate_population(records, "json_containment")
        records[0]["observed_syntax"]["json_containments"] = []
        with self.assertRaisesRegex(ValueError, "absent"):
            validate_population(records, "json_containment")

    def test_exact_source_hash_and_complete_statement_boundaries_are_enforced(self):
        manifest = deepcopy(self.manifest)
        manifest["selections"][0]["selector"]["end"] -= 1
        with self.assertRaisesRegex(ValueError, "complete"):
            extract(manifest, "json_containment")
        manifest = deepcopy(self.manifest)
        manifest["selections"][0]["sql_sha256"] = "0" * 64
        with self.assertRaisesRegex(ValueError, "SQL hash"):
            extract(manifest, "json_containment")


if __name__ == "__main__":
    unittest.main()
