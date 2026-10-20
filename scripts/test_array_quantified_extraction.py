"""Offline whole-source identity and spelling checks for array quantifiers."""
from collections import Counter
from copy import deepcopy
import json
import unittest

from extract_factor_corpus import (
    ROOT, extract, observe_array_quantified, render,
    validate_array_quantified, validate_population,
)
from extract_pagination_corpus import comparison_key


def query(*nodes):
    return {"SelectStmt": {"targetList": list(nodes)}}


def quantified(sql, source_operator="=", quantifier="ANY", right=None):
    """Handbuilt raw-parser-shaped node with a UTF-8 byte position."""
    offset = sql.index(source_operator)
    return {"A_Expr": {
        "kind": "AEXPR_OP_ALL" if quantifier == "ALL" else "AEXPR_OP_ANY",
        "name": [{"String": {"sval": "<>" if source_operator == "!=" else source_operator}}],
        "location": len(sql[:offset].encode("utf-8")),
        "lexpr": {"A_Const": {"ival": {"ival": 1}}},
        "rexpr": right or {"A_ArrayExpr": {"elements": [{"A_Const": {"ival": {"ival": 1}}}]}},
    }}


class ArrayQuantifiedExtractionTests(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        cls.directory = ROOT / "fixtures/array_quantified"
        cls.manifest = json.loads((cls.directory / "concrete_sources.json").read_text())
        cls.records = extract(cls.manifest, "array_quantified")

    def test_fifty_unchanged_sources_reproduce_without_fabricated_bindings(self):
        self.assertEqual(render(self.records), (self.directory / "concrete.jsonl").read_text())
        self.assertEqual(Counter(row["source"] for row in self.records),
                         {"hatchet": 29, "postgres": 18, "sqlc": 3})
        self.assertEqual(Counter(row["source_kind"] for row in self.records),
                         {"application-constant": 29, "engine-regression": 18, "compiler-regression": 3})
        self.assertEqual(sum(len(source["files"]) for source in self.manifest["sources"].values()), 14)
        self.assertEqual(sum(bool(row["observed_parameter_slots"]) for row in self.records), 32)
        for row in self.records:
            self.assertEqual(row["raw_sql"], row["sql"])
            self.assertEqual(row["transformations"], [])
            self.assertIsNone(row["parameter_types"])
            self.assertNotIn("parameter_values", row)
            self.assertEqual(row["application_schema_validity"], "not-claimed")

    def test_source_coverage_preserves_actual_gaps_and_normalized_not_equal(self):
        nodes = [node for row in self.records for node in row["observed_syntax"]["array_quantified"]]
        self.assertEqual(len(nodes), 51)
        self.assertEqual(Counter(node["quantifier"] for node in nodes), {"any": 41, "all": 10})
        self.assertEqual(Counter(node["source_operator"] for node in nodes),
                         {"=": 45, ">=": 4, "!=": 1, ">": 1})
        self.assertEqual([node["operator"] for node in nodes if node["source_operator"] == "!="], ["<>"])
        self.assertEqual(Counter(node["right_form"] for node in nodes),
                         {"TypeCast": 34, "A_Const": 13, "ParamRef": 2, "A_ArrayExpr": 2})

    def test_queries_are_new_beyond_the_whole_grammar_fixture(self):
        old = {comparison_key(json.loads(line)["sql"]) for line in
               (ROOT / "fixtures/statement_families/concrete.jsonl").read_text().splitlines()}
        self.assertFalse(old.intersection(comparison_key(row["sql"]) for row in self.records))

    def test_utf8_byte_locations_do_not_alias_character_offsets(self):
        sql = "SELECT 'é雪'::TEXT = SOME(ARRAY['a','é雪']);"
        node = quantified(sql, quantifier="SOME")
        self.assertNotEqual(node["A_Expr"]["location"], sql.index("="))
        self.assertEqual(observe_array_quantified(query(node), sql), [{
            "operator": "=", "source_operator": "=", "quantifier": "some", "right_form": "A_ArrayExpr",
        }])
        node["A_Expr"]["location"] = sql.index("=")
        with self.assertRaisesRegex(ValueError, "source spelling"):
            observe_array_quantified(query(node), sql)

    def test_comments_preserve_source_operator_and_some_alias(self):
        sql = "SELECT 1 != /* >= ALL(ARRAY[2]) /* nested */ */ SoMe -- comment\n (ARRAY[2]);"
        self.assertEqual(observe_array_quantified(query(quantified(sql, "!=")), sql), [{
            "operator": "<>", "source_operator": "!=", "quantifier": "some", "right_form": "A_ArrayExpr",
        }])

    def test_order_and_rhs_forms_are_preserved(self):
        sql = "SELECT 1 = ANY($1), 2 >= ALL('{1,2}');"
        first = quantified(sql, right={"ParamRef": {"number": 1}})
        second = quantified(sql, ">=", "ALL", {"A_Const": {"sval": {"sval": "{1,2}"}}})
        self.assertEqual(observe_array_quantified(query(first, second), sql), [
            {"operator": "=", "source_operator": "=", "quantifier": "any", "right_form": "ParamRef"},
            {"operator": ">=", "source_operator": ">=", "quantifier": "all", "right_form": "A_Const"},
        ])

    def test_comment_and_quoted_text_cannot_supply_fake_operator_spelling(self):
        for sql in ("SELECT '= ANY(ARRAY[1])';", 'SELECT "= ANY(ARRAY[1])";',
                    "SELECT $body$= ANY(ARRAY[1])$body$;", "SELECT 1 /* = ANY(ARRAY[1]) */;"):
            with self.subTest(sql=sql), self.assertRaisesRegex(ValueError, "source spelling"):
                observe_array_quantified(query(quantified(sql)), sql)
        with self.assertRaisesRegex(ValueError, "factor is absent"):
            observe_array_quantified(query({"A_Const": {"sval": {"sval": "= ANY(ARRAY[1])"}}}),
                                     "SELECT '= ANY(ARRAY[1])';")

    def test_malformed_offsets_and_mid_utf8_offsets_are_rejected(self):
        sql = "SELECT 'é' = ANY(ARRAY['é']);"
        for offset in (None, True, -1, len(sql.encode()), 9):
            node = quantified(sql)
            node["A_Expr"]["location"] = offset
            with self.subTest(offset=offset), self.assertRaisesRegex(ValueError, "byte location"):
                observe_array_quantified(query(node), sql)

    def test_raw_ast_operator_and_quantifier_must_match_source(self):
        sql = "SELECT 1 = ANY(ARRAY[1]);"
        mutations = [
            {"kind": "AEXPR_OP_ALL"},
            {"name": [{"String": {"sval": ">="}}]},
            {"name": [{"String": {"sval": "OPERATOR"}}, {"String": {"sval": "="}}]},
            {"name": [{"String": {"sval": "~~"}}]},
        ]
        for mutation in mutations:
            node = quantified(sql)
            node["A_Expr"].update(mutation)
            with self.subTest(mutation=mutation), self.assertRaises(ValueError):
                observe_array_quantified(query(node), sql)

    def test_later_forms_cannot_hide_in_an_operand_or_other_query_clause(self):
        sql = "SELECT 1 = ANY(ARRAY[1]);"
        later = [{"A_Indices": {}}, {"A_Indirection": {}}, {"RowExpr": {"args": []}},
                 {"SubLink": {"subLinkType": "ARRAY_SUBLINK"}},
                 {"SubLink": {"subLinkType": "ANY_SUBLINK"}},
                 {"SubLink": {"subLinkType": "EXPR_SUBLINK"}}]
        for node in later:
            for tree in (query(quantified(sql, right=node)), query(quantified(sql), node)):
                with self.subTest(node=node), self.assertRaisesRegex(ValueError, "outside"):
                    observe_array_quantified(tree, sql)

    def test_observation_schema_rejects_invented_semantic_metadata(self):
        valid = {"operator": "=", "source_operator": "=", "quantifier": "any", "right_form": "TypeCast"}
        invalid = [[], [{**valid, "operator": "~~"}], [{**valid, "source_operator": "<>"}],
                   [{**valid, "quantifier": "each"}], [{**valid, "right_form": "SubLink"}],
                   [{**valid, "strict": True}], [{**valid, "operator": ["="]}]]
        for nodes in invalid:
            with self.subTest(nodes=nodes), self.assertRaises(ValueError):
                validate_array_quantified(nodes)

    def test_population_cannot_claim_some_sources_or_lose_right_operand_forms(self):
        for field, value in (("quantifier", "some"), ("right_form", "A_Const"),
                             ("source_operator", ">=")):
            records = deepcopy(self.records)
            entry = records[0]["observed_syntax"]["array_quantified"][0]
            entry[field] = value
            if field == "source_operator":
                entry["operator"] = value
            with self.subTest(field=field), self.assertRaisesRegex(ValueError, "51 nodes"):
                validate_population(records, "array_quantified")

    def test_source_hashes_and_complete_statement_boundaries_are_enforced(self):
        manifest = deepcopy(self.manifest)
        selection = next(row for row in manifest["selections"] if row["selector"]["kind"] == "sql_slice")
        selection["selector"]["end"] -= 1
        with self.assertRaisesRegex(ValueError, "complete statement"):
            extract(manifest, "array_quantified")
        manifest = deepcopy(self.manifest)
        manifest["selections"][0]["sql_sha256"] = "0" * 64
        with self.assertRaisesRegex(ValueError, "SQL hash"):
            extract(manifest, "array_quantified")


if __name__ == "__main__":
    unittest.main()
