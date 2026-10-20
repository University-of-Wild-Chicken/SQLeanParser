"""Offline provenance and syntax-boundary tests for unchanged || sources."""
from collections import Counter
from copy import deepcopy
import json
import unittest

from extract_factor_corpus import (
    ROOT, extract, observe_concatenations, render, validate_concatenations,
    validate_population,
)
from extract_pagination_corpus import comparison_key


def string(value="text"):
    return {"A_Const": {"sval": {"sval": value}}}


def cast(value, name, *, array=False):
    return {"TypeCast": {"arg": value, "typeName": {
        "names": [{"String": {"sval": part}} for part in name.split(".")],
        **({"arrayBounds": [{"Integer": {"ival": -1}}]} if array else {}),
    }}}


def concat(left, right, names=("||",), kind="AEXPR_OP"):
    return {"A_Expr": {"kind": kind, "name": [{"String": {"sval": part}} for part in names],
                       "lexpr": left, "rexpr": right}}


def query(*values):
    return {"SelectStmt": {"targetList": list(values)}}


class ConcatenationExtractionTests(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        cls.directory = ROOT / "fixtures/concatenation"
        cls.manifest = json.loads((cls.directory / "concrete_sources.json").read_text())
        cls.records = extract(cls.manifest, "concatenation")

    def test_exact_fifty_originals_reproduce_with_pinned_sources_and_no_invented_catalog(self):
        self.assertEqual(render(self.records), (self.directory / "concrete.jsonl").read_text())
        self.assertEqual(Counter(row["source"] for row in self.records),
                         {"hatchet": 1, "postgres": 49})
        self.assertEqual(Counter(row["source_kind"] for row in self.records),
                         {"application-constant": 1, "engine-regression": 49})
        self.assertEqual(sum(len(source["files"]) for source in self.manifest["sources"].values()), 8)
        for row in self.records:
            self.assertEqual(row["sql"], row["raw_sql"])
            self.assertEqual(row["transformations"], [])
            self.assertEqual(row["observed_parameter_slots"], [])
            self.assertIsNone(row["parameter_types"])
            self.assertEqual(row["application_schema_validity"], "not-claimed")
            for field in ("expected_value", "parameter_values", "output_columns", "operator_signature"):
                self.assertNotIn(field, row)

    def test_eighty_six_nodes_retain_exact_forms_and_immediate_declarations(self):
        entries = [entry for row in self.records for entry in row["observed_syntax"]["concatenations"]]
        self.assertEqual(len(entries), 86)
        self.assertEqual(Counter(entry["left"]["form"] for entry in entries),
                         {"A_Expr": 35, "TypeCast": 30, "A_Const": 15, "FuncCall": 5, "ColumnRef": 1})
        self.assertEqual(Counter(entry["right"]["form"] for entry in entries),
                         {"A_Const": 39, "FuncCall": 25, "TypeCast": 20, "A_Expr": 2})
        self.assertEqual(Counter(entry[side]["declared_type"] for entry in entries for side in ("left", "right")
                                 if entry[side]["declared_type"] is not None),
                         {"jsonb": 42, "text": 4, "pg_catalog.bpchar": 2,
                          "pg_catalog.varchar": 1, "bytea": 1})

    def test_jsonb_bytea_and_mixed_text_sources_are_not_renamed_or_synthesized(self):
        self.assertEqual(sum(row["source_file"].endswith("/jsonb.sql") for row in self.records), 28)
        bytea = [row for row in self.records if row["source_file"].endswith("/rijndael.sql")]
        self.assertEqual([row["sql"] for row in bytea], [
            "select encode(decrypt(encrypt('foo', '0123456', 'aes') || '\\x00'::bytea, "
            "'0123456', 'aes'), 'escape');",
        ])
        text = [row["sql"] for row in self.records if row["source_file"].endswith("/text.sql")]
        self.assertEqual(text, ["select 'four: '::text || 2+2;", "select 'four: ' || 2+2;"])
        self.assertNotIn("select 3 || 4.0;", [row["sql"] for row in self.records])
        hatchet = next(row for row in self.records if row["source"] == "hatchet")
        self.assertEqual(hatchet["symbol"], "checkBloat")
        self.assertIn("quote_ident(schemaname)||'.'||quote_ident(relname)", hatchet["sql"])

    def test_no_duplicates_of_whole_grammar_population(self):
        old = {comparison_key(json.loads(line)["sql"]) for line in
               (ROOT / "fixtures/statement_families/concrete.jsonl").read_text().splitlines()}
        self.assertFalse(old.intersection(comparison_key(row["sql"]) for row in self.records))

    def test_nested_operators_preserve_preorder_and_operand_sides(self):
        tree = query(concat(concat(cast(string("{}"), "jsonb"), string("{}")),
                            cast(string("text"), "text")))
        self.assertEqual(observe_concatenations(tree), [
            {"left": {"form": "A_Expr", "declared_type": None},
             "right": {"form": "TypeCast", "declared_type": "text"}},
            {"left": {"form": "TypeCast", "declared_type": "jsonb"},
             "right": {"form": "A_Const", "declared_type": None}},
        ])

    def test_functions_columns_and_unknown_literals_do_not_acquire_types(self):
        tree = query(concat({"FuncCall": {"funcname": [{"String": {"sval": "custom"}}]}},
                            {"ColumnRef": {"fields": [{"String": {"sval": "value"}}]}}),
                     concat(string("1"), string("2")))
        entries = observe_concatenations(tree)
        self.assertEqual([entry["left"]["form"] for entry in entries], ["FuncCall", "A_Const"])
        self.assertTrue(all(entry[side]["declared_type"] is None
                            for entry in entries for side in ("left", "right")))

    def test_literal_operator_text_does_not_count_and_nonselect_is_rejected(self):
        with self.assertRaisesRegex(ValueError, "absent"):
            observe_concatenations(query(string("a || b")))
        with self.assertRaisesRegex(ValueError, "SELECT"):
            observe_concatenations({"DeleteStmt": {"whereClause": concat(string(), string())}})

    def test_schema_qualified_and_other_extended_operators_are_not_silently_included(self):
        good = concat(string(), string())
        for names in (("pg_catalog", "||"), ("->>",), ("@",), ("^",)):
            with self.subTest(names=names), self.assertRaisesRegex(ValueError, "extended operator"):
                observe_concatenations(query(good, concat(string(), string(), names)))

    def test_array_row_and_quantified_subquery_dependencies_are_excluded(self):
        good = concat(string(), string())
        later = [cast(string("{}"), "text", array=True),
                 {"A_ArrayExpr": {"elements": [string()]}},
                 {"A_Indirection": {"arg": string(), "indirection": []}},
                 {"RowExpr": {"args": [string()]}}]
        later += [{"SubLink": {"subLinkType": kind}} for kind in
                  ("ARRAY_SUBLINK", "ANY_SUBLINK", "ALL_SUBLINK", "ROWCOMPARE_SUBLINK")]
        for value in later:
            with self.subTest(value=value), self.assertRaisesRegex(ValueError, "outside"):
                observe_concatenations(query(good, value))

    def test_missing_operands_and_unknown_casts_are_rejected(self):
        for tree in (query(concat(None, string())),
                     query(concat({}, string())),
                     query(concat(cast(string(), "custom_type"), string()))):
            with self.subTest(tree=tree), self.assertRaises(ValueError):
                observe_concatenations(tree)

    def test_metadata_cannot_invent_resolved_types_or_unknown_overloads(self):
        valid = {"left": {"form": "A_Const", "declared_type": None},
                 "right": {"form": "TypeCast", "declared_type": "jsonb"}}
        bad = [[], [{**valid, "result_type": "jsonb"}]]
        for side, form, declared in (("left", "A_Const", "text"),
                                     ("right", "TypeCast", None),
                                     ("right", "TypeCast", ["jsonb"]),
                                     ("left", ["A_Const"], None),
                                     ("left", "UnknownNode", None)):
            entry = deepcopy(valid)
            entry[side] = {"form": form, "declared_type": declared}
            bad.append([entry])
        for entries in bad:
            with self.subTest(entries=entries), self.assertRaises(ValueError):
                validate_concatenations(entries)

    def test_population_cannot_drop_node_or_change_explicit_declaration(self):
        records = deepcopy(self.records)
        records[0]["observed_syntax"]["concatenations"].pop()
        with self.assertRaisesRegex(ValueError, "86 nodes"):
            validate_population(records, "concatenation")
        records = deepcopy(self.records)
        entry = next(entry for row in records for entry in row["observed_syntax"]["concatenations"]
                     if entry["left"]["declared_type"] == "jsonb")
        entry["left"]["declared_type"] = "text"
        with self.assertRaisesRegex(ValueError, "86 nodes"):
            validate_population(records, "concatenation")

    def test_source_hash_and_whole_statement_boundaries_are_enforced(self):
        manifest = deepcopy(self.manifest)
        selection = next(entry for entry in manifest["selections"] if entry["selector"]["kind"] == "sql_slice")
        selection["selector"]["end"] -= 1
        with self.assertRaisesRegex(ValueError, "complete"):
            extract(manifest, "concatenation")
        manifest = deepcopy(self.manifest)
        manifest["selections"][0]["sql_sha256"] = "0" * 64
        with self.assertRaisesRegex(ValueError, "SQL hash"):
            extract(manifest, "concatenation")


if __name__ == "__main__":
    unittest.main()
