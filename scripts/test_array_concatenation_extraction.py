"""Whole-source provenance and finite array-concatenation syntax observations."""
from collections import Counter
from copy import deepcopy
import json
import unittest

from extract_factor_corpus import (
    ROOT, extract, observe_array_concatenations, render,
    validate_array_concatenations, validate_population,
)
from extract_pagination_corpus import comparison_key


def scalar(value=1):
    return {"A_Const": {"ival": {"ival": value}}}


def array(*values):
    return {"A_ArrayExpr": {"elements": list(values) or [scalar()]}}


def cast(value=None, name="int4", rank=1):
    return {"TypeCast": {"arg": array() if value is None else value, "typeName": {
        "names": [{"String": {"sval": "pg_catalog"}}, {"String": {"sval": name}}],
        "arrayBounds": [{"Integer": {"ival": -1}}] * rank,
    }}}


def concat(left=None, right=None):
    return {"A_Expr": {"kind": "AEXPR_OP", "name": [{"String": {"sval": "||"}}],
                       "lexpr": array() if left is None else left,
                       "rexpr": array() if right is None else right}}


def query(*values):
    return {"SelectStmt": {"targetList": list(values)}}


class ArrayConcatenationExtractionTests(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        cls.directory = ROOT / "fixtures/array_concatenation"
        cls.manifest = json.loads((cls.directory / "concrete_sources.json").read_text())
        cls.records = extract(cls.manifest, "array_concatenation")

    def test_fifty_originals_reproduce_from_postgres_and_apache_licensed_risingwave(self):
        self.assertEqual(render(self.records), (self.directory / "concrete.jsonl").read_text())
        self.assertEqual(Counter(row["source"] for row in self.records), {"postgres": 8, "risingwave": 42})
        self.assertEqual(Counter(row["source_file"] for row in self.records), {
            "src/test/regress/sql/arrays.sql": 8,
            "e2e_test/batch/functions/array_concat.slt.part": 42,
        })
        self.assertEqual(self.manifest["sources"]["risingwave"]["license"], "Apache-2.0")
        self.assertEqual(self.manifest["sources"]["risingwave"]["commit"],
                         "7c5bb80f065b52e3eeaab0e0739684772d48aafc")
        for row in self.records:
            self.assertEqual(row["source_kind"], "engine-regression")
            self.assertEqual(row["sql"], row["raw_sql"])
            self.assertEqual(row["transformations"], [])
            self.assertEqual(row["observed_parameter_slots"], [])
            self.assertIsNone(row["parameter_types"])
            self.assertEqual(row["application_schema_validity"], "not-claimed")
            self.assertIs(row["observed_syntax"]["source_free"], True)
            self.assertEqual(row["observed_syntax"]["function_names"], [])
            self.assertEqual(row["observed_syntax"]["conditional_forms"], [])
            for field in ("expected_value", "parameter_values", "output_columns"):
                self.assertNotIn(field, row)

    def test_slt_queries_preserve_complete_bytes_but_never_import_expected_values(self):
        for row in self.records[8:]:
            self.assertEqual(row["extraction"], "sqllogic_query")
            self.assertEqual(row["query_header"], "query T")
            self.assertEqual(row["source_dialect"], "risingwave")
            self.assertTrue(row["sql"].endswith(";\n"))
            self.assertNotIn("----", row["sql"])
            self.assertNotIn("expected", row)
        for row in self.records[:8]:
            self.assertEqual(row["source"], "postgres")

    def test_two_chains_and_declared_type_mix_remain_exact(self):
        nodes = [entry for row in self.records for entry in row["observed_syntax"]["array_concatenations"]]
        self.assertEqual(len(nodes), 52)
        self.assertEqual(sum(len(row["observed_syntax"]["array_concatenations"]) == 2
                             for row in self.records), 2)
        self.assertEqual(Counter(entry["left"]["form"] for entry in nodes),
                         {"TypeCast": 41, "A_ArrayExpr": 7, "A_Const": 2, "A_Expr": 2})
        self.assertEqual(Counter(entry["right"]["form"] for entry in nodes),
                         {"TypeCast": 41, "A_ArrayExpr": 9, "A_Const": 2})
        names = {entry[side]["declared_type"] for entry in nodes for side in ("left", "right")}
        self.assertEqual(names, {None, "pg_catalog.int2", "pg_catalog.int4", "pg_catalog.int8",
                                 "pg_catalog.numeric", "pg_catalog.float4", "pg_catalog.varchar",
                                 "pg_catalog.timestamp", "date"})

    def test_no_whole_grammar_duplicate_and_aliases_are_not_rewritten(self):
        old = {comparison_key(json.loads(line)["sql"]) for line in
               (ROOT / "fixtures/statement_families/concrete.jsonl").read_text().splitlines()}
        self.assertFalse(old.intersection(comparison_key(row["sql"]) for row in self.records))
        self.assertIn('AS "{0,1,2,3}"', self.records[6]["sql"])
        self.assertIn('AS "ARRAY"', self.records[3]["sql"])
        self.assertTrue(any("timestamp with time zone" in row["sql"] for row in self.records))

    def test_nested_constructor_and_concat_types_are_not_inferred(self):
        result = observe_array_concatenations(query(concat(concat(array(array())), scalar())))
        self.assertIs(result["source_free"], True)
        nodes = result["array_concatenations"]
        self.assertEqual(len(nodes), 2)
        self.assertEqual(nodes[0]["left"], {"form": "A_Expr", "declared_type": None, "array_rank": None})
        self.assertEqual(nodes[1]["left"], {"form": "A_ArrayExpr", "declared_type": None, "array_rank": None})

    def test_scalar_and_array_cast_suffixes_are_distinguished_without_runtime_rank_claim(self):
        nodes = observe_array_concatenations(query(concat(cast(rank=1), cast(scalar(), rank=0))))[
            "array_concatenations"]
        self.assertEqual(nodes[0]["left"], {"form": "TypeCast", "declared_type": "pg_catalog.int4", "array_rank": 1})
        self.assertEqual(nodes[0]["right"], {"form": "TypeCast", "declared_type": "pg_catalog.int4", "array_rank": 0})

    def test_scalar_concat_and_foreign_or_qualified_operators_are_not_selected(self):
        with self.assertRaisesRegex(ValueError, "no explicit array"):
            observe_array_concatenations(query(concat(scalar(), scalar())))
        for names in (["+"], ["@>"], ["custom", "||"]):
            value = concat()
            value["A_Expr"]["name"] = [{"String": {"sval": name}} for name in names]
            with self.subTest(names=names), self.assertRaisesRegex(ValueError, "another operator"):
                observe_array_concatenations(query(value))

    def test_missing_operands_custom_and_sized_casts_are_outside_this_population(self):
        missing = concat()
        missing["A_Expr"].pop("rexpr")
        with self.assertRaisesRegex(ValueError, "two expression operands"):
            observe_array_concatenations(query(missing))
        with self.assertRaisesRegex(ValueError, "explicit"):
            observe_array_concatenations(query(concat(cast(name="custom"))))
        sized = cast()
        sized["TypeCast"]["typeName"]["arrayBounds"][0]["Integer"]["ival"] = 3
        with self.assertRaisesRegex(ValueError, "sized"):
            observe_array_concatenations(query(concat(sized)))

    def test_source_dependencies_hidden_in_any_child_are_rejected(self):
        for kind in ("ColumnRef", "ParamRef", "FuncCall", "SubLink", "RowExpr", "A_Indirection", "A_Indices"):
            with self.subTest(kind=kind), self.assertRaisesRegex(ValueError, "outside"):
                observe_array_concatenations(query(concat(), {kind: {"present": True}}))
        for key in ("fromClause", "withClause", "larg", "rarg", "valuesLists"):
            tree = query(concat())
            tree["SelectStmt"][key] = {"present": True}
            with self.subTest(key=key), self.assertRaisesRegex(ValueError, "source-free"):
                observe_array_concatenations(tree)

    def test_observations_cannot_retype_constructors_or_invent_rank_and_overloads(self):
        valid = observe_array_concatenations(query(concat(cast())))["array_concatenations"]
        bad = [[], [{**valid[0], "overload": "array_cat"}]]
        for key, value in (("form", "ColumnRef"), ("declared_type", "int"),
                           ("array_rank", True), ("array_rank", 2)):
            item = deepcopy(valid)
            item[0]["left"][key] = value
            bad.append(item)
        item = deepcopy(valid)
        item[0]["right"]["array_rank"] = 1
        bad.append(item)
        for entries in bad:
            with self.subTest(entries=entries), self.assertRaises(ValueError):
                validate_array_concatenations(entries)

    def test_population_rejects_dropped_chain_forged_scope_and_cast_rank_drift(self):
        for mutation in ("chain", "scope", "rank"):
            records = deepcopy(self.records)
            if mutation == "chain":
                records[5]["observed_syntax"]["array_concatenations"].pop()
            elif mutation == "scope":
                records[0]["observed_syntax"]["source_free"] = 1
            else:
                row = next(row for row in records if row["observed_syntax"]["array_concatenations"][0]["left"]["form"] == "TypeCast")
                row["observed_syntax"]["array_concatenations"][0]["left"]["array_rank"] ^= 1
            with self.subTest(mutation=mutation), self.assertRaises(ValueError):
                validate_population(records, "array_concatenation")

    def test_source_hash_license_and_complete_slt_boundaries_are_enforced(self):
        for mutation in ("sql", "source", "license", "boundary"):
            manifest = deepcopy(self.manifest)
            if mutation == "sql":
                manifest["selections"][0]["sql_sha256"] = "0" * 64
            elif mutation == "source":
                manifest["sources"]["risingwave"]["files"][0]["sha256"] = "0" * 64
            elif mutation == "license":
                manifest["sources"]["risingwave"]["license_sha256"] = "0" * 64
            else:
                manifest["selections"][8]["selector"]["end"] -= 1
            with self.subTest(mutation=mutation), self.assertRaises(ValueError):
                extract(manifest, "array_concatenation")

    def test_slt_source_format_authority_cannot_leak_to_other_projects(self):
        manifest = deepcopy(self.manifest)
        manifest["selections"][0]["selector"] = manifest["selections"][8]["selector"]
        with self.assertRaisesRegex(ValueError, "explicit source factor"):
            extract(manifest, "array_concatenation")


if __name__ == "__main__":
    unittest.main()
