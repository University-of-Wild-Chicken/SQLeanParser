"""Offline identity and structural-boundary tests for row comparison sources."""
from collections import Counter
from copy import deepcopy
import json
import unittest

from extract_factor_corpus import (
    ROOT, extract, observe_row_comparisons, render,
    validate_population, validate_row_comparisons,
)
from extract_pagination_corpus import comparison_key


def integer(value=1):
    return {"A_Const": {"ival": {"ival": value}}}


def row(*fields, explicit=False):
    return {"RowExpr": {"args": list(fields),
                        "row_format": "COERCE_EXPLICIT_CALL" if explicit else "COERCE_IMPLICIT_CAST"}}


def compare(left, right, operator="=", kind="AEXPR_OP"):
    return {"A_Expr": {"kind": kind, "name": [{"String": {"sval": operator}}],
                       "lexpr": left, "rexpr": right}}


def query(*items):
    return {"SelectStmt": {"targetList": list(items)}}


class RowComparisonExtractionTests(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        cls.directory = ROOT / "fixtures/row_comparisons"
        cls.manifest = json.loads((cls.directory / "concrete_sources.json").read_text())
        cls.records = extract(cls.manifest, "row_comparisons")

    def test_fifty_unchanged_whole_queries_have_pinned_origins_and_no_invented_bindings(self):
        self.assertEqual(render(self.records), (self.directory / "concrete.jsonl").read_text())
        self.assertEqual(Counter(record["source"] for record in self.records),
                         {"hatchet": 16, "postgres": 8, "temporal": 6, "sqlite": 20})
        self.assertEqual(Counter(record["source_kind"] for record in self.records),
                         {"application-constant": 22, "engine-regression": 28})
        self.assertEqual(sum(len(source["files"]) for source in self.manifest["sources"].values()), 13)
        self.assertEqual(sum(bool(record["observed_parameter_slots"]) for record in self.records), 22)
        for record in self.records:
            self.assertEqual(record["raw_sql"], record["sql"])
            self.assertEqual(record["transformations"], [])
            self.assertIsNone(record["parameter_types"])
            self.assertEqual(record["application_schema_validity"], "not-claimed")
            for key in ("parameter_values", "expected_value", "output_columns"):
                self.assertNotIn(key, record)

    def test_exact_operator_arity_and_explicit_source_gaps_are_retained(self):
        pairs = [pair for record in self.records for pair in record["observed_syntax"]["row_comparisons"]]
        self.assertEqual(len(pairs), 72)
        self.assertEqual(Counter(pair["operator"] for pair in pairs),
                         {"=": 40, ">": 10, ">=": 9, "<=": 7, "<": 6})
        self.assertEqual(Counter(pair["arity"] for pair in pairs), {2: 56, 3: 12, 4: 3, 5: 1})
        self.assertEqual(Counter((pair["left_form"], pair["right_form"]) for pair in pairs),
                         {("implicit", "implicit"): 71, ("explicit", "explicit"): 1})
        self.assertEqual([record["sql"] for record in self.records if any(
            pair["left_form"] == "explicit" for pair in record["observed_syntax"]["row_comparisons"])],
            ["select ROW(1,2) = ROW(1,2::int8);"])

    def test_six_original_temporal_selects_retain_original_bytes_and_symbols(self):
        temporal = [record for record in self.records if record["source"] == "temporal"]
        expected_symbols = {
            "getHistoryNodesQuery", "getHistoryNodeMetadataQuery", "paginateBranchesQuery",
            "getTimerTasksQuery", "getTaskV2Qry", "getTaskV2QryWithLimit",
        }
        self.assertEqual({record["symbol"] for record in temporal}, expected_symbols)
        original = {record["symbol"]: record for record in (
            json.loads(line) for line in (ROOT / "fixtures/external_postgresql/temporal.jsonl").read_text().splitlines()
        )}
        for record in temporal:
            self.assertEqual(record["sql"], original[record["symbol"]]["raw_sql"])
            self.assertEqual(record["commit"], original[record["symbol"]]["commit"])

    def test_no_whole_grammar_fixture_duplicates_and_sqlite_results_are_not_metadata(self):
        old = {comparison_key(json.loads(line)["sql"]) for line in
               (ROOT / "fixtures/statement_families/concrete.jsonl").read_text().splitlines()}
        self.assertFalse(old.intersection(comparison_key(record["sql"]) for record in self.records))
        sqlite = [record for record in self.records if record["source"] == "sqlite"]
        self.assertEqual(len(sqlite), 20)
        for record in sqlite:
            self.assertEqual(record["source_dialect"], "sqlite")
            self.assertIn(record["tcl_command"], ("execsql", "do_execsql_test"))
            self.assertEqual(record["extraction"], "tcl_sql_statement")
            self.assertNotIn("expected_result", record)

    def test_all_six_relational_operators_preserve_explicit_and_implicit_forms(self):
        for operator in ("=", "<>", "<", "<=", ">", ">="):
            tree = query(compare(row(integer(), integer(2), explicit=True),
                                 row(integer(), integer(3)), operator))
            with self.subTest(operator=operator):
                self.assertEqual(observe_row_comparisons(tree), [{
                    "operator": operator, "arity": 2, "left_form": "explicit", "right_form": "implicit",
                }])

    def test_operand_order_and_multiple_comparisons_are_preserved(self):
        tree = query(compare(row(integer(), explicit=True), row(integer(), explicit=True), "<"),
                     compare(row(integer(), integer(2), integer(3)), row(integer(), integer(2), integer(4)), ">="))
        self.assertEqual(observe_row_comparisons(tree), [
            {"operator": "<", "arity": 1, "left_form": "explicit", "right_form": "explicit"},
            {"operator": ">=", "arity": 3, "left_form": "implicit", "right_form": "implicit"},
        ])

    def test_empty_and_unequal_rows_do_not_enter_positive_population(self):
        for left, right in ((row(), row()), (row(integer()), row(integer(), integer(2)))):
            with self.subTest(left=left), self.assertRaisesRegex(ValueError, "equal nonzero"):
                observe_row_comparisons(query(compare(left, right)))

    def test_standalone_nested_composite_and_row_in_forms_are_excluded(self):
        good = compare(row(integer(), integer(2)), row(integer(), integer(3)))
        bad = [
            query(row(integer(), integer(2))),
            query(compare(row(row(integer(), integer(2)), integer(3)),
                          row(row(integer(), integer(2)), integer(3)))),
            query(good, {"FuncCall": {"args": [row(integer(), integer(2))]}}),
            query(compare(row(integer(), integer(2)), row(integer(), integer(3)), kind="AEXPR_IN")),
            query(compare(row(integer(), integer(2)), row(integer(), integer(3)), kind="AEXPR_DISTINCT")),
        ]
        for tree in bad:
            with self.subTest(tree=tree), self.assertRaisesRegex(ValueError, "outside"):
                observe_row_comparisons(tree)

    def test_scalar_row_comparison_result_can_be_an_outer_field_without_becoming_composite(self):
        inner = compare(row(integer(), explicit=True), row(integer(), explicit=True))
        tree = query(compare(row(inner, integer(2)), row(integer(), integer(2))))
        self.assertEqual([entry["arity"] for entry in observe_row_comparisons(tree)], [2, 1])

    def test_custom_operator_row_vs_scalar_and_unknown_spelling_are_rejected(self):
        left, right = row(integer(), integer(2)), row(integer(), integer(3))
        for tree in (query(compare(left, right, "~=")), query(compare(left, integer()))):
            with self.subTest(tree=tree), self.assertRaisesRegex(ValueError, "outside"):
                observe_row_comparisons(tree)
        left["RowExpr"]["row_format"] = "COERCE_SQL_SYNTAX"
        with self.assertRaisesRegex(ValueError, "spelling"):
            observe_row_comparisons(query(compare(left, right)))

    def test_quantified_row_array_and_in_subqueries_are_conservatively_excluded(self):
        good = compare(row(integer(), integer(2)), row(integer(), integer(3)))
        for kind in ("ANY_SUBLINK", "ALL_SUBLINK", "ARRAY_SUBLINK", "ROWCOMPARE_SUBLINK"):
            with self.subTest(kind=kind), self.assertRaisesRegex(ValueError, "outside"):
                observe_row_comparisons(query(good, {"SubLink": {"subLinkType": kind}}))

    def test_metadata_rejects_boolean_arities_and_invented_field_types(self):
        valid = {"operator": "=", "arity": 2, "left_form": "explicit", "right_form": "implicit"}
        bad = [[], [{**valid, "arity": True}], [{**valid, "arity": 0}], [{**valid, "operator": ["="]}],
               [{**valid, "operator": "~~"}], [{**valid, "left_form": "anonymous"}],
               [{**valid, "right_form": False}], [{**valid, "field_types": ["int", "int"]}]]
        for observations in bad:
            with self.subTest(observations=observations), self.assertRaises(ValueError):
                validate_row_comparisons(observations)

    def test_population_cannot_invent_missing_operator_or_drop_form_coverage(self):
        for field, value in (("operator", "<>"), ("arity", 1), ("left_form", "explicit")):
            records = deepcopy(self.records)
            records[0]["observed_syntax"]["row_comparisons"][0][field] = value
            with self.subTest(field=field), self.assertRaisesRegex(ValueError, "72 pairs"):
                validate_population(records, "row_comparisons")

    def test_complete_statement_and_original_go_sql_hashes_are_enforced(self):
        for kind in ("tcl_sql_statement", "sql_slice"):
            manifest = deepcopy(self.manifest)
            selection = next(entry for entry in manifest["selections"] if entry["selector"]["kind"] == kind)
            selection["selector"]["end"] -= 1
            with self.subTest(kind=kind), self.assertRaisesRegex(ValueError, "complete"):
                extract(manifest, "row_comparisons")
        manifest = deepcopy(self.manifest)
        selection = next(entry for entry in manifest["selections"] if entry["source"] == "temporal")
        selection["sql_sha256"] = "0" * 64
        with self.assertRaisesRegex(ValueError, "SQL hash"):
            extract(manifest, "row_comparisons")


if __name__ == "__main__":
    unittest.main()
