"""Offline regressions for whole-statement source extraction and family gaps."""
from copy import deepcopy
import json
import unittest

from extract_statement_corpus import (
    DIRECTORY, ROOT, extract, render, selected_sql, statement_spans,
    validate_population,
)
from mine_statement_sources import candidates, select_sources


class StatementBoundaryTests(unittest.TestCase):
    def test_sql_atomic_body_is_one_outer_statement(self):
        source = """-- header
CREATE FUNCTION f(x int) RETURNS int LANGUAGE SQL
BEGIN ATOMIC
  SELECT CASE WHEN x > 0 THEN CASE x WHEN 1 THEN 2 ELSE 3 END ELSE 0 END;
  SELECT x + 1;
END;
SELECT 9;
"""
        spans = statement_spans(source)
        self.assertEqual(len(spans), 2)
        self.assertEqual(source[slice(*spans[0])],
                         source[source.index("CREATE"):source.index("\nSELECT 9;")])
        self.assertEqual(source[slice(*spans[1])], "SELECT 9;")
        records = list(candidates(source, "atomic.sql"))
        self.assertEqual(len(records), 2)
        self.assertNotEqual(records[0]["sql"], "SELECT x + 1;")

    def test_comments_quoted_atomic_and_transaction_begin_do_not_hide_boundaries(self):
        source = """BEGIN;
SELECT 'BEGIN ATOMIC; END;', "END";
SELECT E'x\\';still quoted', $body$BEGIN ATOMIC; END;$body$;
CREATE FUNCTION f() RETURNS int LANGUAGE SQL BEGIN /* comment */ ATOMIC
  SELECT 1 /* END; /* nested */ BEGIN ATOMIC; */;
END;
COMMIT;
"""
        spans = statement_spans(source)
        self.assertEqual(len(spans), 5)
        self.assertEqual(source[slice(*spans[0])], "BEGIN;")
        self.assertEqual(source[slice(*spans[-1])], "COMMIT;")
        self.assertIn("BEGIN /* comment */ ATOMIC", source[slice(*spans[3])])

    def test_unclosed_atomic_body_is_explicitly_excluded(self):
        with self.assertRaisesRegex(ValueError, "unterminated BEGIN ATOMIC"):
            statement_spans("CREATE FUNCTION f() RETURNS int LANGUAGE SQL BEGIN ATOMIC SELECT 1;")

    def test_only_complete_top_level_source_spans_can_be_selected(self):
        source = "CREATE FUNCTION f() RETURNS int LANGUAGE SQL BEGIN ATOMIC SELECT 1; END;"
        spans = statement_spans(source)
        start = source.index("SELECT")
        with self.assertRaisesRegex(ValueError, "complete statement"):
            selected_sql(source, {"kind": "sql_slice", "start": start,
                                  "end": source.index(";", start) + 1,
                                  "statement_index": 0}, spans)
        with self.assertRaisesRegex(ValueError, "must be integers"):
            selected_sql(source, {"kind": "sql_slice", "start": 0,
                                  "end": len(source), "statement_index": False}, spans)

    def test_case_outside_atomic_remains_an_ordinary_expression(self):
        source = "SELECT CASE WHEN 1=1 THEN 2 END; SELECT 3;"
        self.assertEqual([source[a:b] for a, b in statement_spans(source)],
                         ["SELECT CASE WHEN 1=1 THEN 2 END;", "SELECT 3;"])

    def test_selection_caps_each_family_without_creating_source_variants(self):
        rows = [
            {"id": f"source-{i:03}", "sql": f"SELECT {i};",
             "grammar_family": "SelectStmt", "source_kind": "engine-regression",
             "production_ids": [1, i + 2]}
            for i in range(65)
        ]
        rows += [{"id": "begin", "sql": "BEGIN;", "grammar_family": "TransactionStmtLegacy",
                  "source_kind": "engine-regression", "production_ids": [1, 99]}]
        families = ["SelectStmt", "TransactionStmtLegacy", "CreateAssertionStmt"]
        selected = select_sources(rows, families)
        self.assertEqual(len(selected), 51)
        self.assertEqual(sum(row["grammar_family"] == "SelectStmt" for row in selected), 50)
        self.assertTrue(all(any(row is original for original in rows) for row in selected))
        self.assertEqual(select_sources(list(reversed(rows)), families), selected)

    def test_selection_prefers_new_derivations_then_application_provenance(self):
        rows = [
            {"id": "engine", "sql": "SELECT 1;", "grammar_family": "SelectStmt",
             "source_kind": "engine-regression", "production_ids": [1]},
            {"id": "application", "sql": "SELECT application_value FROM table_name;",
             "grammar_family": "SelectStmt", "source_kind": "application-constant",
             "production_ids": [1]},
            {"id": "new-syntax", "sql": "SELECT 1 + 2;", "grammar_family": "SelectStmt",
             "source_kind": "engine-regression", "production_ids": [1, 2, 3]},
        ]
        selected = select_sources(rows, ["SelectStmt"])
        self.assertEqual([row["id"] for row in selected],
                         ["new-syntax", "application", "engine"])


class StatementPopulationTests(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        cls.manifest = json.loads((DIRECTORY / "concrete_sources.json").read_text())
        cls.positive, cls.negative, cls.summary = extract(cls.manifest)
        inventory = json.loads((ROOT / cls.manifest["grammar_inventory"]["path"]).read_text())
        cls.families = {row["name"]: row["entry_production"]
                        for row in inventory["statement_families"]}

    def test_all_selected_original_statements_and_gap_inventory_reproduce(self):
        self.assertEqual(render(self.positive), (DIRECTORY / "concrete.jsonl").read_text())
        self.assertEqual(render(self.negative), (DIRECTORY / "negative.jsonl").read_text())
        self.assertEqual(self.summary, json.loads((DIRECTORY / "inventory.json").read_text()))
        self.assertEqual(len(self.summary["families"]), 125)
        for family in self.summary["families"]:
            self.assertEqual(family["selected"], min(50, family["available"]))
            self.assertEqual(family["shortfall_to_fifty"], 50 - family["selected"])
        self.assertTrue(any(row["shortfall_to_fifty"] for row in self.summary["families"]))

    def test_positive_and_negative_dispositions_keep_claims_separate(self):
        self.assertTrue(all(row["expected_status"] == "grammar-accepted" for row in self.positive))
        self.assertTrue(all(row["expected_status"] == "grammar-rejected" for row in self.negative))
        for row in self.positive + self.negative:
            self.assertEqual(row["raw_sql"], row["sql"])
            self.assertEqual(row["transformations"], [])
            self.assertEqual(row["execution"], "not-performed")
            self.assertEqual(row["static_validity"], "not-claimed")
            self.assertNotIn("parameter_values", row)
            self.assertIn(row["commit"], row["source_url"])
            self.assertTrue(row["source_url"].endswith(f'#L{row["line"]}'))
        self.assertEqual(len(self.negative), 3)
        self.assertTrue(any("$1a" in row["sql"] for row in self.negative))
        self.assertTrue(any("$0_1" in row["sql"] for row in self.negative))
        self.assertTrue(any("RETURNING *" in row["sql"] for row in self.negative))

    def test_missing_records_and_duplicates_cannot_inflate_population(self):
        with self.assertRaisesRegex(ValueError, "population count"):
            validate_population(self.positive[:-1], self.negative, self.manifest, self.families)
        rows = deepcopy(self.positive)
        rows[1]["sql"] = rows[0]["sql"]
        with self.assertRaisesRegex(ValueError, "duplicate statement sql"):
            validate_population(rows, self.negative, self.manifest, self.families)

    def test_missing_family_and_fabricated_fifty_are_rejected(self):
        manifest = deepcopy(self.manifest)
        del manifest["family_population"][next(iter(self.families))]
        with self.assertRaisesRegex(ValueError, "every pinned grammar family"):
            validate_population(self.positive, self.negative, manifest, self.families)
        manifest = deepcopy(self.manifest)
        family = next(name for name, row in manifest["family_population"].items()
                      if row["selected"] < 50)
        manifest["family_population"][family]["selected"] = 50
        with self.assertRaisesRegex(ValueError, "inconsistent source population"):
            validate_population(self.positive, self.negative, manifest, self.families)

    def test_changed_family_production_and_invented_semantic_claims_fail(self):
        for field, value, message in (
            ("entry_production", -1, "entry production"),
            ("static_validity", "proved", "must not claim"),
            ("execution", "passed", "must not claim"),
            ("parameter_types", "integer", "must not be invented"),
            ("transformations", ["renamed test table"], "text was changed"),
        ):
            rows = deepcopy(self.positive)
            rows[0][field] = value
            with self.subTest(field=field), self.assertRaisesRegex(ValueError, message):
                validate_population(rows, self.negative, self.manifest, self.families)

    def test_source_selected_text_and_grammar_inputs_are_hash_bound(self):
        for target in ("source", "selection", "grammar"):
            manifest = deepcopy(self.manifest)
            if target == "source":
                next(iter(manifest["sources"].values()))["files"][0]["sha256"] = "0" * 64
            elif target == "selection":
                manifest["selections"][0]["sql_sha256"] = "0" * 64
            else:
                manifest["grammar_inventory"]["sha256"] = "0" * 64
            with self.subTest(target=target), self.assertRaises(ValueError):
                extract(manifest)


if __name__ == "__main__":
    unittest.main()
