"""Offline regression tests for the pinned concrete pagination population."""
from copy import deepcopy
import json
from pathlib import Path
import tempfile
import unittest

from extract_pagination_corpus import (
    DIRECTORY, EXPECTED_SOURCES, checked_file, extract, extract_selection,
    render, sha256, sql_spans, validate_population,
)


class PaginationExtractionTests(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        cls.manifest = json.loads((DIRECTORY / "concrete_sources.json").read_text())
        cls.records = extract(cls.manifest)

    def test_frozen_population_is_exactly_reproducible(self):
        self.assertEqual(render(self.records), (DIRECTORY / "concrete.jsonl").read_text())
        self.assertEqual(len(self.records), 50)
        self.assertEqual(len({row["sql"] for row in self.records}), 50)
        self.assertEqual(sum(row["source_kind"] == "application-constant"
                             for row in self.records), 42)
        self.assertEqual(sum(row["source_kind"] == "compiler-regression"
                             for row in self.records), 8)
        self.assertEqual(self.manifest["expected_sources"], EXPECTED_SOURCES)
        for row in self.records:
            self.assertEqual(row["sql"], row["raw_sql"])
            self.assertEqual(row["transformations"], [])
            self.assertEqual(row["sql_sha256"], sha256(row["sql"].encode()))
            self.assertIn(f'/blob/{row["commit"]}/{row["source_file"]}', row["source_url"])
            self.assertTrue(row["source_url"].endswith(f'#L{row["line"]}'))

    def test_license_and_source_hash_mutation_is_rejected(self):
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            (root / "input").write_bytes(b"original")
            self.assertEqual(checked_file(root, "input", sha256(b"original")), b"original")
            (root / "input").write_bytes(b"changed")
            with self.assertRaisesRegex(ValueError, "source hash mismatch"):
                checked_file(root, "input", sha256(b"original"))
            with self.assertRaisesRegex(ValueError, "escapes repository"):
                checked_file(root, "../escape", sha256(b""))

    def test_go_constant_decoding_keeps_actual_sql_and_location(self):
        source = '// preface\nconst fields = `a, b`\nconst query = `SELECT ` + fields + ` FROM t LIMIT $1`\n'
        sql, line, detail = extract_selection(
            source, {"kind": "go_constant", "symbol": "query"})
        self.assertEqual(sql, "SELECT a, b FROM t LIMIT $1")
        self.assertEqual(line, 3)
        self.assertTrue(detail["go_constant_folding"])
        with self.assertRaisesRegex(ValueError, "missing or undecodable"):
            extract_selection(source, {"kind": "go_constant", "symbol": "missing"})

    def test_sql_slice_preserves_comments_and_quoted_semicolons(self):
        source = """-- heading
SELECT ';', "semi;name", $tag$; inside$tag$ /* outer /* ; */ inner */
FROM t LIMIT $1;
/* next */ SELECT 2 LIMIT $2;
"""
        spans = sql_spans(source)
        self.assertEqual(len(spans), 2)
        start, end = spans[0]
        sql, line, _ = extract_selection(source, {
            "kind": "sql_slice", "start": start, "end": end, "statement_index": 0,
        })
        self.assertEqual(sql, source[source.index("SELECT"):source.index("\n/* next */")])
        self.assertEqual(line, 2)
        self.assertIn("/* outer /* ; */ inner */", sql)

    def test_partial_sql_slice_and_boolean_position_are_rejected(self):
        source = "SELECT 1 LIMIT $1; SELECT 2 LIMIT $2;"
        start, end = sql_spans(source)[0]
        with self.assertRaisesRegex(ValueError, "complete statement"):
            extract_selection(source, {
                "kind": "sql_slice", "start": start, "end": end - 1, "statement_index": 0,
            })
        with self.assertRaisesRegex(ValueError, "must be integers"):
            extract_selection(source, {
                "kind": "sql_slice", "start": False, "end": end, "statement_index": 0,
            })

    def test_selected_source_mutation_cannot_regenerate_silently(self):
        manifest = deepcopy(self.manifest)
        manifest["selections"][0]["sql_sha256"] = "0" * 64
        with self.assertRaisesRegex(ValueError, "selected SQL hash mismatch"):
            extract(manifest)

    def test_missing_and_duplicate_queries_cannot_inflate_coverage(self):
        with self.assertRaisesRegex(ValueError, "exactly 50"):
            validate_population(self.records[:-1])
        records = deepcopy(self.records)
        records[1]["sql"] = records[0]["sql"]
        with self.assertRaisesRegex(ValueError, "duplicate concrete sql"):
            validate_population(records)
        records[1]["sql"] = " \n" + records[0]["sql"].upper() + " "
        with self.assertRaisesRegex(ValueError, "case/whitespace duplicate"):
            validate_population(records)

    def test_pagination_in_comments_or_data_is_not_the_factor(self):
        for sql in ("SELECT 'LIMIT $1'", "SELECT 1 /* OFFSET $1 */", "SELECT 1 LIMIT 10"):
            records = deepcopy(self.records)
            records[0]["sql"] = sql
            records[0]["raw_sql"] = sql
            with self.assertRaisesRegex(ValueError, "factor is absent"):
                validate_population(records)

    def test_dml_with_nested_pagination_is_not_a_select_fixture(self):
        records = deepcopy(self.records)
        sql = "DELETE FROM t WHERE id IN (SELECT id FROM t LIMIT $1)"
        records[0]["sql"] = records[0]["raw_sql"] = sql
        with self.assertRaisesRegex(ValueError, "whole SELECT"):
            validate_population(records)

    def test_rewritten_query_and_source_population_drift_are_rejected(self):
        records = deepcopy(self.records)
        records[0]["transformations"] = ["replace parameter with integer"]
        with self.assertRaisesRegex(ValueError, "SQL text was changed"):
            validate_population(records)
        records = deepcopy(self.records)
        records[0]["source"] = "other"
        with self.assertRaisesRegex(ValueError, "source population"):
            validate_population(records)
        manifest = deepcopy(self.manifest)
        manifest["sources"]["temporal"]["commit"] = "main"
        with self.assertRaisesRegex(ValueError, "full commit pin"):
            extract(manifest)


if __name__ == "__main__":
    unittest.main()
