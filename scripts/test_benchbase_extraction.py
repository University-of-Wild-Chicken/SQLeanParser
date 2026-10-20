#!/usr/bin/env python3
"""Offline regression tests for the pinned, non-executing BenchBase extractor."""

import json
from pathlib import Path
import shutil
import tempfile
import unittest
from unittest.mock import patch

from extract_benchbase_corpus import (
    ExtractionError, LiteralEvaluator, OUTPUT, extract, input_paths,
    java_string, java_tokens, normalize_sql, number_parameters, read_constants,
    read_overrides, sha256, verify_snapshot, verify_source_inputs,
)


class BenchBaseExtractionTests(unittest.TestCase):
    def evaluate(self, expression, constants=None):
        return LiteralEvaluator(java_tokens(expression), constants or {}).evaluate()

    def test_concatenation_preserves_sql_literal_contents(self):
        self.assertEqual(self.evaluate('"SELECT \\"a\\", \'two  spaces\' " + "FROM t"'),
                         'SELECT "a", \'two  spaces\' FROM t')

    def test_java_escapes_and_text_block_indentation(self):
        self.assertEqual(java_string('"a\\tb\\n\\141\\\\c"'), "a\tb\na\\c")
        self.assertEqual(java_string('"""\n    SELECT \'a  b\',\\s\n      1\n    """'),
                         "SELECT 'a  b', \n  1\n")

    def test_text_block_line_continuation(self):
        self.assertEqual(java_string('"""\n  SELECT \\\n  1\n  """'), "SELECT 1\n")

    def test_formatted_static_identifier_substitution(self):
        constants = {"Tables.NAME": {"value": "orders"}}
        self.assertEqual(self.evaluate('"SELECT * FROM %s WHERE tag LIKE \'%%x%%\'".formatted(Tables.NAME)',
                                       constants),
                         "SELECT * FROM orders WHERE tag LIKE '%x%'")

    def test_unknown_or_executable_java_is_rejected(self):
        for expression in ('System.getenv("SQL")', '"SELECT " + runtimeName',
                           '"SELECT %d".formatted(2)', '"SELECT %s".formatted()'):
            with self.subTest(expression=expression), self.assertRaises(ExtractionError):
                self.evaluate(expression)

    def test_java_comments_and_string_content_are_not_constructors(self):
        tokens = java_tokens('/* new SQLStmt("SELECT 0") */\n'
                             'String s = "new SQLStmt(x)"; // new SQLStmt(x)\n'
                             'SQLStmt q = new SQLStmt("SELECT 1");')
        constructors = sum([t.text for t in tokens[i:i + 3]] == ["new", "SQLStmt", "("]
                           for i in range(len(tokens) - 2))
        self.assertEqual(constructors, 1)

    def test_unsupported_unicode_preprocessing_fails_closed(self):
        with self.assertRaises(ExtractionError):
            java_tokens(r'SQLStmt q = new SQLStmt("\u0022");')

    def test_constants_keep_mutable_default_provenance(self):
        result = read_constants(
            'public static final String TABLE = "accounts";\n'
            'public static int LIMIT = 20;\n'
            'public static int DYNAMIC = calculate();',
            "test/Defaults.java")
        self.assertEqual(result["Defaults.TABLE"]["value"], "accounts")
        self.assertTrue(result["Defaults.TABLE"]["final"])
        self.assertFalse(result["Defaults.LIMIT"]["final"])
        self.assertEqual(result["Defaults.LIMIT"]["source_line"], 2)
        self.assertNotIn("Defaults.DYNAMIC", result)

    def test_xml_entities_dialect_selection_and_source_lines(self):
        result = read_overrides(
            '<dialects>\n<dialect type="POSTGRES"><procedure name="Q">\n'
            '<statement name="q">SELECT 1 WHERE ? &lt;&gt; 2</statement>\n'
            '</procedure></dialect>'
            '<dialect type="SQLITE"><procedure name="Q">'
            '<statement name="q">SELECT 3</statement></procedure></dialect></dialects>',
            "dialect.xml")
        self.assertEqual(result[("Q", "q")]["sql"], "SELECT 1 WHERE ? <> 2")
        self.assertEqual(result[("Q", "q")]["source_line"], 3)

    def test_xml_entities_cannot_read_external_files(self):
        with self.assertRaises(ExtractionError):
            read_overrides('<!DOCTYPE x [<!ENTITY x SYSTEM "file:///etc/passwd">]><x/>',
                           "dialect.xml")

    def test_jdbc_numbering_preserves_quoted_and_commented_question_marks(self):
        sql = """SELECT ?, '?', "?", 'it''s ?',
E'escaped\\'?', $$?$$, $body$?$body$, ? -- ?
/* ? /* nested ? */ ? */ , ?"""
        expected = """SELECT $1, '?', "?", 'it''s ?',
E'escaped\\'?', $$?$$, $body$?$body$, $2 -- ?
/* ? /* nested ? */ ? */ , $3"""
        self.assertEqual(number_parameters(sql), (expected, 3))

    def test_parameter_scanner_rejects_ambiguous_or_unterminated_inputs(self):
        for sql in ("SELECT ??", "SELECT $1, ?", "SELECT '?", "SELECT $x$?",
                    "SELECT /* ?", 'SELECT "column'):
            with self.subTest(sql=sql), self.assertRaises(ExtractionError):
                number_parameters(sql)

    def test_sqlstmt_list_expansion_precedes_jdbc_numbering(self):
        sql, count, transformations = normalize_sql(
            " SELECT * FROM t WHERE id IN (??) AND name = ? ", [3])
        self.assertEqual(sql, "SELECT * FROM t WHERE id IN ($1, $2, $3) AND name = $4")
        self.assertEqual(count, 4)
        self.assertEqual(transformations, [
            "sqlstmt_double_question_expansion", "trim_outer_whitespace",
            "jdbc_to_postgresql_parameters"])

    def test_dynamic_constructor_and_orphan_override_are_catalogued(self):
        with tempfile.TemporaryDirectory() as temporary:
            root = Path(temporary)
            for path, role in input_paths().items():
                destination = root / path
                destination.parent.mkdir(parents=True, exist_ok=True)
                destination.write_text("<dialects/>" if role == "postgres_override" else "")
            procedure = root / "src/main/java/com/oltpbenchmark/benchmarks/ycsb/procedures/ReadRecord.java"
            procedure.write_text('public final SQLStmt readStmt = new SQLStmt(runtimeSql());')
            dialect = root / "src/main/resources/benchmarks/twitter/dialect-postgres.xml"
            dialect.write_text('<dialects><dialect type="POSTGRES"><procedure name="Ghost">'
                               '<statement name="q">SELECT 1</statement>'
                               '</procedure></dialect></dialects>')
            records, metadata = extract(root)
        self.assertEqual(records, [])
        self.assertEqual(metadata["extraction"]["constructor_count"], 1)
        skipped = metadata["extraction"]["skipped_inputs"]
        self.assertEqual(len(skipped), 2)
        self.assertEqual(skipped[0]["id"], "benchbase:twitter:Ghost:q:unapplied_override")
        self.assertEqual(skipped[1]["id"], "benchbase:ycsb:ReadRecord:readStmt")
        self.assertIn("runtimeSql", skipped[1]["reason"])

    def test_committed_corpus_is_complete_for_the_selected_families(self):
        metadata = verify_snapshot(OUTPUT)
        self.assertEqual(metadata["record_count"], 104)
        self.assertEqual(metadata["extraction"]["constructor_count"], 104)
        self.assertEqual(metadata["extraction"]["skipped_inputs"], [])
        self.assertEqual(metadata["extraction"]["postgres_overrides_applied"], 18)
        self.assertEqual(metadata["extraction"]["constructors_by_workload"],
                         {"smallbank": 21, "tatp": 12, "tpcc": 33, "tpch": 24,
                          "twitter": 7, "ycsb": 7})

    def test_upstream_duplicates_are_retained_with_distinct_procedure_ids(self):
        records = [json.loads(line) for line in (OUTPUT / "benchbase.jsonl").read_text().splitlines()]
        self.assertEqual(len({record["sql"] for record in records}), 88)
        q15 = [r for r in records if r["source"] == "benchbase:tpch" and r["procedure"] == "Q15"]
        self.assertEqual({r["statement"] for r in q15},
                         {"createview_stmt", "query_stmt", "dropview_stmt"})
        self.assertTrue(all(r["caveats"] for r in q15))
        twitter_lists = [r for r in records if r["sqlstmt_substitutions"]]
        self.assertEqual(len(twitter_lists), 2)
        self.assertTrue(all(r["parameter_count"] == 20 for r in twitter_lists))

    def test_offline_check_detects_changed_sql_even_with_rehashed_manifest(self):
        with tempfile.TemporaryDirectory() as temporary:
            output = Path(temporary)
            for name in ("benchbase.jsonl", "benchbase_sources.json", "licenses"):
                original = OUTPUT / name
                if original.is_dir():
                    shutil.copytree(original, output / name)
                else:
                    shutil.copy2(original, output / name)
            path = output / "benchbase.jsonl"
            records = [json.loads(line) for line in path.read_text().splitlines()]
            records[0]["sql"] += " AND 1 = 0"
            path.write_text("".join(json.dumps(record) + "\n" for record in records))
            manifest = output / "benchbase_sources.json"
            metadata = json.loads(manifest.read_text())
            metadata["corpus_sha256"] = sha256(path.read_bytes())
            manifest.write_text(json.dumps(metadata))
            with self.assertRaisesRegex(ExtractionError, "normalization mismatch"):
                verify_snapshot(output)

    def test_re_extraction_refuses_to_relabel_edited_sources_as_upstream(self):
        with tempfile.TemporaryDirectory() as temporary:
            root = Path(temporary)
            source = root / "Query.java"
            source.write_bytes(b'new SQLStmt("SELECT 1")')
            verified_manifest = {"inputs": [
                {"path": "Query.java", "sha256": sha256(source.read_bytes())}]}
            with patch("extract_benchbase_corpus.verify_snapshot", return_value=verified_manifest):
                verify_source_inputs(root)
                source.write_bytes(b'new SQLStmt("SELECT 2")')
                with self.assertRaisesRegex(ExtractionError, "differs from pinned upstream"):
                    verify_source_inputs(root)


if __name__ == "__main__":
    unittest.main()
