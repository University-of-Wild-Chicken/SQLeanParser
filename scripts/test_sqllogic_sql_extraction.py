"""Offline tests for literal SQLLogicTest query-block extraction."""
import unittest

from extract_sqllogic_sql import query_blocks, selected_sqllogic_sql


def selection(source, index=0):
    block = query_blocks(source)[index]
    return {"kind": "sqllogic_query", **{key: block[key] for key in ("start", "end", "header_line")}}


class SqlLogicExtractionTests(unittest.TestCase):
    def test_complete_query_preserves_newline_and_optional_semicolon(self):
        source = "# file header\nquery I\nSELECT a[1] FROM t\n----\n42\n\nquery I\nSELECT a[2] FROM t;\n----\n0\n"
        first, line, detail = selected_sqllogic_sql(source, selection(source))
        self.assertEqual(first, "SELECT a[1] FROM t\n")
        self.assertEqual(line, 3)
        self.assertEqual(detail["query_header"], "query I")
        self.assertEqual(detail["extraction"], "sqllogic_query")
        self.assertNotIn("expected", detail)
        second, _, _ = selected_sqllogic_sql(source, selection(source, 1))
        self.assertEqual(second, "SELECT a[2] FROM t;\n")

    def test_multiline_utf8_crlf_source_is_not_normalized(self):
        source = "# λ\r\nquery T rowsort\r\nSELECT '雪;🦆' AS v,\r\n a[:2] FROM t;\r\n----\r\nirrelevant\r\n"
        sql, line, detail = selected_sqllogic_sql(source, selection(source))
        self.assertEqual(sql, "SELECT '雪;🦆' AS v,\r\n a[:2] FROM t;\r\n")
        self.assertEqual(line, 3)
        self.assertEqual(source[detail["start"]:detail["end"]], sql)

    def test_statement_records_and_expected_results_cannot_supply_query_headers(self):
        source = ("statement ok\nCREATE TABLE query(i INT);\n\nquery T\nSELECT 'query I'\n"
                  "----\nquery I\nSELECT malicious[1]\n----\nnot SQL\n\n"
                  "query I\nSELECT a[1] FROM t\n----\n1\n")
        blocks = query_blocks(source)
        self.assertEqual(len(blocks), 2)
        with self.assertRaisesRegex(ValueError, "complete"):
            selected_sqllogic_sql(source, {
                "kind": "sqllogic_query", "header_line": 8,
                "start": source.index("SELECT malicious"), "end": source.index("not SQL"),
            })
        sql, _, _ = selected_sqllogic_sql(source, selection(source, 1))
        self.assertEqual(sql, "SELECT a[1] FROM t\n")

    def test_fragments_and_delimiter_inclusion_are_rejected_independently_of_hash(self):
        source = "query I\nSELECT a[1] FROM t\n----\n42\n"
        original = selection(source)
        for key, delta in (("start", 1), ("end", -1), ("end", 5), ("header_line", 1)):
            with self.subTest(key=key, delta=delta), self.assertRaisesRegex(ValueError, "complete"):
                selected_sqllogic_sql(source, {**original, key: original[key] + delta})

    def test_selector_types_keys_and_kinds_are_closed(self):
        source = "query I\nSELECT a[1] FROM t\n----\n42\n"
        original = selection(source)
        bad = [{**original, "kind": "sql_slice"}, {**original, "header_line": True},
               {**original, "start": str(original["start"])}, {**original, "extra": 1}]
        missing = dict(original)
        missing.pop("end")
        for selector in bad + [missing]:
            with self.subTest(selector=selector), self.assertRaisesRegex(ValueError, "selector"):
                selected_sqllogic_sql(source, selector)

    def test_incomplete_or_empty_query_records_are_rejected(self):
        for source in ("query I\nSELECT 1\n", "query I\nSELECT 1\n\n----\n1\n",
                       "query I\n----\n1\n"):
            with self.subTest(source=source), self.assertRaises(ValueError):
                query_blocks(source)

    def test_unknown_directives_and_header_variants_are_not_interpreted(self):
        for header in ("loop i 1 5", "require duckdb", "load extension", "query X",
                       "query I label", "# comment\nSELECT 1", " query I"):
            with self.subTest(header=header), self.assertRaisesRegex(ValueError, "directive"):
                query_blocks(header + "\nSELECT 1\n----\n1\n")

    def test_multiple_statements_and_non_select_records_are_rejected(self):
        for sql in ("SELECT a[1]; SELECT a[2];", "DELETE FROM t RETURNING a[1];",
                    "SELECT a[1]; -- suffix\n SELECT a[2]"):
            source = f"query I\n{sql}\n----\n1\n"
            with self.subTest(sql=sql), self.assertRaisesRegex(ValueError, "one whole SELECT"):
                selected_sqllogic_sql(source, selection(source))

    def test_template_substitutions_are_not_treated_as_literal_source_sql(self):
        for sql in ("SELECT a[${index}] FROM t", "SELECT '$name', a[1] FROM t",
                    "SELECT '__TEST_DIR__', a[1] FROM t"):
            source = f"query I\n{sql}\n----\n1\n"
            with self.subTest(sql=sql), self.assertRaisesRegex(ValueError, "substitutions"):
                selected_sqllogic_sql(source, selection(source))

    def test_quoted_semicolons_are_allowed_and_unterminated_quotes_fail(self):
        source = "query T\nSELECT ';', a[1] /* ; */ FROM t;\n----\n1\n"
        sql, _, _ = selected_sqllogic_sql(source, selection(source))
        self.assertIn("';'", sql)
        broken = "query T\nSELECT 'unterminated\n----\n1\n"
        with self.assertRaisesRegex(ValueError, "unterminated"):
            selected_sqllogic_sql(broken, selection(broken))


if __name__ == "__main__":
    unittest.main()
