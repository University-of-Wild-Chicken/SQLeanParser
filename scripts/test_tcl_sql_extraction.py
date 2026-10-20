"""Offline tests for literal Tcl-block and complete SQL-statement extraction."""
from copy import deepcopy
import unittest

from extract_statement_corpus import statement_spans
from extract_tcl_sql import COMMAND, block_end, selected_tcl_sql


def selection(source, index=0):
    command = COMMAND.search(source)
    start = command.end()
    end = block_end(source, start - 1)
    a, b = statement_spans(source[start:end])[index]
    return {"kind": "tcl_sql_statement", "command_start": command.start(),
            "block_start": start, "block_end": end, "start": start + a,
            "end": start + b, "statement_index": index}


class TclSqlExtractionTests(unittest.TestCase):
    def test_sql_inside_nested_test_body_is_an_unchanged_whole_statement(self):
        source = """# Header
do_test joins.1 {
  execsql {
    CREATE TABLE t(a);
    SELECT 'a;b' AS text FROM t NATURAL JOIN u;
  }
} {result}
"""
        sql, line, detail = selected_tcl_sql(source, selection(source, 1))
        self.assertEqual(sql, "SELECT 'a;b' AS text FROM t NATURAL JOIN u;")
        self.assertEqual(line, 5)
        self.assertEqual(source[detail["start"]:detail["end"]], sql)
        self.assertEqual(detail["tcl_command"], "execsql")
        self.assertIsNone(detail["tcl_test_name"])
        self.assertEqual(detail["statement_index"], 1)

    def test_literal_block_preserves_dollars_quotes_braces_and_unicode(self):
        source = r'''do_execsql_test join-$id.2 {
  SELECT '{λ}', '\{literal\}', '$1', "MixedCase" FROM t JOIN u USING (a);
} {expected}
'''
        sql, _, detail = selected_tcl_sql(source, selection(source))
        self.assertEqual(sql, r"""SELECT '{λ}', '\{literal\}', '$1', "MixedCase" FROM t JOIN u USING (a);""")
        self.assertEqual(detail["tcl_test_name"], "join-$id.2")
        self.assertEqual(detail["tcl_command"], "do_execsql_test")

    def test_error_capture_origin_is_retained_without_evaluating_the_source(self):
        for command in ("do_catchsql_test join.1", "catchsql"):
            source = command + " {\n SELECT missing FROM t JOIN u USING (x);\n} {1 error}\n"
            sql, _, detail = selected_tcl_sql(source, selection(source))
            self.assertEqual(sql, "SELECT missing FROM t JOIN u USING (x);")
            self.assertEqual(detail["tcl_command"], command.split()[0])

    def test_semicolon_in_string_and_comment_cannot_split_statement(self):
        source = """execsql {
  -- ignored semicolon ;
  SELECT ';' FROM t /* ; */ JOIN u USING (x);
  SELECT 2;
}
"""
        sql, _, _ = selected_tcl_sql(source, selection(source))
        self.assertEqual(sql, "SELECT ';' FROM t /* ; */ JOIN u USING (x);")
        sql2, _, _ = selected_tcl_sql(source, selection(source, 1))
        self.assertEqual(sql2, "SELECT 2;")

    def test_fragment_mutations_and_wrong_statement_index_fail(self):
        source = "execsql {\n SELECT 1; SELECT 2;\n}\n"
        original = selection(source)
        for key, value in (("start", original["start"] + 1), ("end", original["end"] - 1),
                           ("statement_index", 1), ("statement_index", -1),
                           ("statement_index", 2)):
            selector = {**original, key: value}
            with self.subTest(key=key, value=value), self.assertRaisesRegex(ValueError, "statement"):
                selected_tcl_sql(source, selector)

    def test_complete_argument_boundaries_are_checked_independently_of_sql_hash(self):
        source = "execsql {\n SELECT 1;\n}\n"
        original = selection(source)
        for key in ("block_start", "block_end"):
            selector = {**original, key: original[key] + 1}
            with self.subTest(key=key), self.assertRaisesRegex(ValueError, "complete SQL argument"):
                selected_tcl_sql(source, selector)

    def test_wrong_types_missing_fields_and_unrecognized_selector_kind_fail(self):
        source = "execsql {\n SELECT 1;\n}\n"
        original = selection(source)
        bad = [{**original, "statement_index": True}, {**original, "start": "12"},
               {**original, "kind": "sql_slice"}, {**original, "extra": 1}]
        missing = deepcopy(original)
        missing.pop("block_end")
        bad.append(missing)
        for selector in bad:
            with self.subTest(selector=selector), self.assertRaisesRegex(ValueError, "selector"):
                selected_tcl_sql(source, selector)

    def test_comment_or_inline_text_is_not_a_supported_command_line(self):
        source = "execsql {\n SELECT 1;\n}\n"
        original = selection(source)
        for prefix in ("# ", "puts ", 'puts "'):
            altered = prefix + source
            selector = {key: (value + len(prefix) if key not in ("kind", "statement_index") else value)
                        for key, value in original.items()}
            with self.subTest(prefix=prefix), self.assertRaisesRegex(ValueError, "source line"):
                selected_tcl_sql(altered, selector)
        selector = {**original, "command_start": 1}
        with self.assertRaisesRegex(ValueError, "source line"):
            selected_tcl_sql(source, selector)

    def test_similarly_named_command_and_extra_execsql_arguments_fail(self):
        for source in ("execsql_extra {\n SELECT 1;\n}\n",
                       "execsql db {\n SELECT 1;\n}\n",
                       'do_execsql_test "quoted name" {\n SELECT 1;\n}\n'):
            if COMMAND.search(source) is None:
                continue  # Command spelling is rejected before any block can be selected.
            with self.subTest(source=source), self.assertRaises(ValueError):
                selected_tcl_sql(source, selection(source))
        self.assertIsNone(COMMAND.search("execsql_extra {\n SELECT 1;\n}\n"))
        self.assertIsNone(COMMAND.search('execsql "SELECT 1;"\n'))

    def test_backslash_newline_substitution_is_rejected_instead_of_normalized(self):
        source = "execsql {\n SELECT '\\\n changed';\n}\n"
        with self.assertRaisesRegex(ValueError, "substitution would alter"):
            selected_tcl_sql(source, selection(source))

    def test_unterminated_or_appended_brace_argument_fails(self):
        with self.assertRaisesRegex(ValueError, "unterminated"):
            block_end("{SELECT '{';", 0)
        with self.assertRaisesRegex(ValueError, "literal brace"):
            block_end("SELECT 1;", 0)
        source = "execsql {\n SELECT 1;\n}suffix\n"
        with self.assertRaisesRegex(ValueError, "non-word boundary"):
            selected_tcl_sql(source, selection(source))


if __name__ == "__main__":
    unittest.main()
