"""Reject Rust fragments and transformations before selecting source SQL."""
import unittest

from extract_rust_query_sql import query_literals, selected_rust_sql

SQL = "SELECT id FROM t WHERE arr && ARRAY[1]"


def vector(body=None):
    return 'let queries: Vec<(&str, &str)> = vec![' + (
        f'("{SQL}", "description"),' if body is None else body) + '];'


def selector(source, sql=SQL):
    start = source.index('"' + sql + '"')
    return {"kind": "rust_string", "start": start, "end": start + len(sql) + 2}


class RustQueryExtractionTests(unittest.TestCase):
    def test_whole_literal_pair_preserves_bytes_and_source_line(self):
        source = '// heading\n' + vector()
        sql, line, detail = selected_rust_sql(source, selector(source))
        self.assertEqual(sql, SQL)
        self.assertEqual(line, 2)
        self.assertEqual(detail["extraction"], "rust_string")
        self.assertEqual(source[detail["source_start"]:detail["source_end"]], '"' + SQL + '"')

    def test_nested_comments_and_other_literals_cannot_supply_query_vectors(self):
        for prefix in ('// ' + vector() + '\n',
                       '/* ignored /* nested */ ' + vector() + ' */\n',
                       'let prose = r###"' + vector() + '"###;\n'):
            source = prefix + vector()
            tokens = query_literals(source)
            self.assertEqual(len(tokens), 1)
            self.assertGreaterEqual(tokens[0]["start"], len(prefix))
            with self.assertRaises(ValueError):
                selected_rust_sql(source, selector(source))

    def test_substring_offset_and_boolean_indices_fail(self):
        source = vector()
        for key, value in (("start", selector(source)["start"] + 1),
                           ("end", selector(source)["end"] - 1), ("start", True)):
            selected = selector(source)
            selected[key] = value
            with self.assertRaises(ValueError):
                selected_rust_sql(source, selected)

    def test_direct_unescaped_literals_only(self):
        for body in ('(format!("SELECT {}", id), "desc"),',
                     '(r"SELECT 1", "desc"),', '(b"SELECT 1", "desc"),',
                     '("SELECT\\n1", "desc"),', '("SELECT 1".to_owned(), "desc"),',
                     '("SELECT 1", description),'):
            with self.subTest(body=body), self.assertRaises(ValueError):
                query_literals(vector(body))

    def test_only_exact_finite_vector_declaration_is_authorized(self):
        for source in (f'let query = "{SQL}";',
                       vector().replace("queries:", "other:"),
                       vector().replace("Vec<(&str, &str)>", "Vec<&str>")):
            with self.assertRaises(ValueError):
                selected_rust_sql(source, selector(source))

    def test_description_token_cannot_be_selected_as_sql(self):
        source = vector(f'("{SQL}", "SELECT 42"),')
        with self.assertRaises(ValueError):
            selected_rust_sql(source, selector(source, "SELECT 42"))

    def test_multiple_statements_and_non_select_are_rejected(self):
        for sql in ("SELECT 1; SELECT 2;", "DELETE FROM t"):
            source = vector(f'("{sql}", "description"),')
            with self.assertRaises(ValueError):
                selected_rust_sql(source, selector(source, sql))

    def test_unterminated_syntax_and_missing_tuple_separator_fail(self):
        for source in ('/* missing', 'let ignored = r##"unterminated";',
                       vector('("SELECT 1", "d") ("SELECT 2", "d")'),
                       vector()[:-2]):
            with self.subTest(source=source), self.assertRaises(ValueError):
                query_literals(source)

    def test_sql_literal_semicolon_is_not_a_second_statement(self):
        sql = "SELECT ';' AS semicolon"
        source = vector(f'("{sql}", "description"),')
        self.assertEqual(selected_rust_sql(source, selector(source, sql))[0], sql)


if __name__ == "__main__":
    unittest.main()
