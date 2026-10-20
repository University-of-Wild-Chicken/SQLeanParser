"""Unchanged source boundaries, finite SLT prefixes, and SUBSTRING syntax evidence."""
from collections import Counter
from copy import deepcopy
import json
import unittest

from extract_cockroach_sqllogic_sql import selected_cockroach_sql
from extract_factor_corpus import ROOT, extract, render, validate_population
from extract_sqllogic_sql import query_blocks
from observe_substring_source import observe_substrings, validate_substrings


def selection(source, sql):
    start = source.index(sql)
    return {"kind": "cockroach_sqllogic_query", "start": start, "end": start + len(sql),
            "header_line": source.count("\n", 0, start)}


def tree(args=None, *, ordinary=False, location=7):
    return {"SelectStmt": {"op": "SETOP_NONE", "limitOption": "LIMIT_OPTION_DEFAULT",
        "targetList": [{"ResTarget": {"val": {"FuncCall": {
            "funcname": [{"String": {"sval": x}} for x in
                         (["substring"] if ordinary else ["pg_catalog", "substring"])],
            "funcformat": "COERCE_EXPLICIT_CALL" if ordinary else "COERCE_SQL_SYNTAX",
            "location": location, "args": args if args is not None else [
                {"A_Const": {"sval": {"sval": "abcdef"}}}, {"A_Const": {"ival": {"ival": 2}}}],
        }}}}]}}


def call(value):
    return value["SelectStmt"]["targetList"][0]["ResTarget"]["val"]["FuncCall"]


class CockroachLiteralReaderTests(unittest.TestCase):
    def test_prefix_keeps_crlf_sql_and_ignores_expected_values(self):
        sql = "SELECT substring('a' FROM 1);\r\n"
        source = "# test\r\nmode cockroach\r\n\r\nquery T\r\n" + sql + "----\r\nopaque result\r\n"
        actual, line, detail = selected_cockroach_sql(source, selection(source, sql))
        self.assertEqual(actual, sql)
        self.assertEqual(line, 5)
        self.assertEqual(detail["query_header"], "query T")
        self.assertNotIn("opaque", actual)

    def test_prior_error_records_and_column_headers_are_only_skipped(self):
        sql = "SELECT substring('abc' FOR 2)\n"
        source = ("statement error expected\nSELECT bad;\n\n"
                  "query error unknown function\nSELECT not_a_function();\n\n"
                  "query TT colnames,rowsort\nSELECT 'a','b'\n----\na b\nvalue value\n\n"
                  "query T\n" + sql + "----\nnot an oracle\n")
        self.assertEqual(selected_cockroach_sql(source, selection(source, sql))[0], sql)

    def test_header_text_inside_prior_result_or_statement_is_not_selected(self):
        for prefix in ("query T\nSELECT 'opaque'\n----\n", "statement ok\n"):
            sql = "SELECT substring('abc' FROM 1)\n"
            source = prefix + "query T\n" + sql + "----\nvalue\n"
            with self.assertRaises(ValueError):
                selected_cockroach_sql(source, selection(source, sql))

    def test_unknown_prefix_directive_fails_but_later_program_is_not_interpreted(self):
        sql = "SELECT substring('abc' FROM 1)\n"
        block = "query T\n" + sql + "----\na\n"
        for directive in ("foreach V 1 2", "user root", "include other.slt", "mode duckdb"):
            source = directive + "\n\n" + block
            with self.subTest(directive=directive), self.assertRaises(ValueError):
                selected_cockroach_sql(source, selection(source, sql))
        source = block + "\nforeach LATER a b\n"
        self.assertEqual(selected_cockroach_sql(source, selection(source, sql))[0], sql)

    def test_partial_empty_multi_statement_and_substitution_queries_fail(self):
        for sql in ("SELECT 1; SELECT substring('abc' FROM 1)\n",
                    "SELECT substring('${value}' FROM 1)\n",
                    "SELECT substring('{VALUE}' FROM 1)\n",
                    "DELETE FROM x\n", ""):
            source = "query T\n" + sql + "----\nx\n"
            selector = {"kind": "cockroach_sqllogic_query", "start": 8,
                        "end": 8 + len(sql), "header_line": 1}
            with self.subTest(sql=sql), self.assertRaises(ValueError):
                selected_cockroach_sql(source, selector)
        sql = "SELECT substring('abc' FROM 1)\n"
        source = "query T\n" + sql + "----\nx\n"
        for key, value in (("start", 9), ("end", 12), ("header_line", True), ("kind", "sqllogic_query")):
            selector = selection(source, sql)
            selector[key] = value
            with self.subTest(key=key), self.assertRaises(ValueError):
                selected_cockroach_sql(source, selector)

    def test_query_errors_non_text_headers_and_unterminated_queries_cannot_be_selected(self):
        sql = "SELECT substring('abc' FROM 1)\n"
        for header in ("query error expected", "query I", "query T colnames"):
            source = header + "\n" + sql + "----\nx\n"
            with self.subTest(header=header), self.assertRaises(ValueError):
                selected_cockroach_sql(source, selection(source, sql))
        for suffix in ("", "\n----\nx\n"):
            source = "query T\n" + sql + suffix
            with self.assertRaises(ValueError):
                selected_cockroach_sql(source, selection(source, sql))

    def test_original_plain_reader_still_rejects_extended_dialect_headers(self):
        for source in ("mode cockroach\n\nquery T\nSELECT 1\n----\n1\n",
                       "query error unknown function\nSELECT bad()\n\n"):
            with self.assertRaises(ValueError):
                query_blocks(source)


class SubstringExtractionTests(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        cls.directory = ROOT / "fixtures/substring"
        cls.manifest = json.loads((cls.directory / "concrete_sources.json").read_text())
        cls.rows = extract(cls.manifest, "substring")

    def test_fifty_whole_originals_reproduce_with_no_catalog_values_or_rewrites(self):
        self.assertEqual(render(self.rows), (self.directory / "concrete.jsonl").read_text())
        self.assertEqual(Counter(row["source"] for row in self.rows),
                         {"postgres": 27, "cockroach": 11, "materialize": 12})
        for row in self.rows:
            self.assertEqual(row["raw_sql"], row["sql"])
            self.assertEqual(row["transformations"], [])
            self.assertIsNone(row["parameter_types"])
            self.assertEqual(row["observed_parameter_slots"], [])
            self.assertIs(row["observed_syntax"]["source_free"], True)
            for field in ("expected_value", "output_columns", "parameter_values"):
                self.assertNotIn(field, row)

    def test_six_forms_six_bytea_casts_and_seven_boolean_wrappers_are_preserved(self):
        entries = [row["observed_syntax"]["substrings"][0] for row in self.rows]
        self.assertEqual(Counter(entry["form"] for entry in entries), {
            "from-for": 14, "from": 13, "similar-escape": 12, "ordinary": 7, "for": 3, "for-from": 1})
        self.assertEqual(Counter(entry["arguments"][0]["cast"] for entry in entries), {None: 44, "bytea": 6})
        self.assertEqual(Counter(entry["wrapper"] for entry in entries),
                         {"plain": 43, "is-null": 5, "equality": 2})

    def test_syntax_observation_does_not_evaluate_patterns_or_nulls(self):
        value = tree([{"A_Const": {"isnull": True}},
                      {"A_Const": {"sval": {"sval": "invalid regex ["}}}])
        observed = observe_substrings(value, "SELECT substring(NULL FROM 'invalid regex [')")
        self.assertEqual(observed["substrings"][0]["arguments"], [
            {"form": "null", "value": None, "cast": None},
            {"form": "string", "value": "invalid regex [", "cast": None}])

    def test_source_keyword_order_is_distinct_even_when_raw_arguments_match(self):
        args = [*call(tree())["args"], {"A_Const": {"ival": {"ival": 3}}}]
        a = observe_substrings(tree(args), "SELECT substring('abcdef' FROM 2 FOR 3)")
        b = observe_substrings(tree(args), "SELECT substring('abcdef' FOR 3 FROM 2)")
        self.assertEqual(a["substrings"][0]["arguments"], b["substrings"][0]["arguments"])
        self.assertEqual((a["substrings"][0]["form"], b["substrings"][0]["form"]), ("from-for", "for-from"))

    def test_quotes_comments_and_utf8_source_locations_do_not_create_fake_keywords(self):
        sql = "/* λ */ SELECT substring('FROM FOR SIMILAR ESCAPE' /* FOR */ FROM 2)"
        location = len(sql[:sql.index("substring")].encode())
        self.assertEqual(observe_substrings(tree(location=location), sql)["substrings"][0]["form"], "from")
        with self.assertRaises(ValueError):
            observe_substrings(tree(location=4), sql)  # Inside the UTF-8 lambda encoding.

    def test_for_only_requires_the_raw_parsers_default_one_and_integer_cast(self):
        args = [call(tree())["args"][0], {"A_Const": {"ival": {"ival": 1}}},
                {"TypeCast": {"location": -1, "arg": {"A_Const": {"ival": {}}},
                              "typeName": {"names": [{"String": {"sval": "pg_catalog"}},
                                                     {"String": {"sval": "int4"}}]}}}]
        observed = observe_substrings(tree(args), "SELECT substring('abcdef' FOR 0)")
        self.assertEqual(observed["substrings"][0]["arguments"][2],
                         {"form": "integer", "value": 0, "cast": "pg_catalog.int4"})
        for mutation in ("start", "cast", "location"):
            bad = deepcopy(args)
            if mutation == "start":
                bad[1]["A_Const"]["ival"]["ival"] = 2
            elif mutation == "cast":
                bad[2]["TypeCast"]["typeName"]["names"][-1]["String"]["sval"] = "int8"
            else:
                bad[2]["TypeCast"]["location"] = 15
            with self.subTest(mutation=mutation), self.assertRaises(ValueError):
                observe_substrings(tree(bad), "SELECT substring('abcdef' FOR 0)")

    def test_catalog_parameters_nested_calls_queries_and_query_modifiers_are_excluded(self):
        for mutation in ("column", "parameter", "function", "subquery", "table", "order", "projection", "set"):
            bad = tree()
            if mutation in {"column", "parameter", "function", "subquery"}:
                kind = {"column": "ColumnRef", "parameter": "ParamRef",
                        "function": "FuncCall", "subquery": "SubLink"}[mutation]
                call(bad)["args"][0] = {kind: {}}
            elif mutation == "projection":
                bad["SelectStmt"]["targetList"] *= 2
            elif mutation == "set":
                bad["SelectStmt"]["op"] = "SETOP_UNION"
            else:
                bad["SelectStmt"][{"table": "fromClause", "order": "sortClause"}[mutation]] = []
            with self.subTest(mutation=mutation), self.assertRaises(ValueError):
                observe_substrings(bad, "SELECT substring('abcdef' FROM 2)")

    def test_wrong_function_identity_flags_and_spelling_fail_closed(self):
        for mutation in ("qualified", "aggregate", "format", "wrong_location", "no_substring"):
            bad = tree()
            sql = "SELECT substring('abcdef' FROM 2)"
            if mutation == "qualified":
                call(bad)["funcname"][0]["String"]["sval"] = "other"
            elif mutation == "aggregate":
                call(bad)["agg_distinct"] = True
            elif mutation == "format":
                call(bad)["funcformat"] = "COERCE_EXPLICIT_CALL"
            elif mutation == "wrong_location":
                call(bad)["location"] = -1
            else:
                sql = "SELECT othercall('abcdef' FROM 2)"
            with self.subTest(mutation=mutation), self.assertRaises(ValueError):
                observe_substrings(bad, sql)

    def test_plain_bytea_cast_is_recorded_but_array_and_other_types_are_excluded(self):
        for name in ("bytea", "bit", "citext", "custom"):
            bad = tree()
            call(bad)["args"][0] = {"TypeCast": {"arg": call(tree())["args"][0],
                "typeName": {"names": [{"String": {"sval": name}}]}}}
            sql = "SELECT substring('abcdef'::" + name + " FROM 2)"
            if name == "bytea":
                self.assertEqual(observe_substrings(bad, sql)["substrings"][0]["arguments"][0]["cast"], "bytea")
                call(bad)["args"][0]["TypeCast"]["typeName"]["arrayBounds"] = [{"Integer": {"ival": -1}}]
            with self.subTest(name=name), self.assertRaises(ValueError):
                observe_substrings(bad, sql)

    def test_population_rejects_form_cast_wrapper_scope_and_duplicate_mutations(self):
        for mutation in ("form", "cast", "wrapper", "scope", "duplicate"):
            rows = deepcopy(self.rows)
            entry = rows[0]["observed_syntax"]["substrings"][0]
            if mutation == "form":
                entry["form"] = "ordinary"
            elif mutation == "cast":
                entry["arguments"][0]["cast"] = "bytea"
            elif mutation == "wrapper":
                entry["wrapper"] = "plain"
            elif mutation == "scope":
                rows[0]["observed_syntax"]["source_free"] = 1
            else:
                rows[1] = deepcopy(rows[0])
            with self.subTest(mutation=mutation), self.assertRaises(ValueError):
                validate_population(rows, "substring")
        entry = deepcopy(self.rows[0]["observed_syntax"]["substrings"])
        entry[0]["arguments"][1]["value"] = True
        with self.assertRaises(ValueError):
            validate_substrings(entry)

    def test_source_hashes_selectors_and_all_license_notices_are_enforced(self):
        for mutation in ("sql_hash", "selector", "source_hash", "license_hash", "notice"):
            manifest = deepcopy(self.manifest)
            cr = manifest["sources"]["cockroach"]
            if mutation == "sql_hash":
                manifest["selections"][-1]["sql_sha256"] = "0" * 64
            elif mutation == "selector":
                manifest["selections"][-1]["selector"]["end"] -= 1
            elif mutation == "source_hash":
                cr["files"][0]["sha256"] = "0" * 64
            elif mutation == "license_hash":
                cr["license_sha256"] = "0" * 64
            else:
                cr["additional_notices"][0]["sha256"] = "0" * 64
            with self.subTest(mutation=mutation), self.assertRaises(ValueError):
                extract(manifest, "substring")


if __name__ == "__main__":
    unittest.main()
