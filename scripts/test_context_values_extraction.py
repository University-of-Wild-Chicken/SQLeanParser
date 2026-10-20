"""Closed context-name provenance and lexical extraction boundaries."""
from collections import Counter
from copy import deepcopy
import json
import unittest

from extract_application_corpus import go_tokens
from extract_factor_corpus import ROOT, extract, render, validate_population
from extract_go_query_literal import selected_go_query, selected_whole_sql
from extract_pagination_corpus import comparison_key
from observe_context_value_source import observe_context_values, validate_context_values


def keyword(name="current_user", sql="SELECT current_user;"):
    return {"SQLValueFunction": {
        "op": "SVFOP_" + name.upper(), "typmod": -1,
        "location": len(sql[:sql.lower().index(name)].encode()),
    }}


def call(name="current_schema", sql="SELECT current_schema();"):
    return {"FuncCall": {"funcname": [{"String": {"sval": name}}],
                         "location": len(sql[:sql.lower().index(name)].encode())}}


def query(value, **clauses):
    return {"SelectStmt": {"targetList": [{"ResTarget": {"val": value}}], **clauses}}


def go_selector(source, sql):
    index, token = next((i, token) for i, token in enumerate(go_tokens(source))
                        if token.kind == "string" and json.loads(token.text) == sql)
    return {"kind": "go_string_literal", "start": token.start, "end": token.end,
            "token_index": index}


class ContextSourceTests(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        cls.directory = ROOT / "fixtures/context_values"
        cls.manifest = json.loads((cls.directory / "concrete_sources.json").read_text())
        cls.rows = extract(cls.manifest, "context_values")

    def test_whole_originals_reproduce_without_invented_context_or_catalog(self):
        self.assertEqual(render(self.rows), (self.directory / "concrete.jsonl").read_text())
        self.assertEqual(Counter(row["source"] for row in self.rows),
                         {"postgres": 32, "pgweb": 7, "river": 4, "materialize": 2,
                          "duckdb": 4, "risingwave": 1})
        self.assertEqual(len({comparison_key(row["sql"]).rstrip(";").strip()
                              for row in self.rows}), 50)
        for row in self.rows:
            self.assertEqual(row["sql"], row["raw_sql"])
            self.assertEqual(row["transformations"], [])
            self.assertIsNone(row["parameter_types"])
            self.assertEqual(row["application_schema_validity"], "not-claimed")
            for key in ("expected_value", "output_columns", "search_path", "parameter_values"):
                self.assertNotIn(key, row)

    def test_closed_source_forms_scopes_and_uncovered_system_user_are_explicit(self):
        entries = [entry for row in self.rows for entry in row["observed_syntax"]["context_values"]]
        self.assertEqual(len(entries), 63)
        self.assertEqual(Counter((e["name"], e["form"]) for e in entries), {
            ("current_user", "keyword"): 32, ("session_user", "keyword"): 7,
            ("current_role", "keyword"): 2, ("current_catalog", "keyword"): 2,
            ("current_schema", "keyword"): 2, ("user", "keyword"): 2,
            ("current_schema", "call"): 5, ("current_database", "call"): 11,
        })
        self.assertEqual(Counter(r["observed_syntax"]["source_free"] for r in self.rows),
                         {True: 22, False: 28})
        # Source-free syntax does not certify current_setting/privilege/inet calls.
        self.assertTrue(any(r["observed_syntax"]["source_free"]
                            and "has_table_privilege" in r["observed_syntax"]["function_names"]
                            for r in self.rows))

    def test_go_literals_and_embedded_sql_have_whole_source_selectors(self):
        selected = [r for r in self.rows if r["extraction"] == "go_string_literal"]
        self.assertEqual(Counter(r["source"] for r in selected), {"pgweb": 5, "river": 1})
        for row in selected:
            self.assertEqual(json.loads(row["source_expression"]), row["sql"])
        files = [r for r in self.rows if r["extraction"] == "whole_sql_file"]
        self.assertEqual({r["source_file"] for r in files},
                         {"pkg/statements/sql/info.sql", "pkg/statements/sql/info_simple.sql"})
        self.assertTrue(all(r["line"] == 1 for r in files))
        self.assertEqual({r["license"] for r in self.rows if r["source"] == "pgweb"}, {"MIT"})
        self.assertTrue(any("current_query" in r["sql"] for r in self.rows
                            if r["source"] == "pgweb"))

    def test_source_license_pin_selector_and_population_mutations_fail(self):
        for change in ("license", "source", "sql", "pin", "count", "origin", "go_context",
                       "go_bounds", "whole_file_kind", "unused"):
            manifest = deepcopy(self.manifest)
            if change == "license":
                manifest["sources"]["pgweb"]["license_sha256"] = "0" * 64
            elif change == "source":
                manifest["sources"]["pgweb"]["files"][0]["sha256"] = "0" * 64
            elif change == "sql":
                manifest["selections"][0]["sql_sha256"] = "0" * 64
            elif change == "pin":
                manifest["sources"]["pgweb"]["commit"] = "main"
            elif change == "count":
                manifest["selections"].pop()
            elif change == "origin":
                manifest["expected_sources"]["pgweb"] = 8
            elif change in {"go_context", "go_bounds"}:
                selected = next(r for r in manifest["selections"]
                                if r["selector"]["kind"] == "go_string_literal")
                selected["selector"]["token_index" if change == "go_context" else "end"] += 1
            elif change == "whole_file_kind":
                selected = next(r for r in manifest["selections"]
                                if r["selector"]["kind"] == "whole_sql_file")
                selected["selector"]["unexpected"] = True
            else:
                manifest["sources"]["pgweb"]["files"].append(
                    deepcopy(manifest["sources"]["pgweb"]["files"][0]))
            with self.subTest(change=change), self.assertRaises(ValueError):
                extract(manifest, "context_values")

    def test_population_rejects_forged_context_scope_position_and_binding_claims(self):
        for change in ("duplicate", "scope", "scope_bool", "form", "temporal", "position",
                       "bool_position", "types", "raw", "extra_metadata", "missing"):
            rows = deepcopy(self.rows)
            row, observation = rows[0], rows[0]["observed_syntax"]
            entry = observation["context_values"][0]
            if change == "duplicate":
                rows[-1] = rows[0]
            elif change == "scope":
                observation["source_free"] = not observation["source_free"]
            elif change == "scope_bool":
                observation["source_free"] = 0
            elif change == "form":
                entry["form"] = "keyword"
            elif change == "temporal":
                entry["name"] = "current_date"
            elif change == "position":
                entry["byte_location"] += 1
            elif change == "bool_position":
                entry["byte_location"] = True
            elif change == "types":
                row["parameter_types"] = ""
            elif change == "raw":
                row["raw_sql"] += " "
            elif change == "extra_metadata":
                entry["inferred_type"] = "name"
            else:
                observation["context_values"] = []
            with self.subTest(change=change), self.assertRaises(ValueError):
                validate_population(rows, "context_values")


class ContextObserverTests(unittest.TestCase):
    def test_bare_and_call_forms_are_not_conflated(self):
        for sql, value, name, form in (
            ("SELECT current_schema;", keyword("current_schema", "SELECT current_schema;"),
             "current_schema", "keyword"),
            ("SELECT current_schema();", call(), "current_schema", "call"),
            ("SELECT CURRENT_CATALOG;", keyword("current_catalog", "SELECT CURRENT_CATALOG;"),
             "current_catalog", "keyword"),
            ("SELECT current_database();", call("current_database", "SELECT current_database();"),
             "current_database", "call"),
        ):
            with self.subTest(sql=sql):
                self.assertEqual(observe_context_values(query(value), sql), {
                    "source_free": True, "context_values": [
                        {"name": name, "form": form, "byte_location": 7}]})

    def test_utf8_positions_case_comments_and_quoted_lookalikes(self):
        sql = "SELECT 'é', CuRrEnT_ScHeMa /* outer /* nested */ end */ ();"
        value = call("current_schema", sql)
        self.assertEqual(observe_context_values(query(value), sql)["context_values"][0]["byte_location"], 13)
        value["FuncCall"]["location"] = 9  # Inside the UTF-8 encoding of é.
        with self.assertRaisesRegex(ValueError, "UTF-8"):
            observe_context_values(query(value), sql)
        for fake in ("SELECT 'current_user';", 'SELECT "current_user";',
                     "SELECT /* current_user */ 1;", "SELECT prefixcurrent_user;",
                     "SELECT current_user_suffix;", "SELECT pg_catalog.current_user;"):
            value = keyword(sql=fake)
            with self.subTest(sql=fake), self.assertRaises(ValueError):
                observe_context_values(query(value), fake)

    def test_temporal_context_and_modified_or_qualified_calls_stay_outside_population(self):
        for name in ("current_date", "current_timestamp", "localtime"):
            sql = "SELECT " + name + ";"
            with self.subTest(name=name), self.assertRaises(ValueError):
                observe_context_values(query(keyword(name, sql)), sql)
        for field in ("args", "agg_order", "agg_filter", "over", "agg_star",
                      "agg_distinct", "agg_within_group", "func_variadic"):
            value = call()
            value["FuncCall"][field] = True
            with self.subTest(field=field), self.assertRaises(ValueError):
                observe_context_values(query(value), "SELECT current_schema();")
        value = call()
        value["FuncCall"]["funcname"].insert(0, {"String": {"sval": "pg_catalog"}})
        with self.assertRaises(ValueError):
            observe_context_values(query(value), "SELECT current_schema();")
        with self.assertRaises(ValueError):
            observe_context_values(query(keyword("current_schema", "SELECT current_schema();")),
                                   "SELECT current_schema();")

    def test_system_user_uses_postgresql_sql_syntax_function_shape(self):
        sql = "SELECT SYSTEM_USER;"
        value = {"FuncCall": {"funcname": [{"String": {"sval": "pg_catalog"}},
                                          {"String": {"sval": "system_user"}}],
                              "funcformat": "COERCE_SQL_SYNTAX", "location": 7}}
        self.assertEqual(observe_context_values(query(value), sql), {
            "source_free": True, "context_values": [
                {"name": "system_user", "form": "keyword", "byte_location": 7}]})
        with self.assertRaises(ValueError):
            observe_context_values(query(keyword("system_user", sql)), sql)
        for key in ("args", "agg_filter", "over"):
            changed = deepcopy(value)
            changed["FuncCall"][key] = True
            with self.subTest(key=key), self.assertRaises(ValueError):
                observe_context_values(query(changed), sql)

    def test_external_bindings_and_nested_catalog_reads_are_not_source_free(self):
        for dependency in ({"ColumnRef": {}}, {"ParamRef": {"number": 1}},
                           {"SubLink": {"subselect": {"SelectStmt": {"fromClause": [{"RangeVar": {}}]}}}}):
            observed = observe_context_values(query(keyword(), whereClause=dependency), "SELECT current_user;")
            self.assertIs(observed["source_free"], False)
        unknown = query(keyword(), whereClause={"FuncCall": {"funcname": [{"String": {"sval": "version"}}]}})
        self.assertIs(observe_context_values(unknown, "SELECT current_user;")["source_free"], True)

    def test_future_dependencies_empty_factors_and_duplicate_locations_fail(self):
        for dependency in ("UpdateStmt", "InsertStmt", "RangeFunction", "WindowDef",
                           "NamedArgExpr", "CollateClause"):
            with self.subTest(dependency=dependency), self.assertRaises(ValueError):
                observe_context_values(query(keyword(), extra={dependency: {}}), "SELECT current_user;")
        with self.assertRaises(ValueError):
            observe_context_values(query({"A_Const": {}}), "SELECT 1;")
        result = observe_context_values(query(keyword()), "SELECT current_user;")
        result["context_values"] *= 2
        with self.assertRaises(ValueError):
            validate_context_values(result)


class GoQueryLiteralTests(unittest.TestCase):
    SQL = "SELECT coalesce(current_schema(), '');"

    def test_map_and_ctx_query_arguments_are_exact_plain_literals(self):
        for source in ('var q = map[string]string{"default": "' + self.SQL + '",}',
                       'db.QueryRow(ctx, "' + self.SQL + '")',
                       'db.QueryRowContext(ctx, "' + self.SQL + '")'):
            selector = go_selector(source, self.SQL)
            sql, line, detail = selected_go_query(source, selector)
            self.assertEqual((sql, line), (self.SQL, 1))
            self.assertEqual(source[detail["source_start"]:detail["source_end"]],
                             json.dumps(self.SQL))

    def test_comments_raw_strings_and_matching_substrings_cannot_supply_a_query(self):
        literal = json.dumps(self.SQL)
        good = 'db.QueryRow(ctx, ' + literal + ')'
        for prefix in ("// " + good + "\n", "/* " + good + " */\n",
                       "`" + good + "`\n"):
            source = prefix + good
            selector = go_selector(source, self.SQL)
            self.assertGreaterEqual(selector["start"], len(prefix))
            self.assertEqual(selected_go_query(source, selector)[0], self.SQL)
        selector = go_selector(good, self.SQL)
        for delta in (-1, 1):
            changed = {**selector, "start": selector["start"] + delta}
            with self.assertRaises(ValueError):
                selected_go_query(good, changed)

    def test_computed_concatenated_escaped_and_unclosed_go_sources_fail(self):
        literal = json.dumps(self.SQL)
        for source in ("var q = " + literal,
                       'db.QueryRow(ctx, ' + literal + ' + suffix)',
                       'db.QueryRow(ctx, prefix + ' + literal + ')',
                       'db.QueryRow(ctx, ' + literal + ', value)',
                       'db.Exec(ctx, ' + literal + ')',
                       '/* never closed\n db.QueryRow(ctx, ' + literal + ')'):
            selector = go_selector(source, self.SQL)
            with self.subTest(source=source), self.assertRaises(ValueError):
                selected_go_query(source, selector)
        source = 'db.QueryRow(ctx, "SELECT current_schema()\\n")'
        with self.assertRaises(ValueError):
            selected_go_query(source, go_selector(source, "SELECT current_schema()\n"))

    def test_whole_file_selection_preserves_bytes_and_rejects_fragments_or_multiple_queries(self):
        sql = "SELECT\n  current_user,\n  current_database()\n"
        self.assertEqual(selected_whole_sql(sql, {"kind": "whole_sql_file"}),
                         (sql, 1, {"extraction": "whole_sql_file"}))
        for bad in ("current_user", "SELECT current_user; SELECT 1",
                    "SELECT current_schema() WHERE x = %s", "SELECT ${schema}", "\x00SELECT 1"):
            with self.subTest(sql=bad), self.assertRaises(ValueError):
                selected_whole_sql(bad, {"kind": "whole_sql_file"})
        with self.assertRaises(ValueError):
            selected_whole_sql(sql, {"kind": "whole_sql_file", "start": 0})


if __name__ == "__main__":
    unittest.main()
