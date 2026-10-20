"""Whole keyword-call source boundaries and unchanged native-dialect evidence."""
from collections import Counter
from copy import deepcopy
import json
import unittest

from extract_application_corpus import go_tokens
from extract_factor_corpus import ROOT, extract, render, validate_population
from extract_go_query_literal import selected_go_query
from extract_pagination_corpus import comparison_key
from observe_keyword_function_source import observe_keyword_functions, validate_keyword_functions


def query(sql="SELECT left('abc', 1);", name="left", args=None):
    if args is None:
        args = [{"A_Const": {"sval": {"sval": "abc"}}},
                {"A_Const": {"ival": {"ival": 1}}}]
    return {"SelectStmt": {"targetList": [{"ResTarget": {"val": {"FuncCall": {
        "funcname": [{"String": {"sval": name}}], "args": args,
        "location": len(sql[:sql.lower().index(name)].encode()),
    }}}}]}}


def selector(source, sql):
    index, token = next((i, t) for i, t in enumerate(go_tokens(source))
                        if t.kind == "string" and json.loads(t.text) == sql)
    return {"kind": "go_string_literal", "start": token.start,
            "end": token.end, "token_index": index}


class KeywordFunctionSourceTests(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        cls.directory = ROOT / "fixtures/keyword_functions"
        cls.manifest = json.loads((cls.directory / "concrete_sources.json").read_text())
        cls.rows = extract(cls.manifest, "keyword_functions")

    def test_fifty_originals_reproduce_with_distinct_regression_and_shipping_origins(self):
        self.assertEqual(render(self.rows), (self.directory / "concrete.jsonl").read_text())
        self.assertEqual(Counter(r["source"] for r in self.rows),
                         {"doltgresql": 34, "materialize": 14, "postgres": 1, "river": 1})
        self.assertEqual(Counter(r["source_kind"] for r in self.rows),
                         {"generated-engine-regression": 34, "engine-regression": 15, "application-query": 1})
        self.assertEqual(len({comparison_key(r["sql"]).rstrip(";").strip() for r in self.rows}), 50)
        for row in self.rows:
            self.assertEqual(row["raw_sql"], row["sql"])
            self.assertEqual(row["transformations"], [])
            self.assertIsNone(row["parameter_types"])
            self.assertEqual(row["application_schema_validity"], "not-claimed")
            for key in ("parameter_values", "output_columns", "expected_value"):
                self.assertNotIn(key, row)

    def test_fixed_heads_cast_roots_nulls_and_unspecified_river_catalog_are_separate(self):
        entries = [c for r in self.rows for c in r["observed_syntax"]["keyword_functions"]]
        self.assertEqual(Counter(c["function"] for c in entries), {"left": 26, "right": 25})
        self.assertEqual(Counter(r["observed_syntax"]["source_free"] for r in self.rows),
                         {True: 49, False: 1})
        self.assertEqual(sum(sum(c["literal_nulls"]) for c in entries), 4)
        self.assertEqual(Counter(t for c in entries for t in c["explicit_casts"]),
                         {None: 76, "int4": 26})
        river = next(r for r in self.rows if r["source"] == "river")
        self.assertEqual(river["observed_parameter_slots"], [1, 2])
        self.assertIn("pg_catalog.pg_class", river["sql"])
        self.assertIn("WITH index_artifacts", river["sql"])
        self.assertFalse(river["observed_syntax"]["source_free"])

    def test_source_licensing_and_whole_go_token_identity_are_preserved(self):
        dolt = [r for r in self.rows if r["source"] == "doltgresql"]
        for row in dolt:
            self.assertEqual(row["license"], "Apache-2.0")
            self.assertEqual(row["commit"], "b905594b000601fc5ea8db38c432b21683af01fb")
            self.assertEqual(row["extraction"], "go_string_literal")
            self.assertEqual(json.loads(row["source_expression"]), row["sql"])
        self.assertTrue(all("change date 2030-10-20" in r["license"] for r in self.rows
                            if r["source"] == "materialize"))

    def test_manifest_hash_selector_license_and_source_population_mutations_fail(self):
        for change in ("license", "source", "sql", "pin", "count", "population",
                       "go_start", "go_end", "go_index", "wrong_source", "unused"):
            manifest = deepcopy(self.manifest)
            selection = next(r for r in manifest["selections"] if r["source"] == "doltgresql")
            metadata = manifest["sources"]["doltgresql"]
            if change == "license":
                metadata["license_sha256"] = "0" * 64
            elif change == "source":
                metadata["files"][0]["sha256"] = "0" * 64
            elif change == "sql":
                selection["sql_sha256"] = "0" * 64
            elif change == "pin":
                metadata["commit"] = "main"
            elif change == "count":
                manifest["selections"].pop()
            elif change == "population":
                manifest["expected_sources"]["doltgresql"] = 35
            elif change.startswith("go_"):
                key = {"go_start": "start", "go_end": "end", "go_index": "token_index"}[change]
                selection["selector"][key] += 1
            elif change == "wrong_source":
                selection["source"] = "river"
            else:
                metadata["files"].append(deepcopy(metadata["files"][0]))
            with self.subTest(change=change), self.assertRaises(ValueError):
                extract(manifest, "keyword_functions")

    def test_observation_and_binding_mutations_do_not_become_new_evidence(self):
        for change in ("function", "position", "position_bool", "null", "null_int", "form",
                       "cast", "missing", "scope", "scope_int", "extra", "bindings", "raw", "duplicate"):
            rows = deepcopy(self.rows)
            row, observation = rows[0], rows[0]["observed_syntax"]
            call = observation["keyword_functions"][0]
            if change == "function":
                call["function"] = "right"
            elif change == "position":
                call["byte_location"] += 1
            elif change == "position_bool":
                call["byte_location"] = True
            elif change == "null":
                call["literal_nulls"][0] = True
            elif change == "null_int":
                call["literal_nulls"][0] = 0
            elif change == "form":
                call["argument_forms"][1] = "ColumnRef"
            elif change == "cast":
                call["explicit_casts"][1] = None
            elif change == "missing":
                observation["keyword_functions"] = []
            elif change == "scope":
                observation["source_free"] = False
            elif change == "scope_int":
                observation["source_free"] = 1
            elif change == "extra":
                call["inferred_type"] = "text"
            elif change == "bindings":
                row["parameter_types"] = "text"
            elif change == "raw":
                row["raw_sql"] += " "
            else:
                rows[-1] = deepcopy(rows[0])
            with self.subTest(change=change), self.assertRaises(ValueError):
                validate_population(rows, "keyword_functions")


class KeywordFunctionObserverTests(unittest.TestCase):
    def test_unquoted_mixed_case_heads_and_utf8_locations_remain_distinct(self):
        sql = "SELECT LeFt('रः॑', 1);"
        result = observe_keyword_functions(query(sql), sql)
        self.assertEqual(result["keyword_functions"][0]["function"], "left")
        sql = "SELECT right('रः॑', NULL);"
        tree = query(sql, "right", [{"A_Const": {"sval": {"sval": "रः॑"}}},
                                    {"A_Const": {"isnull": True}}])
        result = observe_keyword_functions(tree, sql)
        self.assertEqual(result["keyword_functions"][0]["literal_nulls"], [False, True])

    def test_direct_cast_and_unary_over_cast_do_not_invent_the_same_root(self):
        constant = {"A_Const": {"ival": {"ival": 1}}}
        cast = {"TypeCast": {"arg": constant, "typeName": {
            "names": [{"String": {"sval": "pg_catalog"}}, {"String": {"sval": "int4"}}]}}}
        unary = {"A_Expr": {"kind": "AEXPR_OP", "name": [{"String": {"sval": "-"}}],
                            "rexpr": cast}}
        for argument, form, type_ in ((cast, "TypeCast", "int4"), (unary, "A_Expr", None)):
            sql = "SELECT left('abc', -1::int4);"
            observation = observe_keyword_functions(query(sql, args=[
                {"A_Const": {"sval": {"sval": "abc"}}}, argument]), sql)
            call = observation["keyword_functions"][0]
            self.assertEqual((call["argument_forms"][1], call["explicit_casts"][1]), (form, type_))

    def test_qualified_quoted_wrong_arity_and_later_forms_are_outside_the_population(self):
        sql = "SELECT left('abc', 1);"
        for change in ("qualified", "arity", "variadic", "window", "alias", "helper", "from_function"):
            tree = query(sql)
            target = tree["SelectStmt"]["targetList"][0]["ResTarget"]
            call = target["val"]["FuncCall"]
            if change == "qualified":
                call["funcname"].insert(0, {"String": {"sval": "pg_catalog"}})
            elif change == "arity":
                call["args"].pop()
            elif change in {"variadic", "window"}:
                call["func_variadic" if change == "variadic" else "over"] = True
            elif change == "alias":
                target["name"] = "changed"
            elif change == "helper":
                call["args"][0] = {"FuncCall": {"funcname": [{"String": {"sval": "unknown"}}]}}
            else:
                tree["SelectStmt"]["fromClause"] = [{"RangeFunction": {}}]
            with self.subTest(change=change), self.assertRaises(ValueError):
                observe_keyword_functions(tree, sql)
        observation = observe_keyword_functions(query(sql), sql)
        for spelling in ('SELECT "left"(\'abc\', 1);', "SELECT 'left'('abc', 1);", "SELECT /*left*/('abc',1);"):
            with self.subTest(spelling=spelling), self.assertRaises(ValueError):
                validate_keyword_functions(observation, spelling)

    def test_parameter_or_relation_context_is_not_mistaken_for_closed_literals(self):
        sql = "SELECT left(name, 1) FROM things;"
        tree = query(sql, args=[{"ColumnRef": {"fields": [{"String": {"sval": "name"}}]}},
                               {"A_Const": {"ival": {"ival": 1}}}])
        tree["SelectStmt"]["fromClause"] = [{"RangeVar": {"relname": "things"}}]
        self.assertFalse(observe_keyword_functions(tree, sql)["source_free"])


class GoAssertionQueryTests(unittest.TestCase):
    def test_explicit_opt_in_is_required_for_the_complete_plain_query_field(self):
        sql = "SELECT left('abc', 2);"
        source = "tests := []Assertion{{ Query: " + json.dumps(sql) + ", Expected: nil, }}"
        selected = selector(source, sql)
        with self.assertRaises(ValueError):
            selected_go_query(source, selected)
        actual, _, detail = selected_go_query(source, selected, assertion_query=True)
        self.assertEqual(actual, sql)
        self.assertEqual(json.loads(detail["source_expression"]), sql)

    def test_comments_descriptions_expected_data_and_expression_fragments_fail(self):
        sql = "SELECT right('abc', 2);"
        for source in (
            "{ Name: " + json.dumps(sql) + ", }",
            "{ Expected: " + json.dumps(sql) + ", }",
            "{ Query: " + json.dumps(sql) + " + suffix, }",
            "{ Query: prefix + " + json.dumps(sql) + ", }",
            '{"key": ' + json.dumps(sql) + ",}",
            "q.QueryRow(ctx, " + json.dumps(sql) + ")",
            "// { Query: " + json.dumps(sql) + ", }\nvar x = " + json.dumps(sql),
            "{ Query: " + json.dumps(sql) + ", } /* unterminated",
        ):
            with self.subTest(source=source), self.assertRaises(ValueError):
                selected_go_query(source, selector(source, sql), assertion_query=True)
        source = "{ Query: " + json.dumps(sql + "\n") + ", }"
        with self.assertRaises(ValueError):
            selected_go_query(source, selector(source, sql + "\n"), assertion_query=True)

    def test_multiple_statements_and_bool_offsets_cannot_expand_a_literal(self):
        sql = "SELECT left('abc', 2); SELECT 1;"
        source = "{ Query: " + json.dumps(sql) + ", }"
        with self.assertRaises(ValueError):
            selected_go_query(source, selector(source, sql), assertion_query=True)
        sql = "SELECT left('abc', 2);"
        source = "{ Query: " + json.dumps(sql) + ", }"
        selected = selector(source, sql)
        selected["start"] = True
        with self.assertRaises(ValueError):
            selected_go_query(source, selected, assertion_query=True)


if __name__ == "__main__":
    unittest.main()
