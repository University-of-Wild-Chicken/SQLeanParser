"""Closed unchanged named-call corpus, source-order and interface evidence tests."""
from collections import Counter
from copy import deepcopy
import json
import unittest

from extract_factor_corpus import ROOT, extract, render, validate_population
from extract_pagination_corpus import comparison_key
from observe_named_argument_source import (
    INTERFACE_CASES, INTERFACE_PATH, interface_evidence, observe_named_arguments,
    validate_named_arguments,
)


def parsed(sql, function="f", names=("a", "b"), positional=0):
    """Tiny raw-AST fixture builder; no parser dependency in offline tests."""
    arguments = [{"A_Const": {"ival": {"ival": i + 1}}} for i in range(positional)]
    for name in names:
        location = sql.index(name, sql.index("(") + 1)
        arguments.append({"NamedArgExpr": {"name": name, "location": len(sql[:location].encode()),
                                           "arg": {"A_Const": {"ival": {"ival": 1}}}}})
    call = {"FuncCall": {"funcname": [{"String": {"sval": function}}],
                         "location": len(sql[:sql.index(function)].encode()),
                         "args": arguments}}
    return {"SelectStmt": {"targetList": [{"ResTarget": {"val": call}}]}}


class NamedArgumentSourceTests(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        cls.directory = ROOT / "fixtures/named_arguments"
        cls.manifest = json.loads((cls.directory / "concrete_sources.json").read_text())
        cls.rows = extract(cls.manifest, "named_arguments")
        context = cls.manifest["sources"]["sqlc"]["context_files"][0]
        cls.interface = (ROOT / context["local_path"]).read_text()

    def test_unchanged_whole_queries_reproduce_with_pinned_source_origins(self):
        self.assertEqual(render(self.rows), (self.directory / "concrete.jsonl").read_text())
        self.assertEqual(Counter(row["source"] for row in self.rows), {"postgres": 42, "sqlc": 8})
        self.assertEqual(len({comparison_key(row["sql"]).rstrip(";").strip()
                              for row in self.rows}), 50)
        for row in self.rows:
            self.assertEqual(row["sql"], row["raw_sql"])
            self.assertEqual(row["transformations"], [])
            self.assertEqual(row["application_schema_validity"], "not-claimed")
            self.assertEqual(row["source_kind"],
                             "engine-regression" if row["source"] == "postgres"
                             else "compiler-regression")
            self.assertNotIn("parameter_values", row)
            self.assertNotIn("expected_value", row)

    def test_fixed_notation_order_and_routine_inventory(self):
        calls = [call for row in self.rows for call in row["observed_syntax"]["named_calls"]]
        self.assertEqual(len(calls), 50)
        self.assertEqual(Counter(a["notation"] for c in calls for a in c["named_arguments"]),
                         {":=": 36, "=>": 51})
        self.assertEqual(sum(None in c["argument_names"] for c in calls), 20)
        self.assertEqual(Counter(row["observed_syntax"]["source_free"] for row in self.rows),
                         {True: 46, False: 4})
        self.assertEqual(Counter(c["function"] for c in calls), {
            "dfunc": 22, "make_interval": 7, "concat_lower_or_upper": 4,
            "jsonb_path_match": 4, "jsonb_set_lax": 3, "jsonb_path_query_first": 3,
            "jsonb_path_query_array": 2, "jsonb_path_exists": 2, "plus": 1,
            "table_args": 1, "parse_ident": 1})
        plus = next(r for r in self.rows if r["sql"] == "SELECT plus(b => $2, a => $1);")
        self.assertEqual(plus["observed_syntax"]["named_calls"][0]["argument_names"], ["b", "a"])
        self.assertEqual(plus["observed_parameter_slots"], [2, 1])
        self.assertTrue(any("=>/**/" in r["sql"] for r in self.rows))
        self.assertTrue(any("=>--comment" in r["sql"] for r in self.rows))

    def test_only_two_real_generated_interfaces_declare_inputs(self):
        declared = {row["id"]: row for row in self.rows if row["parameter_types"] is not None}
        self.assertEqual(set(declared), set(INTERFACE_CASES))
        for case_id, row in declared.items():
            expected = INTERFACE_CASES[case_id]
            evidence = row["parameter_type_provenance"]
            self.assertEqual((row["parameter_types"], evidence["go_type"]),
                             (expected[4], expected[3]))
            self.assertEqual(evidence["source_file"], INTERFACE_PATH)
            self.assertEqual(evidence["method"], expected[0])
            self.assertIn("sqlc-dev/sqlc/blob/0f1602fe1a4b780336e3e878dde720892fd8578d/",
                          evidence["source_url"])
        self.assertEqual(sum("parameter_type_provenance" in row for row in self.rows), 2)
        # The source-free flag is structural; forty-one source-free unknown helpers
        # still require independently supplied routine signatures.
        self.assertEqual(sum(r["observed_syntax"]["source_free"]
                             and r["observed_syntax"]["named_calls"][0]["function"] != "make_interval"
                             for r in self.rows), 41)

    def test_pin_license_sql_span_and_interface_hash_mutations_fail(self):
        for mutation in ("license", "source", "sql", "pin", "count", "selector",
                         "interface_hash", "interface_missing", "interface_duplicate", "population"):
            manifest = deepcopy(self.manifest)
            if mutation == "license":
                manifest["sources"]["sqlc"]["license_sha256"] = "0" * 64
            elif mutation == "source":
                manifest["sources"]["postgres"]["files"][0]["sha256"] = "0" * 64
            elif mutation == "sql":
                manifest["selections"][0]["sql_sha256"] = "0" * 64
            elif mutation == "pin":
                manifest["sources"]["postgres"]["commit"] = "main"
            elif mutation == "count":
                manifest["selections"].pop()
            elif mutation == "selector":
                manifest["selections"][0]["selector"]["start"] += 1
            elif mutation == "interface_hash":
                manifest["sources"]["sqlc"]["context_files"][0]["sha256"] = "0" * 64
            elif mutation == "interface_missing":
                manifest["sources"]["sqlc"]["context_files"] = []
            elif mutation == "interface_duplicate":
                manifest["sources"]["sqlc"]["context_files"] *= 2
            else:
                manifest["expected_sources"]["sqlc"] = 9
            with self.subTest(mutation=mutation), self.assertRaises(ValueError):
                extract(manifest, "named_arguments")

    def test_argument_metadata_scope_and_undeclared_binding_mutations_fail(self):
        for mutation in ("duplicate", "scope", "scope_bool", "ordinal", "ordinal_bool",
                         "name", "notation", "position", "function", "extra", "raw", "types",
                         "missing_interface", "wrong_type", "wrong_method"):
            rows = deepcopy(self.rows)
            row = rows[0]
            call = row["observed_syntax"]["named_calls"][0]
            argument = call["named_arguments"][0]
            if mutation == "duplicate":
                rows[-1] = deepcopy(rows[0])
            elif mutation == "scope":
                row["observed_syntax"]["source_free"] = False
            elif mutation == "scope_bool":
                row["observed_syntax"]["source_free"] = 1
            elif mutation == "ordinal":
                argument["ordinal"] += 1
            elif mutation == "ordinal_bool":
                argument["ordinal"] = False
            elif mutation == "name":
                argument["name"] = "months"
            elif mutation == "notation":
                argument["notation"] = "=>"
            elif mutation == "position":
                argument["byte_location"] += 1
            elif mutation == "function":
                call["function"] = "other"
            elif mutation == "extra":
                argument["inferred_type"] = "integer"
            elif mutation == "raw":
                row["raw_sql"] += " "
            elif mutation == "types":
                row["parameter_types"] = "integer"
            else:
                bound = next(r for r in rows if r["parameter_types"] is not None)
                if mutation == "missing_interface":
                    del bound["parameter_type_provenance"]
                elif mutation == "wrong_type":
                    bound["parameter_types"] = "integer"
                else:
                    bound["parameter_type_provenance"]["method"] = "Other"
            with self.subTest(mutation=mutation), self.assertRaises(ValueError):
                validate_population(rows, "named_arguments")

    def test_generated_signature_call_and_sql_identity_are_verified(self):
        row = next(r for r in self.rows if r["parameter_types"] == "double precision")
        url = row["parameter_type_provenance"]["source_url"].split("#")[0]
        evidence = interface_evidence(row["id"], row["sql"], self.interface, url)
        self.assertEqual(evidence, row["parameter_type_provenance"])
        for old, new in (
            ("secs float64", "secs int32"),
            ("makeIntervalSecs, secs", "makeIntervalSecs, 0"),
            ("SELECT make_interval(secs => $1)", "SELECT make_interval(days => $1)"),
            ("func (q *Queries) MakeIntervalSecs", "func (q *Queries) Other"),
        ):
            with self.subTest(old=old), self.assertRaises(ValueError):
                interface_evidence(row["id"], row["sql"], self.interface.replace(old, new), url)
        with self.assertRaises(ValueError):
            interface_evidence("unregistered", row["sql"], self.interface, url)


class NamedArgumentObserverTests(unittest.TestCase):
    def test_mixed_reordered_arguments_preserve_written_notation(self):
        sql = "SELECT f(9, b := 2, a => 1);"
        result = observe_named_arguments(parsed(sql, names=("b", "a"), positional=1), sql)
        call = result["named_calls"][0]
        self.assertEqual(call["argument_names"], [None, "b", "a"])
        self.assertEqual([(a["ordinal"], a["notation"]) for a in call["named_arguments"]],
                         [(1, ":="), (2, "=>")])

    def test_comments_adjacent_signs_and_utf8_byte_positions(self):
        for sql in ("SELECT f(a =>-1, b =>+2);",
                    "SELECT f(a =>/**/1, b =>--line\n2);",
                    "SELECT 'é', f(a /* nested /* c */ */ => 1, b := 2);"):
            with self.subTest(sql=sql):
                result = observe_named_arguments(parsed(sql), sql)
                validate_named_arguments(result, sql)
        sql = "SELECT 'é', f(a => 1, b => 2);"
        tree = parsed(sql)
        tree["SelectStmt"]["targetList"][0]["ResTarget"]["val"]["FuncCall"]["location"] = 9
        with self.assertRaises(ValueError):
            observe_named_arguments(tree, sql)

    def test_string_quoted_qualified_and_comment_lookalikes_fail(self):
        for sql, change in (
            ("SELECT f(a => 1, b => 2);", "position"),
            ("SELECT f(a => 1, b => 2);", "qualified"),
            ("SELECT f(a => 1, b => 2);", "modifier"),
            ("SELECT f(a => 1, b => 2);", "missing"),
        ):
            tree = parsed(sql)
            call = tree["SelectStmt"]["targetList"][0]["ResTarget"]["val"]["FuncCall"]
            if change == "position":
                call["args"][0]["NamedArgExpr"]["location"] = 0
            elif change == "qualified":
                call["funcname"].insert(0, {"String": {"sval": "schema"}})
            elif change == "modifier":
                call["func_variadic"] = True
            else:
                call["args"] = [{"A_Const": {"ival": {"ival": 1}}}]
            with self.subTest(change=change), self.assertRaises(ValueError):
                observe_named_arguments(tree, sql)
        observation = observe_named_arguments(parsed("SELECT f(a => 1, b => 2);"),
                                              "SELECT f(a => 1, b => 2);")
        for sql in ('SELECT f("a"=> 1, b => 2);', "SELECT f('a'=> 1, b => 2);",
                    "SELECT f(/*a=>*/1,b => 2);"):
            with self.subTest(sql=sql), self.assertRaises(ValueError):
                validate_named_arguments(observation, sql)

    def test_duplicate_or_positional_after_named_arguments_are_not_positive_sources(self):
        sql = "SELECT f(a => 1, b => 2);"
        result = observe_named_arguments(parsed(sql), sql)
        for names in (["a", "a"], ["a", None]):
            changed = deepcopy(result)
            changed["named_calls"][0]["argument_names"] = names
            with self.subTest(names=names), self.assertRaises(ValueError):
                validate_named_arguments(changed)

    def test_parameter_source_scope_and_later_dependencies_stay_explicit(self):
        sql = "SELECT f(a => $1, b => 2);"
        tree = parsed(sql)
        call = tree["SelectStmt"]["targetList"][0]["ResTarget"]["val"]["FuncCall"]
        call["args"][0]["NamedArgExpr"]["arg"] = {"ParamRef": {"number": 1}}
        self.assertFalse(observe_named_arguments(tree, sql)["source_free"])
        for kind in ("ColumnRef", "RangeVar", "RangeFunction", "SubLink", "WindowDef",
                     "A_Indirection", "RowExpr", "SQLValueFunction"):
            changed = deepcopy(tree)
            changed["SelectStmt"]["unexpected"] = {kind: {}}
            with self.subTest(kind=kind), self.assertRaises(ValueError):
                observe_named_arguments(changed, sql)


if __name__ == "__main__":
    unittest.main()
