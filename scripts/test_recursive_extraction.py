"""Offline source identity, lexical recursion and input-reader regressions."""
from collections import Counter
from copy import deepcopy
import json
from pathlib import Path
import unittest

from extract_pagination_corpus import comparison_key
from extract_recursive_contract_corpus import ROOT, extract, render, validate_population, validate_registry
from extract_recursive_sqllogic_sql import selected_recursive_sqllogic
from observe_recursive_source import observe_recursive, validate_observation


def position(sql, text, occurrence=0):
    start = -1
    for _ in range(occurrence + 1):
        start = sql.index(text, start + 1)
    return len(sql[:start].encode())


def query(*relations, definitions=(), recursive=False, left=None, right=None):
    node = {"op": "SETOP_NONE", "fromClause": list(relations)}
    if definitions:
        node["withClause"] = {"recursive": recursive, "ctes": list(definitions)}
    if left is not None:
        node.update(op="SETOP_UNION", all=True, larg=left["SelectStmt"], rarg=right["SelectStmt"])
    return {"SelectStmt": node}


def definition(sql, name, body, occurrence=0):
    return {"CommonTableExpr": {
        "ctename": name.strip('"'), "location": position(sql, name + " AS", occurrence),
        "ctequery": body,
    }}


def relation(sql, name, occurrence=0):
    return {"RangeVar": {
        "relname": name.strip('"'),
        "location": position(sql, "FROM " + name, occurrence) + len("FROM ".encode()),
    }}


def example(sql=None):
    sql = sql or "WITH RECURSIVE t AS (SELECT 1 UNION ALL SELECT * FROM t) SELECT * FROM t;"
    body = query(left=query(), right=query(relation(sql, "t", 0)))
    tree = query(relation(sql, "t", 1), definitions=[definition(sql, "t", body)], recursive=True)
    return sql, tree


def block_selector(source, header):
    lines = source.splitlines(keepends=True)
    start = sum(len(line) for line in lines[:header])
    end = source.index("----", start)
    return {"kind": "sqllogic_query", "header_line": header, "start": start, "end": end}


class RecursiveSourceTests(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        cls.directory = ROOT / "fixtures/recursive_contract"
        cls.manifest = json.loads((cls.directory / "concrete_sources.json").read_text())
        cls.rows = extract(cls.manifest)

    def test_fifty_whole_originals_reproduce_without_fabricated_bindings_or_results(self):
        self.assertEqual(render(self.rows), (self.directory / "concrete.jsonl").read_text())
        self.assertEqual(Counter(r["source"] for r in self.rows),
                         {"postgres": 14, "duckdb": 31, "sqlc": 4, "hatchet": 1})
        self.assertEqual(Counter(r["source_kind"] for r in self.rows),
                         {"engine-regression": 45, "compiler-regression": 4, "application-constant": 1})
        for row in self.rows:
            self.assertEqual(row["raw_sql"], row["sql"])
            self.assertEqual(row["transformations"], [])
            self.assertIsNone(row["parameter_types"])
            self.assertNotIn("parameter_values", row)
            self.assertNotIn("expected_value", row)
        self.assertEqual([(r["source"], r["observed_parameter_slots"]) for r in self.rows
                          if r["observed_parameter_slots"]], [("hatchet", [2, 1, 3, 4]), ("sqlc", [1])])

    def test_actual_recursion_and_missing_prerequisites_are_explicit(self):
        definitions = [d for r in self.rows for d in r["observed_syntax"]["ctes"]]
        relations = [d for r in self.rows for d in r["observed_syntax"]["relations"]]
        self.assertEqual((len(definitions), len(relations)), (58, 157))
        self.assertEqual(sum(d["self_references"] != 0 for d in definitions), 55)
        self.assertEqual(sum(d["definition_byte_location"] is None for d in relations), 39)
        self.assertEqual(sum(r["observed_syntax"]["source_free"] for r in self.rows), 31)
        self.assertEqual(sum(r["observed_syntax"]["source_free"] and not r["observed_syntax"]["dependencies"]
                             for r in self.rows), 21)
        self.assertEqual(Counter(k for r in self.rows for k in r["observed_syntax"]["dependencies"]),
                         {"SubLink": 5, "aggregate": 5, "function_calls": 3, "distinctClause": 2})

    def test_all_fifty_are_new_relative_to_prior_concrete_populations(self):
        normalize = lambda sql: comparison_key(sql).rstrip(";").strip()
        prior = set()
        for file in (ROOT / "fixtures").rglob("concrete.jsonl"):
            if file.parent != self.directory:
                prior.update(normalize(json.loads(line)["sql"]) for line in file.read_text().splitlines())
        self.assertFalse({normalize(r["sql"]) for r in self.rows} & prior)

    def test_preregistered_exact_outputs_and_eligibility_are_immutable(self):
        registry = json.loads((self.directory / "source_contracts.json").read_text())
        validate_registry(self.rows, registry)
        columns = [c for entry in registry for c in entry["output_columns"]]
        self.assertEqual((len(registry), len(columns)), (21, 24))
        self.assertEqual(Counter(c["type"] for c in columns),
                         {"int32": 20, "text": 2, "integer[]": 1, "bigint": 1})
        self.assertTrue(all(c["nullable"] is True for c in columns))
        self.assertIn(["n", "fibₙ"], [[c["name"] for c in e["output_columns"]] for e in registry])
        mutations = [
            lambda r: r.pop(),
            lambda r: r[0].update(id=self.rows[0]["id"]),
            lambda r: r[0]["output_columns"][0].update(name="renamed"),
            lambda r: r[0]["output_columns"][0].update(type="text"),
            lambda r: r[0]["output_columns"][0].update(nullable=1),
            lambda r: r[0]["output_columns"][0].update(nullable=False),
            lambda r: r[-1]["output_columns"].reverse(),
        ]
        for mutate in mutations:
            bad = deepcopy(registry)
            mutate(bad)
            with self.subTest(mutate=mutate), self.assertRaises(ValueError):
                validate_registry(self.rows, bad)
        bad = deepcopy(self.rows)
        index = next(i for i, r in enumerate(bad) if r["id"] == registry[0]["id"])
        bad[index]["observed_syntax"]["dependencies"] = {"aggregate": 1}
        with self.assertRaises(ValueError):
            validate_registry(bad, registry)

    def test_pinned_source_license_statement_span_and_population_mutations_fail(self):
        mutations = [
            lambda m: m.update(expected_count=49),
            lambda m: m["sources"]["postgres"].update(commit="main"),
            lambda m: m["sources"]["duckdb"].update(license_sha256="0" * 64),
            lambda m: m["sources"]["duckdb"]["files"][0].update(sha256="0" * 64),
            lambda m: m["selections"][1].update(sql_sha256="0" * 64),
            lambda m: m["selections"][1]["selector"].update(start=29),
            lambda m: m["selections"][0]["selector"].update(symbol="unregisteredConstant"),
        ]
        for mutate in mutations:
            bad = deepcopy(self.manifest)
            mutate(bad)
            with self.subTest(mutate=mutate), self.assertRaises(ValueError):
                extract(bad)
        for field, value in (("raw_sql", "SELECT 0"), ("parameter_types", ["integer"]),
                             ("parameter_values", [1]), ("expected_value", "1")):
            bad = deepcopy(self.rows)
            bad[0][field] = value
            with self.subTest(field=field), self.assertRaises(ValueError):
                validate_population(bad)
        bad = deepcopy(self.rows)
        bad[-1] = deepcopy(bad[0])
        with self.assertRaises(ValueError):
            validate_population(bad)

    def test_lexical_binding_distinguishes_self_reference_from_outer_use(self):
        sql, tree = example()
        value = observe_recursive(tree, sql)
        self.assertEqual(value["actual_recursive_count"], 1)
        self.assertEqual([(c["self_references"], c["anchor_references"], c["step_references"])
                          for c in value["ctes"]], [(1, 0, 1)])
        self.assertEqual([r["contexts"] for r in value["relations"]],
                         [[{"definition_byte_location": 15, "arm": "step"}], []])

    def test_keyword_only_recursive_is_observed_without_inventing_self_recursion(self):
        sql = "WITH RECURSIVE t AS (SELECT 1) SELECT * FROM t;"
        value = observe_recursive(query(relation(sql, "t"),
                                  definitions=[definition(sql, "t", query())], recursive=True), sql)
        self.assertEqual(value["actual_recursive_count"], 0)
        self.assertTrue(value["source_free"])
        # The observer describes this syntax, but the fixed factor witnesses
        # must each exercise actual recursion.
        bad = deepcopy(self.rows)
        bad[0].update(sql=sql, raw_sql=sql, observed_syntax=value, observed_parameter_slots=[])
        with self.assertRaises(ValueError):
            validate_population(bad)

    def test_recursive_siblings_are_visible_forward_but_not_claimed_supported(self):
        sql = ("WITH RECURSIVE a AS (SELECT * FROM b), "
               "b AS (SELECT 1 UNION ALL SELECT * FROM b) SELECT * FROM a;")
        a = definition(sql, "a", query(relation(sql, "b")))
        b = definition(sql, "b", query(left=query(), right=query(relation(sql, "b", 1))))
        value = observe_recursive(query(relation(sql, "a"), definitions=[a, b], recursive=True), sql)
        self.assertTrue(value["source_free"])
        self.assertEqual(value["relations"][0]["definition_byte_location"], position(sql, "b AS"))
        self.assertEqual([c["self_references"] for c in value["ctes"]], [0, 1])

    def test_schema_qualified_same_name_remains_an_external_relation(self):
        sql = "WITH RECURSIVE t AS (SELECT 1 UNION ALL SELECT * FROM t) SELECT * FROM qa.t;"
        body = query(left=query(), right=query(relation(sql, "t")))
        qualified = {"RangeVar": {"relname": "t", "schemaname": "qa",
                                  "location": position(sql, "qa.t")}}
        value = observe_recursive(query(qualified, definitions=[definition(sql, "t", body)],
                                        recursive=True), sql)
        self.assertEqual(value["actual_recursive_count"], 1)
        self.assertFalse(value["source_free"])
        self.assertEqual(value["relations"][-1]["parts"], ["qa", "t"])
        self.assertIsNone(value["relations"][-1]["definition_byte_location"])

    def test_anchor_self_reference_is_observed_then_excluded_from_selected_population(self):
        sql = "WITH RECURSIVE t AS (SELECT * FROM t UNION ALL SELECT 1) SELECT * FROM t;"
        body = query(left=query(relation(sql, "t")), right=query())
        value = observe_recursive(query(relation(sql, "t", 1),
                                  definitions=[definition(sql, "t", body)], recursive=True), sql)
        self.assertEqual((value["ctes"][0]["anchor_references"],
                          value["ctes"][0]["step_references"]), (1, 0))
        bad = deepcopy(self.rows)
        bad[0].update(sql=sql, raw_sql=sql, observed_syntax=value, observed_parameter_slots=[])
        with self.assertRaisesRegex(ValueError, "linear anchor/step"):
            validate_population(bad)

    def test_nonrecursive_inner_shadow_reads_outer_cte_then_rebinds_body(self):
        sql = ("WITH RECURSIVE t AS (SELECT 1 UNION ALL SELECT * FROM t), "
               "u AS (WITH t AS (SELECT * FROM t) SELECT * FROM t) SELECT * FROM u;")
        outer = definition(sql, "t", query(left=query(), right=query(relation(sql, "t"))))
        inner = definition(sql, "t", query(relation(sql, "t", 1)), occurrence=1)
        u = definition(sql, "u", query(relation(sql, "t", 2), definitions=[inner]))
        value = observe_recursive(query(relation(sql, "u"), definitions=[outer, u], recursive=True), sql)
        bindings = [r["definition_byte_location"] for r in value["relations"]]
        self.assertEqual(bindings, [position(sql, "t AS"), position(sql, "t AS"),
                                    position(sql, "t AS", 1), position(sql, "u AS")])
        self.assertEqual(value["actual_recursive_count"], 1)

    def test_join_operands_do_not_get_mistaken_for_raw_select_set_operands(self):
        sql = ("WITH RECURSIVE t AS (SELECT 1 UNION ALL "
               "SELECT * FROM t JOIN external ON TRUE) SELECT * FROM t;")
        join = {"JoinExpr": {"larg": relation(sql, "t"),
                            "rarg": {"RangeVar": {"relname": "external",
                                      "location": position(sql, "external")}}}}
        body = query(left=query(), right=query(join))
        value = observe_recursive(query(relation(sql, "t", 1),
                                  definitions=[definition(sql, "t", body)], recursive=True), sql)
        self.assertFalse(value["source_free"])
        self.assertEqual(value["ctes"][0]["step_references"], 1)
        self.assertIsNone(value["relations"][1]["definition_byte_location"])

    def test_unicode_positions_and_numbered_parameter_first_use_order(self):
        sql = ('WITH RECURSIVE "é" AS (SELECT $2 UNION ALL SELECT $1 FROM "é") '
               'SELECT $2 FROM "é";')
        left = query()
        left["SelectStmt"]["targetList"] = [{"ParamRef": {"number": 2, "location": position(sql, "$2")}}]
        right = query(relation(sql, '"é"'))
        right["SelectStmt"]["targetList"] = [{"ParamRef": {"number": 1, "location": position(sql, "$1")}}]
        tree = query(relation(sql, '"é"', 1),
                     definitions=[definition(sql, '"é"', query(left=left, right=right))], recursive=True)
        tree["SelectStmt"]["targetList"] = [{"ParamRef": {"number": 2, "location": position(sql, "$2", 1)}}]
        value = observe_recursive(tree, sql)
        self.assertEqual(value["parameter_slots"], [2, 1])
        self.assertFalse(value["source_free"])
        self.assertEqual(value["ctes"][0]["step_references"], 1)
        bad = deepcopy(value)
        bad["relations"][0]["byte_location"] -= 1
        with self.assertRaises(ValueError):
            validate_observation(bad, sql)

    def test_reference_count_boolean_and_context_mutations_are_rejected(self):
        sql, tree = example()
        value = observe_recursive(tree, sql)
        mutations = [
            lambda v: v["ctes"][0].update(self_references=0),
            lambda v: v["ctes"][0].update(anchor_references=True),
            lambda v: v["ctes"][0].update(with_recursive=False),
            lambda v: v["relations"][0].update(definition_byte_location=None),
            lambda v: v["relations"][0]["contexts"][0].update(arm="unknown"),
            lambda v: v.update(source_free=1),
            lambda v: v.update(parameter_slots=[1, 1]),
        ]
        for mutate in mutations:
            bad = deepcopy(value)
            mutate(bad)
            with self.subTest(mutate=mutate), self.assertRaises(ValueError):
                validate_observation(bad, sql)

    def test_slt_reader_retains_exact_requirement_and_crlf_bytes(self):
        source = ("require no_alternative_verify\r\n\r\nstatement ok\r\nPRAGMA disable_verification\r\n\r\n"
                  "query I\r\nWITH RECURSIVE t AS (SELECT 1 UNION SELECT * FROM t) SELECT * FROM t;\r\n"
                  "----\r\n1\r\n\r\nunknown control after selection\r\n")
        selector = block_selector(source, 6)
        sql, line, detail = selected_recursive_sqllogic(source, selector)
        self.assertTrue(sql.endswith(";\r\n"))
        self.assertEqual(line, 7)
        self.assertEqual(detail["source_requirements"], ["require no_alternative_verify"])
        self.assertEqual(sql, source[selector["start"]:selector["end"]])
        self.assertEqual(sum(bool(r.get("source_requirements")) for r in self.rows), 3)

    def test_slt_results_are_opaque_and_unknown_prefix_controls_fail_closed(self):
        source = ("query I\nSELECT 1;\n----\nquery I\nWITH RECURSIVE fake AS (SELECT 1) SELECT 1;\n\n"
                  "query I\nWITH RECURSIVE t AS (SELECT 1 UNION SELECT * FROM t) SELECT * FROM t;\n----\n1\n")
        selected = block_selector(source, 7)
        sql, _, _ = selected_recursive_sqllogic(source, selected)
        self.assertIn("RECURSIVE t AS", sql)
        fake = {"kind": "sqllogic_query", "header_line": 4,
                "start": source.index("WITH RECURSIVE fake"), "end": source.index("\n\n")}
        with self.assertRaises(ValueError):
            selected_recursive_sqllogic(source, fake)
        for prefix in ("require extension\n", "onlyif postgres\n", "load file\n",
                       "require no_alternative_verify\nrequire no_alternative_verify\n"):
            bad = prefix + source
            selector = block_selector(bad, 7 + prefix.count("\n"))
            with self.subTest(prefix=prefix), self.assertRaises(ValueError):
                selected_recursive_sqllogic(bad, selector)

    def test_slt_partial_multiple_substituted_and_unterminated_inputs_fail(self):
        for sql in ("SELECT 1; SELECT 2;\n", "SELECT '${value}';\n", "SELECT 1\n\n"):
            source = "query I\n" + sql + "----\n1\n"
            with self.subTest(sql=sql), self.assertRaises(ValueError):
                selected_recursive_sqllogic(source, block_selector(source, 1))
        source = "query I\nSELECT 1;\n----\n1\n"
        selector = block_selector(source, 1)
        selector["start"] += 1
        with self.assertRaises(ValueError):
            selected_recursive_sqllogic(source, selector)
        source = "query I\nSELECT 1;\n"
        with self.assertRaises(ValueError):
            selected_recursive_sqllogic(source, {"kind": "sqllogic_query", "header_line": 1,
                                               "start": 8, "end": len(source)})


if __name__ == "__main__":
    unittest.main()
