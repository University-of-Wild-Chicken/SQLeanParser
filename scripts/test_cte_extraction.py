"""Pinned whole-query CTE sources and lexical observation boundaries."""
from collections import Counter
from copy import deepcopy
import json
import unittest

from extract_cockroach_sqllogic_sql import selected_cockroach_sql
from extract_factor_corpus import ROOT, extract, render, validate_population
from extract_pagination_corpus import comparison_key
from extract_sqllogic_sql import selected_sqllogic_sql
from observe_cte_source import observe_ctes, validate_ctes


def query(*relations, definitions=()):
    node = {"op": "SETOP_NONE", "fromClause": list(relations)}
    if definitions:
        node["withClause"] = {"ctes": list(definitions)}
    return {"SelectStmt": node}


def definition(sql, name, body=None, *, occurrence=0, aliases=()):
    spelling = name + " AS"
    location = -1
    for _ in range(occurrence + 1):
        location = sql.index(spelling, location + 1)
    return {"CommonTableExpr": {
        "ctename": name.strip('"'), "location": len(sql[:location].encode()),
        "aliascolnames": [{"String": {"sval": n}} for n in aliases],
        "ctematerialized": "CTEMaterializeDefault", "ctequery": body or query(),
    }}


def relation(sql, name, *, occurrence=0):
    spelling, position = "FROM " + name, -1
    for _ in range(occurrence + 1):
        position = sql.index(spelling, position + 1)
    parts = name.split(".")
    return {"RangeVar": {
        "relname": parts[-1].strip('"'), "location": len(sql[:position + 5].encode()),
        **({"schemaname": parts[0]} if len(parts) == 2 else {}),
    }}


class CTESourceTests(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        cls.directory = ROOT / "fixtures/cte_contract"
        cls.manifest = json.loads((cls.directory / "concrete_sources.json").read_text())
        cls.rows = extract(cls.manifest, "cte_contract")

    def test_fifty_unchanged_sources_reproduce_with_real_catalog_and_input_dependencies(self):
        self.assertEqual(render(self.rows), (self.directory / "concrete.jsonl").read_text())
        self.assertEqual(Counter(r["source"] for r in self.rows),
                         {"postgres": 7, "sqlc": 8, "materialize": 14, "duckdb": 12, "sqlite": 7, "hatchet": 2})
        self.assertEqual(Counter(r["source_kind"] for r in self.rows),
                         {"engine-regression": 40, "compiler-regression": 8, "application-constant": 2})
        self.assertEqual(len({comparison_key(r["sql"]).rstrip(";").strip() for r in self.rows}), 50)
        for row in self.rows:
            self.assertEqual(row["raw_sql"], row["sql"])
            self.assertEqual(row["transformations"], [])
            self.assertIsNone(row["parameter_types"])
            self.assertNotIn("parameter_values", row)
            self.assertNotIn("expected_value", row)
            self.assertEqual(row["application_schema_validity"], "not-claimed")
        parameters = [(r["source"], r["observed_parameter_slots"]) for r in self.rows if r["observed_parameter_slots"]]
        self.assertEqual(parameters, [("sqlc", [1]), ("hatchet", [1]), ("hatchet", [1, 2])])

    def test_exact_lexical_footprint_keeps_nested_and_repeated_definitions(self):
        definitions = [e for r in self.rows for e in r["observed_syntax"]["ctes"]]
        relations = [e for r in self.rows for e in r["observed_syntax"]["cte_relations"]]
        self.assertEqual((len(definitions), len(relations)), (78, 130))
        self.assertEqual(sum(e["definition_byte_location"] is None for e in relations), 55)
        self.assertEqual(sum(e["shadows_visible"] for e in definitions), 5)
        self.assertEqual(sum(bool(e["column_aliases"]) for e in definitions), 14)
        self.assertEqual(Counter(e["query_depth"] for e in definitions), {0: 60, 1: 13, 2: 3, 3: 2})
        self.assertEqual(Counter(r["observed_syntax"]["source_free"] for r in self.rows), {True: 13, False: 37})

    def test_preregistered_outputs_are_fixed_before_checking_source_queries(self):
        registry = json.loads((self.directory / "source_contracts.json").read_text())
        self.assertEqual(len(registry), 13)
        self.assertEqual({r["id"] for r in registry},
                         {r["id"] for r in self.rows if r["observed_syntax"]["source_free"]})
        columns = [c for r in registry for c in r["output_columns"]]
        self.assertEqual((len(columns), Counter(c["type"] for c in columns)),
                         (21, {"int32": 15, "text": 2, "bool": 4}))
        self.assertTrue(all(c["nullable"] is False for c in columns))
        self.assertIn(["x", "y", "x", "y"], [[c["name"] for c in r["output_columns"]] for r in registry])
        self.assertIn(["zzz", "y"], [[c["name"] for c in r["output_columns"]] for r in registry])

    def test_literal_conditional_test_provenance_is_retained_without_execution(self):
        conditional = [r for r in self.rows if r.get("source_condition")]
        self.assertEqual([(r["source"], r["line"]) for r in conditional],
                         [("materialize", 38), ("materialize", 46), ("materialize", 74), ("materialize", 299)])
        self.assertTrue(all(r["source_condition"] == "onlyif cockroach" for r in conditional))
        shipping = [r for r in self.rows if r["source"] == "hatchet"]
        self.assertEqual([r["symbol"] for r in shipping], ["readDAGByExternalID", "lookUpTraceId"])
        self.assertTrue(all(r["license"] == "MIT" for r in shipping))

    def test_source_hash_license_selector_and_closed_population_mutations_fail(self):
        for change in ("license", "source_hash", "sql_hash", "pin", "count", "population",
                       "selector_start", "selector_header", "source", "unused"):
            manifest = deepcopy(self.manifest)
            selected = next(s for s in manifest["selections"] if s["source"] == "duckdb")
            metadata = manifest["sources"]["duckdb"]
            if change == "license":
                metadata["license_sha256"] = "0" * 64
            elif change == "source_hash":
                metadata["files"][0]["sha256"] = "0" * 64
            elif change == "sql_hash":
                selected["sql_sha256"] = "0" * 64
            elif change == "pin":
                metadata["commit"] = "main"
            elif change == "count":
                manifest["selections"].pop()
            elif change == "population":
                manifest["expected_sources"]["duckdb"] += 1
            elif change.startswith("selector_"):
                selected["selector"]["start" if change == "selector_start" else "header_line"] += 1
            elif change == "source":
                selected["source"] = "postgres"
            else:
                metadata["files"].append(deepcopy(metadata["files"][0]))
            with self.subTest(change=change), self.assertRaises(ValueError):
                extract(manifest, "cte_contract")

    def test_observation_mutations_do_not_become_new_certificate_or_scope_evidence(self):
        for change in ("name", "location", "location_bool", "depth", "shadow", "shadow_int",
                       "aliases", "reference", "reference_bool", "scope", "scope_int", "extra",
                       "missing", "bindings", "raw", "duplicate"):
            rows = deepcopy(self.rows)
            row = next(r for r in rows if r["observed_syntax"]["source_free"])
            observation = row["observed_syntax"]
            entry = observation["ctes"][0]
            if change == "name":
                entry["name"] = "wrong"
            elif change == "location":
                entry["byte_location"] += 1
            elif change == "location_bool":
                entry["byte_location"] = True
            elif change == "depth":
                entry["query_depth"] += 1
            elif change in {"shadow", "shadow_int"}:
                entry["shadows_visible"] = True if change == "shadow" else 0
            elif change == "aliases":
                entry["column_aliases"] = []
            elif change in {"reference", "reference_bool"}:
                observation["cte_relations"][0]["definition_byte_location"] = None if change == "reference" else True
            elif change in {"scope", "scope_int"}:
                observation["source_free"] = False if change == "scope" else 1
            elif change == "extra":
                entry["inferred_type"] = "int32"
            elif change == "missing":
                observation["ctes"] = []
            elif change == "bindings":
                row["parameter_types"] = "int"
            elif change == "raw":
                row["raw_sql"] += " "
            else:
                rows[-1] = deepcopy(rows[0])
            with self.subTest(change=change), self.assertRaises(ValueError):
                validate_population(rows, "cte_contract")


class CTELexicalObservationTests(unittest.TestCase):
    def test_prior_definitions_are_visible_sequentially(self):
        sql = "WITH a AS (SELECT 1), b AS (SELECT * FROM a) SELECT * FROM b"
        first = definition(sql, "a")
        second = definition(sql, "b", query(relation(sql, "a")))
        tree = query(relation(sql, "b"), definitions=[first, second])
        observed = observe_ctes(tree, sql)
        self.assertTrue(observed["source_free"])
        self.assertEqual([r["definition_byte_location"] for r in observed["cte_relations"]],
                         [first["CommonTableExpr"]["location"], second["CommonTableExpr"]["location"]])

    def test_forward_reference_remains_external_without_inventing_a_catalog(self):
        sql = "WITH a AS (SELECT * FROM b), b AS (SELECT 1) SELECT * FROM a"
        tree = query(relation(sql, "a"), definitions=[
            definition(sql, "a", query(relation(sql, "b"))), definition(sql, "b")])
        observed = observe_ctes(tree, sql)
        self.assertFalse(observed["source_free"])
        self.assertIsNone(observed["cte_relations"][0]["definition_byte_location"])

    def test_shadowing_definition_sees_outer_binding_then_publishes_its_own(self):
        sql = "WITH a AS (SELECT 1) SELECT * FROM (WITH a AS (SELECT * FROM a) SELECT * FROM a) d"
        outer = definition(sql, "a")
        inner = definition(sql, "a", query(relation(sql, "a")), occurrence=1)
        child = query(relation(sql, "a", occurrence=1), definitions=[inner])
        tree = query({"RangeSubselect": {"subquery": child}}, definitions=[outer])
        observed = observe_ctes(tree, sql)
        self.assertEqual([e["shadows_visible"] for e in observed["ctes"]], [False, True])
        self.assertEqual([e["query_depth"] for e in observed["ctes"]], [0, 1])
        self.assertEqual([r["definition_byte_location"] for r in observed["cte_relations"]],
                         [outer["CommonTableExpr"]["location"], inner["CommonTableExpr"]["location"]])

    def test_qualified_relation_and_parameter_declarations_remain_external_assumptions(self):
        sql = "WITH a AS (SELECT 1) SELECT * FROM public.a"
        result = observe_ctes(query(relation(sql, "public.a"), definitions=[definition(sql, "a")]), sql)
        self.assertEqual(result["cte_relations"][0]["parts"], ["public", "a"])
        self.assertFalse(result["source_free"])
        sql = "WITH a AS (SELECT $1) SELECT * FROM a"
        body = query()
        body["SelectStmt"]["targetList"] = [{"ResTarget": {"val": {"ParamRef": {"number": 1}}}}]
        result = observe_ctes(query(relation(sql, "a"), definitions=[definition(sql, "a", body)]), sql)
        self.assertFalse(result["source_free"])

    def test_quoted_name_and_utf8_source_positions_are_not_flattened(self):
        sql = 'WITH "A" AS (SELECT \'é\') SELECT * FROM "A"'
        tree = query(relation(sql, '"A"'), definitions=[definition(sql, '"A"')])
        result = observe_ctes(tree, sql)
        self.assertEqual(result["ctes"][0]["name"], "A")
        self.assertTrue(result["source_free"])
        invalid = deepcopy(result)
        invalid["cte_relations"][0]["byte_location"] -= 1
        with self.assertRaises(ValueError):
            validate_ctes(invalid, sql)

    def test_other_cte_features_and_expression_dependencies_fail_closed(self):
        sql = "WITH a AS (SELECT 1) SELECT * FROM a"
        for change in ("recursive", "materialized", "duplicate", "modifying", "values", "setop",
                       "group", "aggregate", "subquery", "lateral", "window"):
            tree = query(relation(sql, "a"), definitions=[definition(sql, "a")])
            outer = tree["SelectStmt"]
            with_ = outer["withClause"]
            cte = with_["ctes"][0]["CommonTableExpr"]
            body = cte["ctequery"]["SelectStmt"]
            if change == "recursive":
                with_["recursive"] = True
            elif change == "materialized":
                cte["ctematerialized"] = "CTEMaterializeAlways"
            elif change == "duplicate":
                with_["ctes"].append(deepcopy(with_["ctes"][0]))
            elif change == "modifying":
                cte["ctequery"] = {"DeleteStmt": {}}
            elif change == "values":
                body["valuesLists"] = [[{"A_Const": {"isnull": True}}]]
            elif change == "setop":
                body["op"] = "SETOP_UNION"
            elif change == "group":
                body["groupClause"] = [{"A_Const": {"isnull": True}}]
            elif change == "lateral":
                body["fromClause"] = [{"RangeSubselect": {"lateral": True, "subquery": query()}}]
            else:
                key = {"aggregate": "FuncCall", "subquery": "SubLink", "window": "WindowDef"}[change]
                body["targetList"] = [{"ResTarget": {"val": {key: {}}}}]
            with self.subTest(change=change), self.assertRaises(ValueError):
                observe_ctes(tree, sql)

    def test_reference_metadata_cannot_point_to_an_unrelated_definition(self):
        sql = "WITH a AS (SELECT 1), b AS (SELECT 2) SELECT * FROM a"
        observed = observe_ctes(query(relation(sql, "a"), definitions=[
            definition(sql, "a"), definition(sql, "b")]), sql)
        observed["cte_relations"][0]["definition_byte_location"] = observed["ctes"][1]["byte_location"]
        with self.assertRaises(ValueError):
            validate_ctes(observed, sql)


class CTEPrefixReaderTests(unittest.TestCase):
    @staticmethod
    def selector(source, sql, kind):
        start = source.index(sql)
        return dict(kind=kind, start=start, end=start + len(sql),
                    header_line=source[:start].count("\n"))

    def test_duckdb_prefix_opt_in_never_ignores_earlier_unknown_controls(self):
        sql = "WITH x AS (SELECT 1) SELECT * FROM x\n"
        source = "query I\n" + sql + "----\n1\n\nrequire optional_feature\n"
        selector = self.selector(source, sql, "sqllogic_query")
        self.assertEqual(selected_sqllogic_sql(source, selector, prefix_only=True)[0], sql)
        with self.assertRaises(ValueError):
            selected_sqllogic_sql(source, selector)
        source = "require optional_feature\n" + source
        with self.assertRaises(ValueError):
            selected_sqllogic_sql(source, self.selector(source, sql, "sqllogic_query"), prefix_only=True)

    def test_materialize_condition_and_count_records_have_explicit_cte_provenance(self):
        sql = "WITH x AS (SELECT 1) SELECT * FROM x\n"
        prefix = "mode cockroach\nstatement count 1\nINSERT INTO x VALUES (1)\n\nonlyif cockroach\n"
        source = prefix + "query I\n" + sql + "----\n1\n"
        selector = self.selector(source, sql, "cockroach_sqllogic_query")
        actual, _, details = selected_cockroach_sql(source, selector, cte_queries=True)
        self.assertEqual(actual, sql)
        self.assertEqual(details["source_condition"], "onlyif cockroach")
        with self.assertRaises(ValueError):
            selected_cockroach_sql(source, selector, null_predicates=True)
        for changed in (source.replace("onlyif cockroach", "onlyif postgres"),
                        source.replace("statement count 1", "statement count $n")):
            with self.assertRaises(ValueError):
                selected_cockroach_sql(changed, self.selector(changed, sql, "cockroach_sqllogic_query"),
                                      cte_queries=True)

    def test_cte_prefix_requires_whole_query_not_a_body_or_expected_result(self):
        sql = "WITH x AS (SELECT 1) SELECT * FROM x\n"
        source = "query I\n" + sql + "----\nSELECT 2\n"
        selected = self.selector(source, sql, "sqllogic_query")
        for change in ("body", "end", "header_bool"):
            selector = dict(selected)
            if change == "body":
                selector["start"] = source.index("SELECT 1")
            elif change == "end":
                selector["end"] -= 1
            else:
                selector["header_line"] = True
            with self.subTest(change=change), self.assertRaises(ValueError):
                selected_sqllogic_sql(source, selector, prefix_only=True)


if __name__ == "__main__":
    unittest.main()
