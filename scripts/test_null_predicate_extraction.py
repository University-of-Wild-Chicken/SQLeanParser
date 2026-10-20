"""Unchanged source identities and finite NULL-predicate input readers."""
from collections import Counter
from copy import deepcopy
import json
import unittest

from extract_cockroach_sqllogic_sql import selected_cockroach_sql
from extract_factor_corpus import ROOT, extract, render, validate_population
from extract_null_predicate_input import selected_null_input
from extract_pagination_corpus import comparison_key
from observe_null_predicate_source import observe_null_predicates, validate_null_predicates


def embedded(source, context, sql, container=None):
    container = sql if container is None else container
    a = source.index(container)
    start = source.index(sql, a)
    return dict(kind="embedded_null_input", context=context, start=start,
                end=start + len(sql), container_start=a, container_end=a + len(container))


def null_tree(sql, argument=None, negated=False):
    location = next(i for i in range(len(sql)) if sql[i:].upper().startswith(
        ("ISNULL", "NOTNULL", "IS NULL", "IS NOT NULL")))
    return {"SelectStmt": {"targetList": [{"ResTarget": {"val": {"NullTest": {
        "arg": argument or {"A_Const": {"isnull": True}},
        "location": len(sql[:location].encode()),
        "nulltesttype": "IS_NOT_NULL" if negated else "IS_NULL",
    }}}}]}}


class NullSourceExtractionTests(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        cls.manifests = {f: json.loads((ROOT / f"fixtures/{f}/concrete_sources.json").read_text())
                         for f in ("distinct_from", "null_predicates")}
        cls.rows = {f: extract(m, f) for f, m in cls.manifests.items()}

    def test_closed_populations_reproduce_without_sql_or_binding_transformations(self):
        for factor, rows in self.rows.items():
            self.assertEqual(render(rows), (ROOT / f"fixtures/{factor}/concrete.jsonl").read_text())
            self.assertEqual(len({comparison_key(r["sql"]).rstrip(";").strip() for r in rows}), 50)
            for row in rows:
                self.assertEqual(row["raw_sql"], row["sql"])
                self.assertEqual(row["transformations"], [])
                self.assertIsNone(row["parameter_types"])
                self.assertEqual(row["observed_parameter_slots"], [])
                self.assertNotIn("expected_value", row)
                self.assertNotIn("parameter_values", row)
        self.assertEqual(Counter(r["source"] for r in self.rows["distinct_from"]),
                         {"postgres": 18, "materialize": 20, "duckdb": 12})
        self.assertEqual(Counter(r["source"] for r in self.rows["null_predicates"]),
                         {"h2": 22, "sqlite": 10, "sqlglot": 5, "materialize": 3,
                          "duckdb": 3, "postgres": 2, "turso": 2, "sqlparser-rs": 1,
                          "jsqlparser": 1, "calcite": 1})

    def test_new_spelling_counts_and_structural_scope_are_fixed(self):
        expected = {
            "distinct_from": ({"is distinct from": 37, "is not distinct from": 22}, 25),
            "null_predicates": ({"isnull": 18, "notnull": 11, "is null": 19, "is not null": 12}, 23),
        }
        for factor, (forms, closed) in expected.items():
            rows = self.rows[factor]
            self.assertEqual(Counter(e["form"] for r in rows for e in r["observed_syntax"][factor]), forms)
            self.assertEqual(sum(r["observed_syntax"]["source_free"] for r in rows), closed)
        entries = [e for r in self.rows["null_predicates"] for e in r["observed_syntax"]["null_predicates"]]
        self.assertEqual(Counter(e["row_arity"] for e in entries), {None: 29, 0: 1, 2: 20, 3: 9, 4: 1})
        nested = [r for r in self.rows["null_predicates"]
                  if any(e["nested_row"] for e in r["observed_syntax"]["null_predicates"])]
        self.assertEqual([r["source"] for r in nested], ["calcite"])

    def test_registered_complete_sources_are_not_success_selected(self):
        registry = json.loads((ROOT / "fixtures/null_predicates/source_contracts.json").read_text())
        self.assertEqual({f: len(rs) for f, rs in registry.items()}, {"distinct_from": 25, "null_predicates": 22})
        self.assertEqual({f: sum(len(r["output_columns"]) for r in rs) for f, rs in registry.items()},
                         {"distinct_from": 34, "null_predicates": 25})
        for factor, rows in self.rows.items():
            expected_ids = {r["id"] for r in rows
                            if r["observed_syntax"]["source_free"] and r["source"] != "calcite"}
            self.assertEqual({r["id"] for r in registry[factor]}, expected_ids)
            for row in registry[factor]:
                self.assertTrue(all(c["nullable"] is False for c in row["output_columns"]))
        null_columns = [c for r in registry["null_predicates"] for c in r["output_columns"]]
        self.assertEqual(Counter(c["type"] for c in null_columns), {"bool": 23, "varchar": 2})
        self.assertEqual([c["name"] for c in null_columns if c["type"] == "varchar"], ["varchar", "varchar"])

    def test_explain_input_bodies_retain_whole_wrappers_and_are_not_expected_plans(self):
        rows = [r for r in self.rows["null_predicates"] if r.get("source_container", "").startswith("EXPLAIN ")]
        self.assertEqual(len(rows), 6)
        for row in rows:
            self.assertEqual(row["source_container"], "EXPLAIN " + row["sql"])
            self.assertEqual(row["source_start"], row["container_start"] + 8)
            self.assertEqual(row["source_end"], row["container_end"])

    def test_source_license_selector_population_and_sql_hash_mutations_fail(self):
        for change in ("license", "source_hash", "sql_hash", "pin", "count", "population",
                       "offset", "context", "wrapper", "extra_file"):
            manifest = deepcopy(self.manifests["null_predicates"])
            selection = next(s for s in manifest["selections"] if s["source"] == "h2")
            metadata = manifest["sources"]["h2"]
            if change == "license":
                metadata["license_sha256"] = "0" * 64
            elif change == "source_hash":
                metadata["files"][0]["sha256"] = "0" * 64
            elif change == "sql_hash":
                selection["sql_sha256"] = "0" * 64
            elif change == "pin":
                metadata["commit"] = "main"
            elif change == "count":
                manifest["selections"].pop()
            elif change == "population":
                manifest["expected_sources"]["h2"] += 1
            elif change == "offset":
                selection["selector"]["start"] += 1
            elif change == "context":
                selection["selector"]["context"] = "python"
            elif change == "wrapper":
                selection["selector"]["container_start"] += 1
            else:
                metadata["files"].append(deepcopy(metadata["files"][0]))
            with self.subTest(change=change), self.assertRaises(ValueError):
                extract(manifest, "null_predicates")

    def test_observation_mutation_is_not_new_syntax_evidence(self):
        for factor in self.rows:
            for change in ("form", "byte", "bool_byte", "scope", "scope_int", "extra", "missing",
                           "bindings", "raw", "duplicate"):
                rows = deepcopy(self.rows[factor])
                row, observation = rows[0], rows[0]["observed_syntax"]
                entry = observation[factor][0]
                if change == "form":
                    entry["form"] = "is not distinct from" if factor == "distinct_from" else "notnull"
                elif change == "byte":
                    entry["byte_location"] += 1
                elif change == "bool_byte":
                    entry["byte_location"] = True
                elif change in {"scope", "scope_int"}:
                    observation["source_free"] = False if change == "scope" else 1
                elif change == "extra":
                    entry["inferred_type"] = "bool"
                elif change == "missing":
                    observation[factor] = []
                elif change == "bindings":
                    row["parameter_types"] = "int"
                elif change == "raw":
                    row["raw_sql"] += " "
                else:
                    rows[-1] = deepcopy(rows[0])
                with self.subTest(factor=factor, change=change), self.assertRaises(ValueError):
                    validate_population(rows, factor)


class NullInputReaderTests(unittest.TestCase):
    def test_h2_complete_input_and_explain_body_preserve_offsets(self):
        sql = "SELECT (A, NULL) IS NULL FROM TEST;"
        for wrapper in (sql, "EXPLAIN " + sql):
            source = "-- source input\n" + wrapper + "\n> output\n"
            selector = embedded(source, "h2", sql, wrapper)
            actual, line, detail = selected_null_input(source, selector)
            self.assertEqual((actual, line), (sql, 2))
            self.assertEqual(detail["source_container"], wrapper)
        source = "> SELECT (A,NULL) IS NULL;\n"
        with self.assertRaises(ValueError):
            selected_null_input(source, embedded(source, "h2", source[2:].rstrip()))

    def test_h2_comment_wrapper_fragment_and_unrecognized_control_fail(self):
        sql = "SELECT 1 ISNULL;"
        for source, container in (
            ("/*\n" + sql + "\n> result\n*/", sql),
            ("SET MODE PostgreSQL;\n" + sql + "\n> result\n", sql),
            ("EXPLAIN ANALYZE " + sql + "\n> result\n", "EXPLAIN ANALYZE " + sql),
            ("EXPLAIN " + sql + " SELECT 2;\n> result\n", "EXPLAIN " + sql + " SELECT 2;"),
        ):
            with self.subTest(source=source), self.assertRaises(ValueError):
                selected_null_input(source, embedded(source, "h2", sql, container))

    def test_plain_host_input_literals_are_distinct_from_expected_results(self):
        sql = "SELECT NULL NOTNULL"
        for context, source in (
            ("python", 'self.validate_identity("' + sql + '")'),
            ("rust", 'verified_only_select_with_canonical("' + sql + '", "expected");'),
            ("java", 'String sqlStr = "' + sql + '";'),
        ):
            selector = embedded(source, context, sql, '"' + sql + '"')
            self.assertEqual(selected_null_input(source, selector)[0], sql)
        for context, source in (
            ("python", 'self.validate_identity("SELECT 1", "' + sql + '")'),
            ("python", 'self.validate_identity("' + sql + '" + suffix)'),
            ("python", '# self.validate_identity("' + sql + '")'),
            ("rust", 'verified_only_select_with_canonical("SELECT 1", "' + sql + '");'),
            ("rust", '// verified_only_select_with_canonical("' + sql + '", "expected");'),
            ("java", 'String expected = "' + sql + '";'),
            ("java", 'String sqlStr = "' + sql + '" + suffix;'),
        ):
            with self.subTest(context=context, source=source), self.assertRaises(ValueError):
                selected_null_input(source, embedded(source, context, sql, '"' + sql + '"'))

    def test_boolean_offsets_and_partial_tokens_are_rejected(self):
        source = 'String sqlStr = "SELECT NULL NOTNULL";'
        selector = embedded(source, "java", "SELECT NULL NOTNULL", '"SELECT NULL NOTNULL"')
        for key in ("start", "end", "container_start", "container_end"):
            changed = deepcopy(selector)
            changed[key] = True
            with self.subTest(key=key), self.assertRaises(ValueError):
                selected_null_input(source, changed)
        selector["start"] += 1
        with self.assertRaises(ValueError):
            selected_null_input(source, selector)

    def test_turso_complete_test_body_never_selects_expect_block(self):
        sql = "select null isnull;\n"
        container = "test isnull {\n" + sql + "}"
        source = container + "\nexpect {\nTRUE\n}\n"
        self.assertEqual(selected_null_input(source, embedded(source, "turso", sql, container))[0], sql)
        for changed in (source.replace("test isnull", "expect"), source.replace("expect {", "execute {"),
                        source.replace("test isnull", "test unrelated")):
            with self.subTest(source=changed), self.assertRaises(ValueError):
                selected_null_input(changed, embedded(changed, "turso", sql, changed[:changed.index("}") + 1]))

    def test_calcite_requires_pinned_input_marker_and_result_boundary(self):
        sql = "SELECT ROW(1,NULL) IS NULL;"
        source = "# [CALCITE-3627] Null check if all fields of ROW are null\n" + sql + "\n+---+\n"
        self.assertEqual(selected_null_input(source, embedded(source, "calcite", sql))[0], sql)
        for changed in (source.replace("CALCITE-3627", "CALCITE-0"), source.replace("\n+---", "\nSELECT")):
            with self.assertRaises(ValueError):
                selected_null_input(changed, embedded(changed, "calcite", sql))

    def test_materialize_directives_are_factor_scoped_and_not_selected_conditions(self):
        prefix = "mode cockroach\nsubtest rows\nonlyif cockroach\nquery B\nSELECT 0\n----\ntrue\n\n"
        sql = "SELECT (1,2) IS NULL\n"
        source = prefix + "query B\n" + sql + "----\nfalse\n"
        start = source.index(sql)
        selector = dict(kind="cockroach_sqllogic_query", start=start, end=start + len(sql),
                        header_line=source[:start].count("\n"))
        self.assertEqual(selected_cockroach_sql(source, selector, null_predicates=True)[0], sql)
        with self.assertRaises(ValueError):
            selected_cockroach_sql(source, selector)
        for directive in ("onlyif cockroach\n", "onlyif postgres\n", "subtest x; shell\n"):
            changed = source[:start - 8] + directive + source[start - 8:]
            new_start = changed.index(sql)
            selection = dict(selector, start=new_start, end=new_start + len(sql),
                             header_line=changed[:new_start].count("\n"))
            with self.subTest(directive=directive), self.assertRaises(ValueError):
                selected_cockroach_sql(changed, selection, null_predicates=True)


class NullSourceObserverTests(unittest.TestCase):
    def test_postfix_and_flat_empty_rows_are_new_but_scalar_long_form_is_not(self):
        for sql in ("SELECT NULL ISNULL", "SELECT 'é' ISNULL"):
            result = observe_null_predicates(null_tree(sql), sql, "null_predicates")
            self.assertEqual(result["null_predicates"][0]["form"], "isnull")
        sql = "SELECT ROW() IS NULL"
        result = observe_null_predicates(null_tree(sql, {"RowExpr": {"args": []}}), sql, "null_predicates")
        self.assertEqual(result["null_predicates"][0]["row_arity"], 0)
        with self.assertRaises(ValueError):
            observe_null_predicates(null_tree("SELECT NULL IS NULL"), "SELECT NULL IS NULL", "null_predicates")

    def test_nested_record_is_observed_without_claiming_a_complete_contract(self):
        sql = "SELECT ROW(ROW(NULL)) IS NULL"
        tree = null_tree(sql, {"RowExpr": {"args": [{"RowExpr": {"args": [{"A_Const": {"isnull": True}}]}}]}})
        result = observe_null_predicates(tree, sql, "null_predicates")
        self.assertTrue(result["source_free"])
        self.assertTrue(result["null_predicates"][0]["nested_row"])

    def test_negation_utf8_comments_and_ordinary_function_names_cannot_forge_locations(self):
        sql = "SELECT 'é' NOTNULL"
        result = observe_null_predicates(null_tree(sql, negated=True), sql, "null_predicates")
        for text in ("SELECT 'é' ISNULL ", "SELECT 'é' /*NOTNULL*/", "SELECT 'é' notnull_function()"):
            with self.assertRaises(ValueError):
                validate_null_predicates(result, "null_predicates", text)
        bad = deepcopy(result)
        bad["null_predicates"][0]["byte_location"] = len("SELECT '".encode()) + 1
        with self.assertRaises(ValueError):
            validate_null_predicates(bad, "null_predicates", sql)
        with self.assertRaises(ValueError):
            observe_null_predicates(null_tree(sql, negated=False), sql, "null_predicates")

    def test_columns_parameters_and_unselected_helpers_keep_separate_scope(self):
        sql = "SELECT value ISNULL"
        result = observe_null_predicates(null_tree(sql, {"ColumnRef": {}}), sql, "null_predicates")
        self.assertFalse(result["source_free"])
        sql = "SELECT NULL ISNULL WHERE $1"
        tree = null_tree(sql)
        tree["SelectStmt"]["whereClause"] = {"ParamRef": {"number": 1}}
        self.assertFalse(observe_null_predicates(tree, sql, "null_predicates")["source_free"])
        for kind in ("FuncCall", "SubLink", "A_ArrayExpr", "A_Indirection", "WindowDef"):
            tree = null_tree(sql, {kind: {}})
            with self.subTest(kind=kind), self.assertRaises(ValueError):
                observe_null_predicates(tree, sql, "null_predicates")


if __name__ == "__main__":
    unittest.main()
