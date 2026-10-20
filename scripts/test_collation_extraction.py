"""Offline COLLATE source identity, token positions and declaration evidence."""
from collections import Counter
from copy import deepcopy
import json
import unittest

from extract_collation_corpus import (
    ROOT, extract, render, selected_declaration, source_context,
    validate_context, validate_population,
)
from extract_pagination_corpus import comparison_key
from extract_statement_corpus import statement_spans
from observe_collation_source import (
    observe_collations, observe_declaration, validate_observation, written_collation,
)


def location(sql, text, occurrence=0):
    start = -1
    for _ in range(occurrence + 1):
        start = sql.index(text, start + 1)
    return len(sql[:start].encode())


def clause(sql, token, names, argument=None, occurrence=0):
    return {"CollateClause": {
        "location": location(sql, token, occurrence),
        "collname": [{"String": {"sval": n}} for n in names],
        "arg": argument or {"A_Const": {"sval": {"sval": "value"}}},
    }}


def select(*expressions, **fields):
    return {"SelectStmt": {"op": "SETOP_NONE", "targetList": list(expressions), **fields}}


class CollationSourceTests(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        cls.directory = ROOT / "fixtures/collations"
        cls.manifest = json.loads((cls.directory / "concrete_sources.json").read_text())
        cls.rows, cls.context = extract(cls.manifest)

    def test_fifty_originals_and_all_declaration_outputs_reproduce(self):
        self.assertEqual(render(self.rows), (self.directory / "concrete.jsonl").read_text())
        self.assertEqual(self.context, json.loads((self.directory / "declaration_contexts.json").read_text()))
        self.assertEqual(len(self.rows), 50)
        self.assertEqual(Counter(r["source_kind"] for r in self.rows), {"engine-regression": 50})
        for row in self.rows:
            self.assertEqual(row["sql"], row["raw_sql"])
            self.assertEqual(row["transformations"], [])
            self.assertEqual(row["observed_parameter_slots"], [])
            self.assertIsNone(row["parameter_types"])
            self.assertNotIn("parameter_values", row)
            self.assertNotIn("expected_value", row)
            self.assertNotIn("output_columns", row)

    def test_exact_clause_names_positions_and_source_dependency_inventory(self):
        clauses = [c for r in self.rows for c in r["observed_syntax"]["collations"]]
        self.assertEqual(len(clauses), 67)
        self.assertEqual(len({tuple(c["parts"]) for c in clauses}), 26)
        self.assertEqual(Counter(r["observed_syntax"]["source_free"] for r in self.rows), {True: 34, False: 16})
        self.assertTrue(all(len(c["parts"]) == 1 for c in clauses))
        self.assertIn(["ucs_basic"], [c["parts"] for c in clauses])
        self.assertIn("UCS_BASIC", [c["spelling"] for c in clauses])
        self.assertIn(["C"], [c["parts"] for c in clauses])
        for row in self.rows:
            validate_observation(row["observed_syntax"], row["sql"])

    def test_no_duplicates_with_prior_factor_inputs(self):
        normalize = lambda sql: comparison_key(sql).rstrip(";").strip()
        prior = set()
        for path in (ROOT / "fixtures").rglob("concrete.jsonl"):
            if path.parent != self.directory:
                prior.update(normalize(json.loads(line)["sql"]) for line in path.read_text().splitlines())
        self.assertFalse(prior & {normalize(r["sql"]) for r in self.rows})

    def test_catalog_references_never_invent_installed_objects_or_provider_fields(self):
        dependencies = [d for r in self.rows for d in r["declaration_provenance"]["collation_dependencies"]]
        self.assertEqual(Counter(d["origin"] for d in dependencies),
                         {"written-create-collation": 24, "unresolved-catalog-reference": 41})
        by_id = {d["id"]: d for d in self.context["declarations"]}
        for dependency in dependencies:
            self.assertEqual(set(dependency), {"parts", "uses", "declaration_id", "origin",
                                               "runtime_catalog_resolution"})
            self.assertEqual(dependency["runtime_catalog_resolution"], "not-performed")
            if dependency["declaration_id"] is None:
                self.assertEqual(dependency["origin"], "unresolved-catalog-reference")
            else:
                declaration = by_id[dependency["declaration_id"]]["observed_declaration"]
                self.assertEqual(declaration["kind"], "collation")
                self.assertEqual(declaration["name"], dependency["parts"])
        # Bootstrap and imported locale names are references, not inventions
        # of object OIDs/provider flags based solely on spelling.
        self.assertTrue(all(d["declaration_id"] is None for d in dependencies
                            if d["parts"] in [["C"], ["POSIX"], ["en-x-icu"], ["en_US"]]))

    def test_written_fields_keep_omissions_and_arrays_without_inferred_defaults(self):
        declarations = self.context["declarations"]
        self.assertEqual(Counter(d["observed_declaration"]["kind"] for d in declarations),
                         {"collation": 14, "table": 8, "schema": 3, "search_path": 3})
        table = next(d["observed_declaration"] for d in declarations
                     if d["observed_declaration"].get("name") == ["test6a"])
        self.assertEqual(table["columns"][1], {
            "name": "b", "raw_type_name": ["text"], "written_array_bounds": [-1],
            "written_not_null": False, "written_collation": None,
        })
        sensitive = next(d["observed_declaration"] for d in declarations
                         if d["observed_declaration"].get("name") == ["case_sensitive"])
        self.assertEqual(sensitive["written_options"],
                         [{"name": "provider", "value": "icu"}, {"name": "locale", "value": ""}])
        nondet = next(d["observed_declaration"] for d in declarations
                      if d["observed_declaration"].get("name") == ["ctest_nondet"])
        self.assertIn({"name": "deterministic", "value": "false"}, nondet["written_options"])
        self.assertTrue(all(d["execution"] == "not-performed" for d in declarations))

    def test_environment_preambles_and_source_search_path_are_retained_not_evaluated(self):
        preambles = self.context["preambles"]
        self.assertEqual(len(preambles), 3)
        self.assertEqual(sum("\\if :skip_test" in p["text"] for p in preambles), 2)
        self.assertEqual(sum("SET client_encoding TO UTF8;" in p["text"] for p in preambles), 2)
        self.assertTrue(all(p["execution"] == "not-performed" for p in preambles))
        for row in self.rows:
            provenance = row["declaration_provenance"]
            self.assertEqual(len(provenance["session_declaration_ids"]), 2)
            self.assertEqual(provenance, source_context(row, self.context["declarations"]))

    def test_hash_statement_and_context_mutations_fail_closed(self):
        mutations = [
            lambda m: m["sources"]["postgres"].update(commit="0" * 40),
            lambda m: m["sources"]["postgres"].update(license_sha256="0" * 64),
            lambda m: m["sources"]["postgres"]["files"][0].update(sha256="0" * 64),
            lambda m: m["selections"][0].update(sql_sha256="0" * 64),
            lambda m: m["selections"][0]["selector"].update(start=2438),
            lambda m: m["preambles"][0].update(sha256="0" * 64),
            lambda m: m["declaration_contexts"][0]["observed_declaration"].update(name="invented_schema"),
            lambda m: m["declaration_contexts"].pop(),
        ]
        for mutate in mutations:
            bad = deepcopy(self.manifest)
            mutate(bad)
            with self.subTest(mutate=mutate), self.assertRaises(ValueError):
                extract(bad)
        bad = deepcopy(self.context)
        entry = next(d for d in bad["declarations"] if d["observed_declaration"]["kind"] == "collation")
        entry["observed_declaration"]["written_options"][0]["value"] = "invented-provider"
        with self.assertRaises(ValueError):
            validate_context(bad)

    def test_query_provenance_mutations_do_not_pass_on_unchanged_sql(self):
        for field, value in (("origin", "installed"), ("provider", "icu"), ("oid", 12345),
                             ("runtime_catalog_resolution", "resolved")):
            bad = deepcopy(self.rows)
            bad[0]["declaration_provenance"]["collation_dependencies"][0][field] = value
            with self.subTest(field=field), self.assertRaises(ValueError):
                validate_population(bad, self.context["declarations"])
        bad = deepcopy(self.rows)
        bad[-1]["declaration_provenance"]["relation_declarations"] = []
        with self.assertRaises(ValueError):
            validate_population(bad, self.context["declarations"])

    def test_quoted_dot_is_one_component_and_schema_path_is_two(self):
        sql = 'SELECT \'é\' COLLATE "Odd.Name", \'z\' COLLATE "S".plain;'
        tree = select(clause(sql, "COLLATE", ["Odd.Name"]),
                      clause(sql, "COLLATE", ["S", "plain"], occurrence=1))
        value = observe_collations(tree, sql)
        self.assertEqual([c["parts"] for c in value["collations"]], [["Odd.Name"], ["S", "plain"]])
        self.assertEqual([c["quoted"] for c in value["collations"]], [[True], [True, False]])
        self.assertTrue(value["source_free"])
        bad = deepcopy(value)
        bad["collations"][0]["quoted"] = [1]
        with self.assertRaises(ValueError):
            validate_observation(bad, sql)

    def test_collate_comments_unicode_and_keyword_positions_are_checked(self):
        sql = 'SELECT \'é\' CoLlAtE /* one /* nested */ */ "a""b";'
        value = observe_collations(select(clause(sql, "CoLlAtE", ['a"b'])), sql)
        self.assertEqual(value["collations"][0]["parts"], ['a"b'])
        self.assertGreater(value["collations"][0]["byte_location"], sql.index("CoLlAtE"))
        for bad_location in (True, location(sql, "é") + 1, len(sql.encode()) + 1):
            with self.subTest(location=bad_location), self.assertRaises(ValueError):
                written_collation(sql, bad_location)
        masked = 'SELECT \'COLLATE "C"\', 1;'
        with self.assertRaises(ValueError):
            written_collation(masked, location(masked, "COLLATE"))
        with self.assertRaises(ValueError):
            written_collation('SELECT \'x\' COLLATE /* open', len("SELECT 'x' ".encode()))

    def test_raw_name_or_argument_disagreement_is_rejected(self):
        sql = 'SELECT \'x\' COLLATE "C";'
        with self.assertRaises(ValueError):
            observe_collations(select(clause(sql, "COLLATE", ["POSIX"])), sql)
        tree = select(clause(sql, "COLLATE", ["C"], {"TypeCast": {}}))
        with self.assertRaises(ValueError):
            observe_collations(tree, sql)
        value = observe_collations(select(clause(sql, "COLLATE", ["C"])), sql)
        value["collations"].append(deepcopy(value["collations"][0]))
        with self.assertRaises(ValueError):
            validate_observation(value, sql)

    def test_relation_occurrence_controls_source_free_not_collation_presence(self):
        sql = 'SELECT b COLLATE "C" FROM qa.t;'
        relation = {"RangeVar": {"relname": "t", "schemaname": "qa",
                                 "location": location(sql, "qa.t")}}
        tree = select(clause(sql, "COLLATE", ["C"], {"ColumnRef": {}}), fromClause=[relation])
        value = observe_collations(tree, sql)
        self.assertFalse(value["source_free"])
        self.assertEqual(value["relations"][0]["parts"], ["qa", "t"])
        bad = deepcopy(value)
        bad["source_free"] = True
        with self.assertRaises(ValueError):
            validate_observation(bad, sql)

    def test_unselected_syntax_dependencies_are_not_silently_filtered(self):
        sql = 'SELECT \'x\' COLLATE "C";'
        for dependency in ("FuncCall", "ParamRef", "SubLink", "RangeSubselect"):
            tree = select(clause(sql, "COLLATE", ["C"]), **{"whereClause": {dependency: {}}})
            with self.subTest(dependency=dependency), self.assertRaises(ValueError):
                observe_collations(tree, sql)
        for field in ("valuesLists", "withClause", "groupClause", "distinctClause"):
            with self.subTest(field=field), self.assertRaises(ValueError):
                observe_collations(select(clause(sql, "COLLATE", ["C"]), **{field: [{}]}), sql)

    def test_declaration_option_observer_keeps_literal_booleans_and_rejects_expressions(self):
        node = {"DefineStmt": {"kind": "OBJECT_COLLATION",
                "defnames": [{"String": {"sval": "custom"}}],
                "definition": [{"DefElem": {"defname": "deterministic",
                                "arg": {"Boolean": {"boolval": False}}}}]}}
        self.assertEqual(observe_declaration(node)["written_options"],
                         [{"name": "deterministic", "value": False}])
        node["DefineStmt"]["definition"][0]["DefElem"]["arg"] = {"FuncCall": {}}
        with self.assertRaises(ValueError):
            observe_declaration(node)
        node = {"CreateStmt": {"relation": {"relname": "t"},
                              "tableElts": [{"ColumnDef": {"colname": "x",
                              "typeName": {"names": [{"String": {"sval": "text"}}]},
                              "constraints": [{"Constraint": {"contype": "CONSTR_DEFAULT"}}]}}]}}
        with self.assertRaises(ValueError):
            observe_declaration(node)

    def test_psql_describe_container_preserves_prefix_and_whole_create_body(self):
        source = "\\d collate_test_like\n\nCREATE TABLE collate_test2 (b text COLLATE \"C\");"
        spans = statement_spans(source)
        selector = {"kind": "psql_describe_then_declaration", "container_start": 0,
                    "start": source.index("CREATE"), "end": len(source), "statement_index": 0}
        sql, line, detail = selected_declaration(source, selector, spans)
        self.assertEqual(line, 3)
        self.assertEqual(sql, source[selector["start"]:])
        self.assertEqual(detail["source_prefix"], "\\d collate_test_like\n\n")
        self.assertEqual(sum("source_prefix" in d for d in self.context["declarations"]), 1)
        for prefix in ("\\include arbitrary\n\n", "\\d other\n\n",
                       "\\d collate_test_like\nSELECT 1;\n"):
            changed = prefix + sql
            bad = {**selector, "start": len(prefix), "end": len(changed)}
            with self.subTest(prefix=prefix), self.assertRaises(ValueError):
                selected_declaration(changed, bad, statement_spans(changed))
        for key in ("start", "end", "container_start"):
            bad = {**selector, key: selector[key] + 1}
            with self.subTest(key=key), self.assertRaises(ValueError):
                selected_declaration(source, bad, spans)


if __name__ == "__main__":
    unittest.main()
