"""Source component identity and the catalog-dependent qualification corpus."""
from collections import Counter
from copy import deepcopy
import json
import unittest

from extract_factor_corpus import ROOT, extract, render, validate_population
from observe_qualified_name_source import observe_qualified_names, source_name, validate_qualified_names


def query(sql="SELECT * FROM s.t", schema="s", relation="t"):
    location = len(sql[:sql.index("FROM") + 5].encode())
    return {"SelectStmt": {"fromClause": [{"RangeVar": {
        "schemaname": schema, "relname": relation, "location": location,
        "inh": True, "relpersistence": "p"}}]}}


class QualifiedNameExtractionTests(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        cls.directory = ROOT / "fixtures/qualified_names"
        cls.manifest = json.loads((cls.directory / "concrete_sources.json").read_text())
        cls.records = extract(cls.manifest, "qualified_names")

    def test_fifty_originals_reproduce_without_invented_catalog_or_bindings(self):
        self.assertEqual(render(self.records), (self.directory / "concrete.jsonl").read_text())
        self.assertEqual(Counter(row["source"] for row in self.records),
                         {"postgres": 37, "sqlc": 12, "hatchet": 1})
        self.assertEqual(len({row["sql"] for row in self.records}), 50)
        for row in self.records:
            self.assertEqual(row["raw_sql"], row["sql"])
            self.assertEqual(row["transformations"], [])
            self.assertIsNone(row["parameter_types"])
            self.assertEqual(row["application_schema_validity"], "not-claimed")
            self.assertIs(row["observed_syntax"]["source_free"], False)
            for field in ("catalog", "schema", "namespace", "expected_value", "output_columns", "parameter_values"):
                self.assertNotIn(field, row)

    def test_fixed_component_alias_quoting_and_parameter_inventory(self):
        obs = [row["observed_syntax"] for row in self.records]
        self.assertEqual(sum(len(o["qualified_relations"]) for o in obs), 58)
        self.assertEqual(sum(any(r["alias"] is not None for r in o["qualified_relations"]) for o in obs), 9)
        self.assertEqual(sum(any(any(r["quoted"]) for r in o["qualified_relations"]) for o in obs), 4)
        self.assertEqual(Counter(len(c["parts"]) for o in obs for c in o["qualified_columns"]), {2: 36, 3: 4})
        self.assertEqual(sum(bool(row["observed_parameter_slots"]) for row in self.records), 7)
        self.assertFalse(any("." in part for o in obs for r in o["qualified_relations"] for part in r["parts"]))
        app = next(row for row in self.records if row["source"] == "hatchet")
        self.assertEqual(app["symbol"], "ensureTablePartitionsExist")
        self.assertEqual(app["source_kind"], "application-constant")
        self.assertTrue(app["sql"].startswith("-- name: EnsureTablePartitionsExist"))

    def test_quoted_dots_are_components_not_separators(self):
        names = ['"a.b".c', 'a."b.c"', '"a.b.c"']
        observed = [source_name(sql, 0) for sql in names]
        self.assertEqual([item["parts"] for item in observed], [["a.b", "c"], ["a", "b.c"], ["a.b.c"]])
        self.assertEqual([item["quoted"] for item in observed], [[True, False], [False, True], [True]])
        self.assertEqual(len({".".join(item["parts"]) for item in observed}), 1)
        self.assertEqual([item["spelling"] for item in observed], names)
        first = observe_qualified_names(query("SELECT * FROM \"a.b\".c", "a.b", "c"), 'SELECT * FROM "a.b".c')
        second = observe_qualified_names(query('SELECT * FROM a."b.c"', "a", "b.c"), 'SELECT * FROM a."b.c"')
        self.assertNotEqual(first["qualified_relations"][0]["parts"], second["qualified_relations"][0]["parts"])

    def test_case_escaped_quotes_and_literal_wildcard_identity_are_retained(self):
        self.assertEqual(source_name('PuBlic."T""Name"', 0),
                         {"parts": ["public", 'T"Name'], "quoted": [False, True], "spelling": 'PuBlic."T""Name"'})
        self.assertEqual(source_name('s.*', 0)["quoted"], [False, False])
        self.assertEqual(source_name('s."*"', 0)["quoted"], [False, True])
        for spelling in ('s."*"', '"*".t'):
            entry = {**source_name(spelling, 0), "alias": None, "column_aliases": []}
            validate_qualified_names({"source_free": False, "qualified_relations": [entry], "qualified_columns": []})

    def test_utf8_offsets_and_nested_comments_around_dots(self):
        sql = '/* λ */ SELECT * FROM "é" /* outer /* nested */ end */ . -- next\n "表"'
        start = sql.index('"é"')
        observed = source_name(sql, len(sql[:start].encode()))
        self.assertEqual(observed["parts"], ["é", "表"])
        self.assertEqual(observed["spelling"], sql[start:])
        self.assertEqual(observed["quoted"], [True, True])
        with self.assertRaises(ValueError):
            source_name(sql, 4)
        with self.assertRaises(ValueError):
            source_name("s /* unfinished", 0)

    def test_multipart_column_path_is_observed_without_resolving_it(self):
        sql = "SELECT s.t.c FROM s.t AS x"
        parsed = query(sql)
        parsed["SelectStmt"]["fromClause"][0]["RangeVar"]["alias"] = {"aliasname": "x"}
        parsed["SelectStmt"]["targetList"] = [{"ResTarget": {"val": {"ColumnRef": {
            "fields": [{"String": {"sval": part}} for part in ("s", "t", "c")], "location": 7}}}}]
        observed = observe_qualified_names(parsed, sql)
        self.assertEqual(observed["qualified_relations"][0]["alias"], "x")
        self.assertEqual(observed["qualified_columns"][0]["parts"], ["s", "t", "c"])
        # Alias masking is a namespace-validity question, deliberately not inferred here.

    def test_database_qualification_more_than_three_column_parts_and_only_are_excluded(self):
        for mutation in ("database", "column", "only", "column_alias"):
            sql = "SELECT * FROM s.t"
            parsed = query(sql)
            relation = parsed["SelectStmt"]["fromClause"][0]["RangeVar"]
            if mutation == "database":
                relation["catalogname"] = "db"
            elif mutation == "column":
                parsed["SelectStmt"]["targetList"] = [{"ResTarget": {"val": {"ColumnRef": {
                    "fields": [{"String": {"sval": part}} for part in ("db", "s", "t", "c")],
                    "location": 7}}}}]
            elif mutation == "only":
                relation["inh"] = False
            else:
                relation["alias"] = {"aliasname": "x", "colnames": [{"String": {"sval": "c"}}]}
            with self.subTest(mutation=mutation), self.assertRaises(ValueError):
                observe_qualified_names(parsed, sql)

    def test_scope_and_source_location_cannot_be_fabricated(self):
        for mutation in ("schema", "relation", "location", "unqualified", "statement"):
            parsed = query()
            relation = parsed["SelectStmt"]["fromClause"][0]["RangeVar"]
            if mutation in {"schema", "relation"}:
                relation[{"schema": "schemaname", "relation": "relname"}[mutation]] = "wrong"
            elif mutation == "location":
                relation["location"] = -1
            elif mutation == "unqualified":
                del relation["schemaname"]
            else:
                parsed = {"DeleteStmt": parsed["SelectStmt"]}
            with self.subTest(mutation=mutation), self.assertRaises(ValueError):
                observe_qualified_names(parsed, "SELECT * FROM s.t")

    def test_entry_metadata_requires_relation_fields_exact_bools_and_matching_spelling(self):
        good = observe_qualified_names(query(), "SELECT * FROM s.t")
        for mutation in ("delete_alias", "delete_fields", "empty_alias", "quotes", "spelling", "parts",
                         "extra", "wildcard", "array_alias"):
            observed = deepcopy(good)
            entry = observed["qualified_relations"][0]
            if mutation == "delete_alias":
                del entry["alias"]
            elif mutation == "delete_fields":
                del entry["alias"]
                del entry["column_aliases"]
            elif mutation == "empty_alias":
                entry["alias"] = ""
            elif mutation == "quotes":
                entry["quoted"][0] = 0
            elif mutation == "spelling":
                entry["spelling"] = '"s"."t"'
            elif mutation == "parts":
                entry["parts"] = ["s.t"]
            elif mutation == "extra":
                entry["resolved_schema"] = "s"
            elif mutation == "wildcard":
                entry.update(source_name("s.*", 0))
            else:
                entry["column_aliases"] = ["c"]
            with self.subTest(mutation=mutation), self.assertRaises(ValueError):
                validate_qualified_names(observed)

    def test_population_rejects_removed_alias_quote_and_multipart_coverage(self):
        for mutation in ("count", "alias", "quote", "column", "scope", "types", "duplicate"):
            rows = deepcopy(self.records)
            if mutation == "count":
                rows.pop()
            elif mutation == "alias":
                row = next(row for row in rows if any(x["alias"] for x in row["observed_syntax"]["qualified_relations"]))
                for entry in row["observed_syntax"]["qualified_relations"]:
                    entry["alias"] = None
            elif mutation == "quote":
                row = next(row for row in rows if any(any(x["quoted"]) for x in row["observed_syntax"]["qualified_relations"]))
                row["observed_syntax"]["qualified_relations"][0]["quoted"] = [False, False]
            elif mutation == "column":
                row = next(row for row in rows if any(len(c["parts"]) == 3 for c in row["observed_syntax"]["qualified_columns"]))
                row["observed_syntax"]["qualified_columns"] = []
            elif mutation == "scope":
                rows[0]["observed_syntax"]["source_free"] = 0
            elif mutation == "types":
                rows[0]["parameter_types"] = "int"
            else:
                rows[1] = deepcopy(rows[0])
            with self.subTest(mutation=mutation), self.assertRaises(ValueError):
                validate_population(rows, "qualified_names")

    def test_exact_selectors_source_hashes_and_licenses_are_mandatory(self):
        for mutation in ("selector", "constant", "sql_hash", "source_hash", "license_hash"):
            manifest = deepcopy(self.manifest)
            if mutation == "selector":
                manifest["selections"][0]["selector"]["end"] -= 1
            elif mutation == "constant":
                row = next(row for row in manifest["selections"] if row["source"] == "hatchet")
                row["selector"]["symbol"] = "missing"
            elif mutation == "sql_hash":
                manifest["selections"][0]["sql_sha256"] = "0" * 64
            elif mutation == "source_hash":
                manifest["sources"]["sqlc"]["files"][0]["sha256"] = "0" * 64
            else:
                manifest["sources"]["hatchet"]["license_sha256"] = "0" * 64
            with self.subTest(mutation=mutation), self.assertRaises(ValueError):
                extract(manifest, "qualified_names")


if __name__ == "__main__":
    unittest.main()
