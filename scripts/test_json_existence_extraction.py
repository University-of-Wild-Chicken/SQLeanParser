"""Reproducible unchanged JSONB existence sources and their finite observer."""
from collections import Counter
from copy import deepcopy
import json
import unittest

from extract_cockroach_sqllogic_sql import selected_cockroach_sql
from extract_factor_corpus import ROOT, extract, render, validate_population
from extract_pagination_corpus import comparison_key
from observe_json_existence_source import observe_json_existence, validate_json_existence


def literal(value="{}"):
    return {"A_Const": {"isnull": True} if value is None else {"sval": {"sval": value}}}


def cast(value=None, name="jsonb", array=False):
    type_name = {"names": [{"String": {"sval": name}}]}
    if array:
        type_name["arrayBounds"] = [{"Integer": {"ival": -1}}]
    return {"TypeCast": {"arg": literal() if value is None else value, "typeName": type_name}}


SQL = "SELECT '{}'::jsonb ? 'a';"


def predicate(sql=SQL, operator="?", left=None, right=None):
    return {"A_Expr": {"kind": "AEXPR_OP", "name": [{"String": {"sval": operator}}],
                       "lexpr": cast() if left is None else left,
                       "rexpr": literal("a") if right is None else right,
                       "location": len(sql[:sql.index("?")].encode())}}


def query(value=None, table=None):
    result = {"targetList": [{"ResTarget": {"val": predicate() if value is None else value}}]}
    if table:
        result["fromClause"] = [{"RangeVar": {"relname": table}}]
    return {"SelectStmt": result}


class JsonExistenceExtractionTests(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        cls.directory = ROOT / "fixtures/json_existence"
        cls.manifest = json.loads((cls.directory / "concrete_sources.json").read_text())
        cls.rows = extract(cls.manifest, "json_existence")

    def test_fifty_whole_sources_reproduce_with_pinned_origins_and_no_invented_catalog(self):
        self.assertEqual(render(self.rows), (self.directory / "concrete.jsonl").read_text())
        self.assertEqual(Counter(row["source"] for row in self.rows),
                         {"postgres": 27, "cockroach": 14, "materialize": 8, "river": 1})
        self.assertEqual(len({comparison_key(row["sql"]) for row in self.rows}), 50)
        for row in self.rows:
            self.assertEqual(row["raw_sql"], row["sql"])
            self.assertEqual(row["transformations"], [])
            self.assertIsNone(row["parameter_types"])
            self.assertEqual(row["application_schema_validity"], "not-claimed")
            self.assertEqual(row["observed_syntax"]["function_names"], [])
            self.assertEqual(row["observed_syntax"]["conditional_forms"], [])
            for field in ("expected_value", "output_columns", "parameter_values"):
                self.assertNotIn(field, row)

    def test_fixed_operators_source_scopes_and_literal_nulls_remain_explicit(self):
        entries = [entry for row in self.rows for entry in row["observed_syntax"]["json_existence"]]
        self.assertEqual(len(entries), 56)
        self.assertEqual(Counter(entry["operator"] for entry in entries), {"?": 33, "?|": 11, "?&": 12})
        self.assertEqual(Counter(row["observed_syntax"]["source_free"] for row in self.rows),
                         {True: 44, False: 6})
        self.assertEqual(Counter(entry["left_form"] for entry in entries),
                         {"TypeCast": 50, "ColumnRef": 4, "A_Expr": 2})
        self.assertEqual(Counter(entry["right_cast"] for entry in entries),
                         {None: 53, "text": 1, "text[]": 2})
        nullable = [row for row in self.rows if any(
            entry["left_literal_null"] for entry in row["observed_syntax"]["json_existence"])]
        self.assertEqual([(row["source"], row["header_line"]) for row in nullable],
                         [("materialize", 663), ("materialize", 668)])
        self.assertEqual(sum(len(row["observed_syntax"]["json_existence"]) == 2 for row in self.rows), 6)

    def test_river_constant_retains_template_comment_and_original_parameter_slot(self):
        row = next(row for row in self.rows if row["source"] == "river")
        self.assertEqual(row["symbol"], "jobGetCancelRequested")
        self.assertEqual(row["source_kind"], "application-constant")
        self.assertEqual(row["license"], "MPL-2.0")
        self.assertIn("FROM /* TEMPLATE: schema */river_job", row["sql"])
        self.assertIn("id = any($1::bigint[])", row["sql"])
        self.assertIn("metadata ? 'cancel_attempted_at'", row["sql"])
        self.assertEqual(row["observed_parameter_slots"], [1])
        self.assertTrue(all(other["observed_parameter_slots"] == []
                            for other in self.rows if other["source"] != "river"))
        self.assertFalse(row["observed_syntax"]["source_free"])

    def test_manifest_rejects_wrong_hashes_license_selectors_and_closed_source_counts(self):
        for mutation in ("source_hash", "license_hash", "sql_hash", "selector", "count", "origins", "pin"):
            manifest = deepcopy(self.manifest)
            if mutation == "source_hash":
                manifest["sources"]["postgres"]["files"][0]["sha256"] = "0" * 64
            elif mutation == "license_hash":
                manifest["sources"]["river"]["license_sha256"] = "0" * 64
            elif mutation == "sql_hash":
                manifest["selections"][0]["sql_sha256"] = "0" * 64
            elif mutation == "selector":
                selection = next(row for row in manifest["selections"] if row["source"] == "cockroach")
                selection["selector"]["end"] -= 1
            elif mutation == "count":
                manifest["selections"].pop()
            elif mutation == "origins":
                manifest["expected_sources"]["postgres"] += 1
            else:
                manifest["sources"]["postgres"]["commit"] = "main"
            with self.subTest(mutation=mutation), self.assertRaises(ValueError):
                extract(manifest, "json_existence")

    def test_population_rejects_changed_scope_nodes_duplicate_source_and_binding_claims(self):
        for mutation in ("operator", "scope", "null", "duplicate", "raw", "types", "slot", "fields"):
            rows = deepcopy(self.rows)
            row = rows[0]
            entry = row["observed_syntax"]["json_existence"][0]
            if mutation == "operator":
                entry["operator"] = "?&"
            elif mutation == "scope":
                row["observed_syntax"]["source_free"] = False
            elif mutation == "null":
                entry["left_literal_null"] = True
            elif mutation == "duplicate":
                rows[-1] = rows[0]
            elif mutation == "raw":
                row["raw_sql"] += " "
            elif mutation == "types":
                row["parameter_types"] = ""
            elif mutation == "slot":
                row["observed_parameter_slots"] = [1]
            else:
                entry["inferred_type"] = "jsonb"
            with self.subTest(mutation=mutation), self.assertRaises(ValueError):
                validate_population(rows, "json_existence")

    def test_observer_preserves_explicit_casts_without_assigning_table_column_types(self):
        observation = observe_json_existence(query(), SQL)
        self.assertEqual(observation, {"source_free": True, "json_existence": [
            {"operator": "?", "left_form": "TypeCast", "left_cast": "jsonb", "left_literal_null": False,
             "right_form": "A_Const", "right_cast": None}]})
        column = {"ColumnRef": {"fields": [{"String": {"sval": "document"}}]}}
        table = observe_json_existence(query(predicate(left=column), table="documents"), SQL)
        self.assertFalse(table["source_free"])
        self.assertIsNone(table["json_existence"][0]["left_cast"])
        with self.assertRaisesRegex(ValueError, "source-free"):
            observe_json_existence(query(predicate(left=column)), SQL)

    def test_sql_null_is_distinct_from_json_null_and_null_array_members(self):
        for document, outer_null in ((None, True), ("null", False), ('{"key":null}', False)):
            observed = observe_json_existence(query(predicate(left=cast(literal(document)))), SQL)
            self.assertIs(observed["json_existence"][0]["left_literal_null"], outer_null)
        sql = "SELECT '{}'::jsonb ?| ARRAY[NULL,'a'];"
        value = predicate(sql, "?|", right={"A_ArrayExpr": {"elements": [literal(None), literal("a")]}})
        observed = observe_json_existence(query(value), sql)
        self.assertIs(observed["json_existence"][0]["left_literal_null"], False)

    def test_wrong_document_types_arrays_and_malformed_json_are_not_selected(self):
        for left in (cast(name="json"), cast(name="text"), cast(array=True),
                     cast(literal("{bad}")), cast(literal("NaN")), cast(literal("Infinity"))):
            with self.subTest(left=left), self.assertRaises(ValueError):
                observe_json_existence(query(predicate(left=left)), SQL)
        for modifier in ("typmods", "setof", "pct_type"):
            value = predicate()
            value["A_Expr"]["lexpr"]["TypeCast"]["typeName"][modifier] = [1]
            with self.subTest(modifier=modifier), self.assertRaises(ValueError):
                observe_json_existence(query(value), SQL)

    def test_key_shape_type_and_nonempty_constructor_are_checked(self):
        sql = "SELECT '{}'::jsonb ?| ARRAY['a'];"
        for right in (literal("a"), cast(literal("{}"), "jsonb"),
                      {"A_ArrayExpr": {}}, {"A_ArrayExpr": {"elements": [cast(literal("a"), "text")]}}):
            with self.subTest(right=right), self.assertRaises(ValueError):
                observe_json_existence(query(predicate(sql, "?|", right=right)), sql)
        text_array = cast(literal("{}"), "text", array=True)
        observed = observe_json_existence(query(predicate(sql, "?|", right=text_array)), sql)
        self.assertEqual(observed["json_existence"][0]["right_cast"], "text[]")
        with self.assertRaises(ValueError):
            observe_json_existence(query(predicate(right=text_array)), SQL)

    def test_source_position_is_utf8_aligned_and_cannot_point_into_a_literal_or_comment(self):
        sql = """SELECT '"é"'::jsonb /* ? */ ? 'x';"""
        value = predicate(sql, left=cast(literal('"é"')))
        value["A_Expr"]["location"] = len(sql[:sql.rindex("?")].encode())
        self.assertEqual(observe_json_existence(query(value), sql)["json_existence"][0]["operator"], "?")
        positions = [len(sql[:sql.index("?")].encode()), len(sql[:sql.index("é")].encode()) + 1, -1, True]
        for position in positions:
            invalid = deepcopy(value)
            invalid["A_Expr"]["location"] = position
            with self.subTest(position=position), self.assertRaises(ValueError):
                observe_json_existence(query(invalid), sql)
        for spelling in ("?|", "?&", "@?", "??"):
            changed_sql = SQL.replace(" ? ", " " + spelling + " ")
            value = predicate(changed_sql)
            with self.subTest(spelling=spelling), self.assertRaisesRegex(ValueError, "spelling"):
                observe_json_existence(query(value), changed_sql)

    def test_qualified_operators_hidden_dependencies_and_nonpredicate_projection_are_excluded(self):
        value = predicate()
        value["A_Expr"]["name"].insert(0, {"String": {"sval": "custom"}})
        with self.assertRaisesRegex(ValueError, "qualified operators"):
            observe_json_existence(query(value), SQL)
        for kind in ("SubLink", "RowExpr", "A_Indirection", "RangeSubselect", "CollateClause", "ParamRef"):
            tree = query()
            tree["SelectStmt"]["targetList"].append({"ResTarget": {"val": {kind: {}}}})
            with self.subTest(kind=kind), self.assertRaises(ValueError):
                observe_json_existence(tree, SQL)
        tree = query()
        tree["SelectStmt"]["targetList"].append({"ResTarget": {"val": literal("extra")}})
        with self.assertRaisesRegex(ValueError, "projection"):
            observe_json_existence(tree, SQL)
        for clause in ("withClause", "larg", "valuesLists", "groupClause", "lockingClause"):
            tree = query()
            tree["SelectStmt"][clause] = [{"present": True}]
            with self.subTest(clause=clause), self.assertRaises(ValueError):
                observe_json_existence(tree, SQL)

    def test_metadata_validation_requires_exact_booleans_and_never_infers_casts(self):
        original = observe_json_existence(query(), SQL)
        for field, value in (("source_free", 1), ("left_literal_null", 0),
                             ("left_cast", None), ("right_cast", "text"), ("operator", "custom.?")):
            observation = deepcopy(original)
            target = observation if field == "source_free" else observation["json_existence"][0]
            target[field] = value
            with self.subTest(field=field), self.assertRaises(ValueError):
                validate_json_existence(observation)

    def test_boolean_header_extension_is_explicit_and_preserves_complete_source_bytes(self):
        for header in ("query B", "query BB"):
            source = "mode cockroach\r\n\r\n" + header + "\r\n" + SQL + "\r\n----\r\nopaque\r\n\r\n"
            start = source.index(SQL)
            selector = {"kind": "cockroach_sqllogic_query", "header_line": 3,
                        "start": start, "end": start + len(SQL) + 2}
            with self.subTest(header=header), self.assertRaises(ValueError):
                selected_cockroach_sql(source, selector)
            sql, line, detail = selected_cockroach_sql(source, selector, boolean_queries=True)
            self.assertEqual((sql, line, detail["query_header"]), (SQL + "\r\n", 4, header))
            changed = {**selector, "end": selector["end"] - 1}
            with self.assertRaises(ValueError):
                selected_cockroach_sql(source, changed, boolean_queries=True)
        source = "query T\n" + SQL + "\n----\ntrue\n\n"
        selector = {"kind": "cockroach_sqllogic_query", "header_line": 1,
                    "start": len("query T\n"), "end": source.index("----")}
        self.assertEqual(selected_cockroach_sql(source, selector)[0], SQL + "\n")
        with self.assertRaises(ValueError):
            selected_cockroach_sql(source, selector, boolean_queries=True)

    def test_boolean_selection_does_not_accept_guards_scripts_or_other_factor_inputs(self):
        for prefix in ("onlyif cockroach\n", "skipif sqlite\n", "system echo unsafe\n"):
            source = prefix + "query B\n" + SQL + "\n----\ntrue\n\n"
            selector = {"kind": "cockroach_sqllogic_query", "header_line": 2,
                        "start": source.index(SQL), "end": source.index("----")}
            with self.subTest(prefix=prefix), self.assertRaises(ValueError):
                selected_cockroach_sql(source, selector, boolean_queries=True)
        manifest = deepcopy(self.manifest)
        manifest["factor"] = "substring"
        with self.assertRaises(ValueError):
            extract(manifest, "json_existence")


if __name__ == "__main__":
    unittest.main()
