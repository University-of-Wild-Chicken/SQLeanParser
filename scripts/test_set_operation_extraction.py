"""Pinned source identity, finite reader boundaries, and raw-tree observations."""
from collections import Counter
from copy import deepcopy
import json
import unittest

from extract_set_operation_corpus import (
    DIRECTORY, POPULATIONS, extract, render, validate_population, validate_registry,
)
from extract_setop_sqllogic_sql import selected_setop_sqllogic
from observe_set_operation_source import observe, validate_observation


def select(**fields):
    return {"SelectStmt": {"op": "SETOP_NONE", **fields}}


def compound(operator="UNION", left=None, right=None, **fields):
    return {"SelectStmt": {
        "op": "SETOP_" + operator, "larg": (left or select())["SelectStmt"],
        "rarg": (right or select())["SelectStmt"], **fields,
    }}


def relation(sql, name, occurrence=0):
    start = -1
    for _ in range(occurrence + 1):
        start = sql.index("FROM " + name, start + 1)
    return {"RangeVar": {"relname": name, "location": len(sql[:start + 5].encode())}}


def selector(text, header_line):
    lines = text.splitlines(keepends=True)
    start = sum(map(len, lines[:header_line]))
    end = start
    for line in lines[header_line:]:
        if line.rstrip("\r\n") == "----":
            break
        end += len(line)
    return {"kind": "setop_sqllogic_query", "header_line": header_line, "start": start, "end": end}


class SetSourceTests(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        cls.manifest = json.loads((DIRECTORY / "concrete_sources.json").read_text())
        cls.rows = extract(cls.manifest)
        cls.registry = json.loads((DIRECTORY / "source_contracts.json").read_text())

    def test_exact_150_unchanged_inputs_and_provenance_reproduce(self):
        self.assertEqual(render(self.rows), (DIRECTORY / "concrete.jsonl").read_text())
        self.assertEqual(Counter(r["factor"] for r in self.rows), dict.fromkeys(POPULATIONS, 50))
        self.assertEqual(Counter(r["source_kind"] for r in self.rows),
                         {"engine-regression": 148, "compiler-regression": 2})
        self.assertEqual(sum(bool(r.get("source_condition")) for r in self.rows), 16)
        for r in self.rows:
            self.assertEqual(r["raw_sql"], r["sql"])
            self.assertEqual(r["transformations"], [])
            self.assertEqual(r["observed_parameter_slots"], [])
            self.assertIsNone(r["parameter_types"])
            self.assertEqual(r["application_schema_validity"], "not-claimed")
            self.assertNotIn("parameter_values", r)
            self.assertNotIn("expected_value", r)
            self.assertIn(r["commit"], r["source_url"])

    def test_exact_operation_tree_and_all_inventory(self):
        self.assertEqual(Counter((e["operator"], e["all"]) for r in self.rows
                                 for e in r["observed_syntax"]["set_operations"]), {
            ("union", True): 53, ("union", False): 48,
            ("intersect", True): 7, ("intersect", False): 44,
            ("except", True): 14, ("except", False): 44,
        })
        gaps = [r for r in self.rows if r["observed_syntax"]["dependencies"]]
        self.assertEqual(len(gaps), 4)
        self.assertTrue(all(r["factor"] == "intersect" and not r["observed_syntax"]["source_free"] for r in gaps))

    def test_fixed_registry_and_cte_alias_override(self):
        validate_registry(self.rows, self.registry)
        self.assertEqual([len(self.registry[f]) for f in POPULATIONS], [50, 6, 6])
        self.assertEqual(sum(len(r["output_columns"]) for rs in self.registry.values() for r in rs), 83)
        row = next(r for r in self.rows if "t3(z) AS" in r["sql"])
        expected = next(r["output_columns"] for r in self.registry["union"] if r["id"] == row["id"])
        self.assertEqual(expected, [{"name": "x", "type": "int32", "nullable": False},
                                    {"name": "z", "type": "int32", "nullable": False}])

    def test_registry_rejects_metadata_identity_and_order_mutations(self):
        for field, value in [("name", "renamed"), ("type", "text"), ("nullable", 0),
                             ("nullable", True)]:
            changed = deepcopy(self.registry)
            changed["union"][0]["output_columns"][0][field] = value
            with self.subTest(field=field, value=value), self.assertRaises(ValueError):
                validate_registry(self.rows, changed)
        for mutation in (
            lambda r: r["union"].pop(),
            lambda r: r["union"].reverse(),
            lambda r: r["intersect"][0].update(id=r["except"][0]["id"]),
        ):
            changed = deepcopy(self.registry)
            mutation(changed)
            with self.assertRaises(ValueError):
                validate_registry(self.rows, changed)

    def test_population_rejects_missing_duplicate_or_wrong_factor(self):
        with self.assertRaises(ValueError):
            validate_population(self.rows[:-1])
        changed = deepcopy(self.rows)
        changed[50]["sql"] = changed[0]["sql"]
        with self.assertRaises(ValueError):
            validate_population(changed)
        changed = deepcopy(self.rows)
        changed[0]["factor"] = "intersect"
        with self.assertRaises(ValueError):
            validate_population(changed)

    def test_source_pin_slice_and_selector_mutations_fail(self):
        for mutate in (
            lambda m: m["sources"]["postgres"]["files"][0].update(sha256="0" * 64),
            lambda m: m["sources"]["postgres"].update(license_sha256="0" * 64),
            lambda m: m["selections"][0]["selector"].update(start=m["selections"][0]["selector"]["start"] + 1),
            lambda m: m["selections"][0]["selector"].update(kind="unregistered"),
            lambda m: m["selections"][0].update(sql_sha256="0" * 64),
        ):
            changed = deepcopy(self.manifest)
            mutate(changed)
            with self.assertRaises(ValueError):
                extract(changed)

    def test_raw_set_children_preserve_precedence_and_operand_local_modifiers(self):
        tree = compound("UNION", right=compound("INTERSECT", all=True, sortClause=[{}]),
                        limitCount={"A_Const": {"ival": {"ival": 1}}})
        o = observe(tree, "SELECT 1 UNION (SELECT 2 INTERSECT ALL SELECT 3 ORDER BY 1) LIMIT 1", "union")
        self.assertEqual([(e["path"], e["operator"], e["all"], e["order_items"]) for e in o["set_operations"]],
                         [("$", "union", False, 0), ("$.right", "intersect", True, 1)])
        self.assertTrue(o["set_operations"][0]["limit"])
        with self.assertRaises(ValueError):
            validate_observation(o, "except")

    def test_join_larg_rarg_are_not_mistaken_for_set_children(self):
        tree = select(fromClause=[{"JoinExpr": {
            "larg": {"RangeSubselect": {"subquery": compound()}},
            "rarg": {"RangeSubselect": {"subquery": compound("EXCEPT")}},
        }}])
        result = observe(tree, "SELECT 1", "union")
        self.assertEqual([e["operator"] for e in result["set_operations"]], ["union", "except"])

    def test_sequential_cte_scope_and_utf8_byte_positions(self):
        sql = "WITH c AS (SELECT 'é') SELECT * FROM c UNION SELECT * FROM real_table"
        tree = compound(left=select(fromClause=[relation(sql, "c")]),
                        right=select(fromClause=[relation(sql, "real_table")]),
                        withClause={"ctes": [{"CommonTableExpr": {
                            "ctename": "c", "ctequery": select(),
                        }}]})
        result = observe(tree, sql, "union")
        self.assertEqual([r["cte"] for r in result["relations"]], [True, False])
        self.assertFalse(result["source_free"])
        changed = deepcopy(result)
        changed["source_free"] = True
        with self.assertRaises(ValueError):
            validate_observation(changed, "union", sql)
        changed = deepcopy(result)
        changed["relations"][0]["byte_location"] -= 1
        with self.assertRaises(ValueError):
            validate_observation(changed, "union", sql)

    def test_recursive_values_lateral_and_unregistered_calls_are_rejected(self):
        for tree in (
            compound(withClause={"recursive": True}),
            compound(left=select(valuesLists=[[{}]])),
            compound(left=select(fromClause=[{"RangeSubselect": {"lateral": True, "subquery": select()}}])),
            compound(left=select(targetList=[{"FuncCall": {"funcname": [{"String": {"sval": "lower"}}]}}])),
        ):
            with self.assertRaises(ValueError):
                observe(tree, "SELECT 1 UNION SELECT 2", "union")

    def test_repeated_paths_wrong_boolean_and_input_footprints_fail(self):
        base = observe(compound(), "SELECT 1 UNION SELECT 2", "union")
        for mutate in (
            lambda x: x["set_operations"][0].update(all=1),
            lambda x: x["set_operations"].append(x["set_operations"][0]),
            lambda x: x.update(parameter_slots=[True]),
            lambda x: x.update(parameter_slots=[1]),
            lambda x: x.update(dependencies={"made_up": 1}),
        ):
            changed = deepcopy(base)
            mutate(changed)
            with self.assertRaises(ValueError):
                validate_observation(changed, "union")


class SetSQLLogicReaderTests(unittest.TestCase):
    def test_complete_crlf_input_and_literal_condition_are_retained(self):
        text = "mode cockroach\r\nonlyif cockroach\r\nquery II rowsort\r\nSELECT 1,2 UNION SELECT 3,4\r\n----\r\nopaque\r\n"
        sql, line, detail = selected_setop_sqllogic(text, selector(text, 3))
        self.assertEqual(sql, "SELECT 1,2 UNION SELECT 3,4\r\n")
        self.assertEqual(line, 4)
        self.assertEqual(detail["source_condition"], "onlyif cockroach")

    def test_multiline_results_are_opaque_and_cannot_be_selected(self):
        text = ("query T multiline\nEXPLAIN SOMETHING\n----\nplan\n\nquery I\n"
                "SELECT 99 UNION SELECT 98\n----\nnot an input\nEOF\n\n"
                "query I\n(SELECT 1) UNION SELECT 2\n----\n1\n2\n")
        sql, _, _ = selected_setop_sqllogic(text, selector(text, 12))
        self.assertEqual(sql, "(SELECT 1) UNION SELECT 2\n")
        with self.assertRaises(ValueError):
            selected_setop_sqllogic(text, selector(text, 6))

    def test_simple_connection_record_is_skipped_without_execution(self):
        text = ("simple conn=mz_system,user=mz_system\nALTER SYSTEM x\n----\nCOMPLETE 0\n\n"
                "mode cockroach\nquery I\nSELECT 1 EXCEPT SELECT 2\n----\n1\n")
        self.assertEqual(selected_setop_sqllogic(text, selector(text, 7))[0], "SELECT 1 EXCEPT SELECT 2\n")

    def test_unselected_legacy_empty_result_does_not_relax_selected_delimiter(self):
        text = "query I\nSELECT 0\n\nquery I\nSELECT 1 INTERSECT SELECT 2\n----\n\n"
        self.assertEqual(selected_setop_sqllogic(text, selector(text, 4))[0], "SELECT 1 INTERSECT SELECT 2\n")
        with self.assertRaises(ValueError):
            selected_setop_sqllogic(text, selector(text, 1))

    def test_bad_prefix_missing_eof_partial_and_multiple_inputs_fail(self):
        valid = "query I\nSELECT 1 UNION SELECT 2\n----\n1\n2\n"
        for text, line in [
            ("require unknown\n" + valid, 2),
            ("query T multiline\nEXPLAIN x\n----\nopaque\n\n" + valid, 7),
            ("query I\nSELECT 1; SELECT 2\n----\n1\n", 1),
            ("query I\nSELECT ${dynamic}\n----\n1\n", 1),
        ]:
            with self.subTest(text=text), self.assertRaises(ValueError):
                selected_setop_sqllogic(text, selector(text, line))
        changed = selector(valid, 1)
        changed["end"] -= 1
        with self.assertRaises(ValueError):
            selected_setop_sqllogic(valid, changed)


if __name__ == "__main__":
    unittest.main()
