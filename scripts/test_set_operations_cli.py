"""Independent multiset anchors and fail-closed set-operation evidence protocols."""
from collections import Counter
from copy import deepcopy
import json
from pathlib import Path
import subprocess
import tempfile
import unittest
from unittest.mock import patch

import check_assurance_cli
import check_set_operations_cli as checker
from check_postgresql_cli import NULL
from generate_set_operation_examples import all_cases, cases, combine, schema


def native_transcript(expected):
    lines = []
    for name, (width, rows) in expected.items():
        lines.extend((name, ",".join(f'"c{i}"' for i in range(width))))
        for row in rows:
            lines.append(",".join(NULL if value is None else '"' + value.replace('"', '""') + '"'
                                  for value in row))
    return "\n".join(lines) + "\n"


class SetOperationsCliTests(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        cls.authored, cls.sources = checker.load_cases()
        cls.registry = json.loads((checker.FIXTURES / "source_contracts.json").read_text())

    def case(self, shape, factor="union"):
        return next(row for row in self.authored if row["shape"] == shape and row["factor"] == factor)

    def fixture_copy(self, rows=None, sources=None, registry=None, catalog=None):
        temporary = tempfile.TemporaryDirectory()
        self.addCleanup(temporary.cleanup)
        root = Path(temporary.name)
        (root / "synthetic.json").write_text(json.dumps(self.authored if rows is None else rows))
        (root / "schema.json").write_text(json.dumps(schema() if catalog is None else catalog))
        (root / "source_contracts.json").write_text(json.dumps(self.registry if registry is None else registry))
        (root / "concrete.jsonl").write_text("".join(json.dumps(row) + "\n" for row in (
            self.sources if sources is None else sources)))
        return root

    def test_three_factors_have_fifty_unique_examples_each(self):
        self.assertEqual(self.authored, all_cases())
        for rows in (self.authored, self.sources):
            self.assertEqual(Counter(row["factor"] for row in rows),
                             {"union": 50, "intersect": 50, "except": 50})
            self.assertEqual(len({row["sql"] for row in rows}), 150)
        self.assertEqual(sum(len(row["output_columns"]) for row in self.authored), 162)
        self.assertEqual(len({row["shape"] for row in self.authored}), 50)

    def test_multiset_model_handles_duplicates_nulls_and_empty_inputs(self):
        left, right = [[1], [1], [1], [None], [None], [2]], [[1], [1], [None], [3]]
        wanted = {
            ("union", True): [[1]] * 5 + [[None]] * 3 + [[2], [3]],
            ("union", False): [[1], [None], [2], [3]],
            ("intersect", True): [[1], [1], [None]],
            ("intersect", False): [[1], [None]],
            ("except", True): [[1], [None], [2]],
            ("except", False): [[2]],
        }
        for (factor, all_), rows in wanted.items():
            with self.subTest(factor=factor, all=all_):
                self.assertEqual(Counter(map(tuple, combine(factor, all_, left, right))),
                                 Counter(map(tuple, rows)))
                self.assertEqual(combine(factor, all_, [], []), [])
        self.assertEqual(combine("except", True, [[None, 1], [None, 1]], [[None, 1]]), [[None, 1]])
        self.assertEqual(combine("except", False, [[None, 1], [None, 1]], [[None, 1]]), [])

    def test_independent_extra_population_detects_bag_and_join_multiplicity(self):
        data = {"items": [[8, None, "N"], [9, 8, "A"], [10, 8, "B"]],
                "labels": [[8, "A"], [8, "B"], [11, "C"]]}
        generated = {(r["factor"], r["shape"]): r for r in cases(data)}
        expected = {
            ("union", "using-join-bags"): [[8], [8], [8], [9], [10]],
            ("intersect", "using-join-bags"): [[8]],
            ("except", "using-join-bags"): [[8]],
            ("intersect", "base-null-duplicate-bags"): [[8], [8]],
            ("except", "base-null-duplicate-bags"): [[None]],
        }
        for key, rows in expected.items():
            self.assertEqual(Counter(map(tuple, generated[key]["expected_rows"])),
                             Counter(map(tuple, rows)))

    def test_unknowns_modifiers_labels_and_dialect_differences_are_preregistered(self):
        unknown = self.case("contextual-null")
        self.assertEqual([(c["type"], c["nullable"]) for c in unknown["output_columns"]], [("int32", True)])
        self.assertEqual(self.case("unknown-null")["output_columns"][0]["type"], "text")
        self.assertEqual(self.case("same-varchar-modifier")["output_columns"][0]["type"], "varchar(3)")
        self.assertEqual(self.case("different-varchar-modifier")["output_columns"][0]["type"], "varchar")
        self.assertEqual(self.case("char-text")["output_columns"][0]["type"], "bpchar")
        self.assertEqual(self.case("char-text")["expected_rows"], [["a  "], ["b"]])
        self.assertEqual([c["type"] for c in self.case("sort-one-unknown-slot")["output_columns"]],
                         ["text", "int32"])
        self.assertEqual([c["name"] for c in self.case("identical-duplicate-label-sort")["output_columns"]],
                         ["x", "x"])
        self.assertEqual(self.case("contextual-string")["expected_rows"], [[1]])
        self.assertEqual(self.case("contextual-string")["sqlite_expected_rows"], [["1"], [1]])
        self.assertEqual(self.case("precedence", "intersect")["expected_rows"], [[1], [2]])
        self.assertEqual(self.case("precedence", "intersect")["sqlite_expected_rows"], [[2]])
        self.assertEqual(self.case("left-nested-all")["sqlite_source_error"], 'near "(": syntax error')

    def test_source_registry_has_fixed_sixty_two_queries_and_eighty_three_positions(self):
        registry = checker.source_registry()
        self.assertEqual(len(registry), 62)
        self.assertEqual(sum(map(len, registry.values())), 83)
        self.assertEqual([len(self.registry[f]) for f in checker.FACTORS], [50, 6, 6])
        self.assertEqual(set(registry), {r["id"] for r in self.sources if r["observed_syntax"]["source_free"]})
        self.assertEqual(len(self.sources) - len(registry), 88)
        self.assertTrue(all(r["raw_sql"] == r["sql"] and r["transformations"] == [] for r in self.sources))

    def test_source_registry_rejects_omissions_duplicates_and_metadata_changes(self):
        for change in ("missing", "duplicate", "order", "name", "type", "nullable", "nullable_int", "extra"):
            registry = deepcopy(self.registry)
            if change == "missing":
                registry["union"].pop()
            elif change == "duplicate":
                registry["union"][1] = deepcopy(registry["union"][0])
            elif change == "order":
                registry["union"].reverse()
            elif change == "extra":
                registry["new_key"] = True
            else:
                key = "nullable" if change == "nullable_int" else change
                registry["union"][0]["output_columns"][0][key] = {
                    "name": "renamed", "type": "text", "nullable": True, "nullable_int": 0}[change]
            with self.subTest(change=change), patch.object(checker, "FIXTURES", self.fixture_copy(
                    registry=registry)), self.assertRaises(AssertionError):
                checker.source_registry()

    def test_loader_rejects_population_catalog_parameter_and_provenance_tampering(self):
        for change in ("rows", "sql", "factor", "nullable_int", "catalog_exposure",
                       "ordered", "parameters", "state", "sqlite_value", "source_hash", "source_raw",
                       "source_transform", "source_eligibility", "source_eligibility_int", "source_slots"):
            rows, sources, catalog = deepcopy(self.authored), deepcopy(self.sources), schema()
            if change == "rows":
                rows.pop()
            elif change == "sql":
                rows[0]["sql"] += " "
            elif change == "factor":
                rows[0]["factor"] = "intersect"
            elif change == "nullable_int":
                rows[0]["output_columns"][0]["nullable"] = 0
            elif change == "catalog_exposure":
                catalog["tables"][0]["exposeUnqualified"] = 1
            elif change == "ordered":
                rows[45]["ordered"] = False
            elif change == "parameters":
                rows[47]["parameter_values"].reverse()
            elif change == "state":
                rows[0]["expected_rows_by_state"].pop("empty")
            elif change == "sqlite_value":
                rows[6]["sqlite_expected_rows_by_state"]["both"] = [[1]]
            elif change == "source_hash":
                sources[0]["sql_sha256"] = "0" * 64
            elif change == "source_raw":
                sources[0]["raw_sql"] += " "
            elif change == "source_transform":
                sources[0]["transformations"] = ["rewritten"]
            elif change in ("source_eligibility", "source_eligibility_int"):
                sources[0]["observed_syntax"]["source_free"] = False if change.endswith("eligibility") else 1
            else:
                sources[0]["observed_parameter_slots"] = [1]
            with self.subTest(change=change), patch.object(checker, "FIXTURES", self.fixture_copy(
                    rows, sources, catalog=catalog)), self.assertRaises(AssertionError):
                checker.load_cases()

    def test_parameters_count_cte_definitions_once_and_preserve_numbered_reuse(self):
        anonymous, numbered = self.case("anonymous-parameters"), self.case("numbered-parameters")
        self.assertEqual(checker.parameters(anonymous["sql"], "postgres"),
                         [("anonymous", i) for i in range(1, 7)])
        self.assertEqual(checker.parameters(numbered["sql"], "postgres"),
                         [("numbered", 2), ("numbered", 1), ("numbered", 1)])
        self.assertIn("EXECUTE set_parameters (3, 6)", checker.capture(numbered, numbered["sql"])[1])
        self.assertEqual(checker.sqlite_bindings(numbered["sqlite_sql"], numbered["parameter_values"]),
                         {"1": 3, "2": 6})

    def test_static_certificate_requires_exact_profile_and_independent_metadata(self):
        row = self.case("contextual-null")
        good = {"status": "valid", "assurance": "declarative",
                "profile": check_assurance_cli.PROFILES["contract"], "evidence": "declarative-derivation",
                "catalogUnchanged": True, "typePrecision": "exact",
                "outputColumns": [{k: col[k] for k in ("name", "type", "nullable")} for col in row["output_columns"]]}
        for change in (None, "assurance", "profile", "evidence", "catalogUnchanged", "typePrecision", "nullable"):
            report = deepcopy(good)
            if change == "nullable":
                report["outputColumns"][0]["nullable"] = False
            elif change is not None:
                report[change] = "weaker"
            with self.subTest(change=change), patch.object(check_assurance_cli, "invoke",
                    return_value=subprocess.CompletedProcess([], 0, json.dumps(report), "")):
                if change is None:
                    checker.validity(row)
                else:
                    with self.assertRaises(AssertionError):
                        checker.validity(row)

    def test_native_protocol_checks_all_populations_and_preserves_exact_descriptors(self):
        sql = [r["sql"] for r in self.authored]
        script, expected = checker.postgres_script(self.authored, sql)
        self.assertEqual(len(expected), 1200)
        for token in ("SAVEPOINT set_case;", "ROLLBACK TO SAVEPOINT set_case;", "RELEASE SAVEPOINT set_case;"):
            self.assertEqual(script.splitlines().count(token), 1200)
        self.assertEqual(script.count("TRUNCATE public.items,public.labels;"), 4)
        self.assertTrue(script.endswith("ROLLBACK;"))
        descriptions, columns = checker.describe_script(self.authored, sql)
        self.assertEqual(len(columns), 324)
        self.assertEqual(descriptions.splitlines().count("\\gdesc"), 300)
        for type_ in ("v|character varying(3)", "v|bpchar", "v|numeric(6,2)", "v|timestamp(2) without time zone"):
            self.assertIn(type_, columns)
        for function in (checker.postgres_script, checker.describe_script, checker.sqlite_observations):
            with self.subTest(function=function), self.assertRaises(AssertionError):
                function(self.authored, sql[:-1])

    def test_native_results_reject_missing_rows_duplicate_bags_width_and_extra_markers(self):
        _, expected = checker.postgres_script(self.authored, [r["sql"] for r in self.authored])
        actual = checker.parse_results(native_transcript(expected))
        checker.validate_native(actual, expected)
        checker.validate_ordered(actual, self.authored)
        keys = list(expected)
        for change in ("missing", "extra", "width", "duplicate"):
            mutated = deepcopy(actual)
            if change == "missing":
                mutated.pop(keys[0])
            elif change == "extra":
                mutated["unexpected"] = (1, [])
            elif change == "width":
                mutated[keys[0]] = (2, mutated[keys[0]][1])
            else:
                mutated[keys[0]][1].append(mutated[keys[0]][1][0])
            with self.subTest(change=change), self.assertRaises(AssertionError):
                checker.validate_native(mutated, expected)

    def test_ordered_rows_reject_equal_bags_in_wrong_order(self):
        _, expected = checker.postgres_script(self.authored, [r["sql"] for r in self.authored])
        actual = checker.parse_results(native_transcript(expected))
        row = self.case("ordered-null-last")
        index = self.authored.index(row) + 1
        key = checker.marker("set_both", index, True, "postgres")
        actual[key][1].reverse()
        checker.validate_native(actual, expected)
        with self.assertRaises(AssertionError):
            checker.validate_ordered(actual, self.authored)

    def test_analysis_observations_keep_conversion_success_separate_from_typing(self):
        rows = checker.boundary_cases()
        self.assertEqual(len(rows), 90)
        self.assertEqual(Counter(r["status"] for r in rows), {"invalid": 75, "unsupported": 9, "valid": 6})
        conversion = [r for r in rows if r["id"].endswith("unknown-string-conversion")]
        self.assertEqual(len(conversion), 3)
        self.assertTrue(all(r["status"] == "valid" and r["prepare_state"] == "22P02" for r in conversion))
        script, expected = checker.analysis_script()
        self.assertEqual(len(expected), 180)
        self.assertEqual(script.count("SELECT pg_temp.set_stage("), 180)
        self.assertIn("FROM pg_prepared_statements WHERE name='set_probe'", script)
        _, repeated = checker.analysis_script([r["sql"] for r in rows])
        self.assertEqual(len(repeated), 360)
        with self.assertRaises(AssertionError):
            checker.analysis_script([r["sql"] for r in rows[:-1]])
        with patch.object(checker, "assert_report") as report:
            self.assertEqual(checker.boundaries(), 92)
        self.assertEqual([call.args[1] for call in report.call_args_list[-2:]], ["invalid", "invalid"])

    def test_sqlite_exclusions_require_exact_exit_status_and_diagnostic(self):
        for shape, factor in (("array-widening", "union"), ("branch-local-cte", "union"),
                              ("duplicate-all", "intersect"), ("nested-row-lock", "except")):
            row = self.case(shape, factor)
            code, status = (1, "invalid") if row["sqlite_mode"] == "input_excluded" else (3, "unsupported")
            for change in (None, "exit", "status", "diagnostic"):
                report = {"status": status, "diagnostic": {"code": row["sqlite_diagnostic"]}}
                exit_code = code
                if change == "exit":
                    exit_code = 0
                elif change == "status":
                    report["status"] = "valid"
                elif change == "diagnostic":
                    report["diagnostic"]["code"] = "unrelated"
                with self.subTest(shape=shape, change=change), patch.object(checker, "invoke",
                        return_value=subprocess.CompletedProcess([], exit_code, json.dumps(report), "")):
                    if change is None:
                        self.assertIsNone(checker.sqlite_render(row))
                    else:
                        with self.assertRaises(AssertionError):
                            checker.sqlite_render(row)

    def test_scripts_never_execute_scraped_sql(self):
        row = deepcopy(self.authored[0])
        row["source_kind"] = self.sources[0]["source_kind"]
        self.assertNotEqual(row["source_kind"], "synthetic")
        for function in (checker.postgres_script, checker.describe_script, checker.sqlite_observations):
            with self.subTest(function=function), self.assertRaises(AssertionError):
                function([row], [row["sql"]])


if __name__ == "__main__":
    unittest.main()
