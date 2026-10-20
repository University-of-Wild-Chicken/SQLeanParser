"""Independent recursive models and fail-closed evidence protocol checks."""
from copy import deepcopy
import json
from pathlib import Path
import subprocess
import tempfile
import unittest
from unittest.mock import patch

import check_assurance_cli
import check_recursive_contract_cli as checker
from generate_recursive_contract_examples import all_cases, cases, closure, schema
from test_set_operations_cli import native_transcript


class RecursiveContractCliTests(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        cls.authored = all_cases()
        cls.sources = [json.loads(line) for line in (checker.FIXTURES / "concrete.jsonl").read_text().splitlines()]

    def case(self, shape):
        return next(row for row in self.authored if row["shape"] == shape)

    def fixture_copy(self, rows=None, sources=None, registry=None, catalog=None):
        temporary = tempfile.TemporaryDirectory()
        self.addCleanup(temporary.cleanup)
        root = Path(temporary.name)
        (root / "synthetic.json").write_text(json.dumps(self.authored if rows is None else rows))
        (root / "schema.json").write_text(json.dumps(schema() if catalog is None else catalog))
        if registry is None:
            registry = json.loads((checker.FIXTURES / "source_contracts.json").read_text())
        (root / "source_contracts.json").write_text(json.dumps(registry))
        (root / "concrete.jsonl").write_text("".join(json.dumps(row) + "\n" for row in (
            self.sources if sources is None else sources)))
        return root

    def test_fifty_distinct_authored_and_unchanged_concrete_queries(self):
        rows, sources = checker.load_cases()
        self.assertEqual(rows, self.authored)
        self.assertEqual(len({r["shape"] for r in rows}), 50)
        self.assertEqual(sum(len(r["output_columns"]) for r in rows), 58)
        self.assertEqual(len({r["sql"] for r in sources}), 50)
        self.assertTrue(all(r["raw_sql"] == r["sql"] and not r["transformations"] for r in sources))
        self.assertTrue(all(set(r["expected_rows_by_state"]) == set(checker.STATES) for r in rows))

    def test_frontier_evaluation_distinguishes_path_bags_from_reachability(self):
        edges = [(1, 2), (1, 3), (2, 4), (3, 4)]
        step = lambda row: [[dst] for src, dst in edges if row[0] == src]
        self.assertEqual(closure([[1]], step), [[1], [2], [3], [4], [4]])
        self.assertEqual(closure([[1]], step, distinct=True), [[1], [2], [3], [4]])
        self.assertEqual(closure([[1], [1]], lambda row: [row], distinct=True), [[1]])
        self.assertEqual(closure([], lambda _: [[1]]), [])
        with self.assertRaisesRegex(ValueError, "did not terminate"):
            closure([[1]], lambda row: [row])

    def test_independent_population_checks_dag_paths_and_missing_nodes(self):
        data = {"nodes": [[1, None, "root"], [2, 1, "a"], [3, 1, "b"], [7, 2, "c"]],
                "edges": [[1, 2, 1], [1, 3, 2], [2, 7, 3], [3, 7, 5], [7, 8, 9]]}
        rows = {r["shape"]: r for r in cases(data)}
        self.assertEqual(rows["graph-path-bags"]["expected_rows"], [[1], [2], [3], [7], [7], [8], [8]])
        self.assertEqual(rows["graph-reachability"]["expected_rows"], [[1], [2], [3], [7], [8]])
        self.assertEqual(rows["hierarchy-depth"]["expected_rows"], [[1, 0], [2, 1], [3, 1], [7, 2]])
        self.assertEqual(rows["ancestors"]["expected_rows"], [])
        self.assertEqual(self.case("graph-path-bags")["expected_rows_by_state"]["empty"], [[1]])
        self.assertEqual(self.case("hierarchy-all")["expected_rows_by_state"]["empty"], [])

    def test_exact_modifiers_unknowns_and_nullable_bounds_are_preregistered(self):
        for shape, type_ in (("unknown-null-anchor", "text"), ("typed-null-anchor", "int32"),
                             ("varchar-modifier", "varchar(3)"), ("numeric-modifier", "numeric(6,2)"),
                             ("array-growth", "integer[]")):
            with self.subTest(shape=shape):
                self.assertEqual(self.case(shape)["output_columns"][0]["type"], type_)
                self.assertIs(self.case(shape)["output_columns"][0]["nullable"], True)
        self.assertEqual(self.case("numeric-modifier")["expected_rows"], [["1.00"], ["1.50"], ["2.00"]])
        self.assertEqual(self.case("numeric-modifier")["sqlite_expected_rows"], [[1], [1.5], [2]])
        self.assertIs(self.case("nonnullable-outer-expression")["output_columns"][0]["nullable"], False)
        self.assertIs(self.case("unused-definition-parameters")["output_columns"][0]["nullable"], False)

    def test_source_registry_is_fixed_and_rejects_metadata_tampering(self):
        registry = json.loads((checker.FIXTURES / "source_contracts.json").read_text())
        self.assertEqual(len(checker.source_registry()), 21)
        self.assertEqual(sum(len(r["output_columns"]) for r in registry), 24)
        for change in ("missing", "duplicate", "order", "name", "type", "nullable"):
            mutated = deepcopy(registry)
            if change == "missing":
                mutated.pop()
            elif change == "duplicate":
                mutated[1] = deepcopy(mutated[0])
            elif change == "order":
                mutated.reverse()
            else:
                mutated[0]["output_columns"][0][change] = {"name": "other", "type": "bool", "nullable": False}[change]
            with self.subTest(change=change), patch.object(checker, "FIXTURES", self.fixture_copy(
                    registry=mutated)), self.assertRaises(AssertionError):
                checker.source_registry()

    def test_loader_rejects_fixture_catalog_parameters_and_source_tampering(self):
        for change in ("population", "sql", "nullable_int", "catalog", "parameters", "state",
                       "sqlite_rows", "source_hash", "source_raw", "source_transform"):
            rows, sources, catalog = deepcopy(self.authored), deepcopy(self.sources), schema()
            if change == "population":
                rows.pop()
            elif change == "sql":
                rows[0]["sql"] += " "
            elif change == "nullable_int":
                rows[0]["output_columns"][0]["nullable"] = 1
            elif change == "catalog":
                catalog["tables"][0]["exposeUnqualified"] = 1
            elif change == "parameters":
                rows[30]["parameter_values"][0] = 99
            elif change == "state":
                rows[0]["expected_rows_by_state"].pop("empty")
            elif change == "sqlite_rows":
                rows[0]["sqlite_expected_rows_by_state"]["both"] = []
            elif change == "source_hash":
                sources[0]["sql_sha256"] = "0" * 64
            elif change == "source_raw":
                sources[0]["raw_sql"] += " "
            else:
                sources[0]["transformations"] = ["changed"]
            with self.subTest(change=change), patch.object(checker, "FIXTURES", self.fixture_copy(
                    rows=rows, sources=sources, catalog=catalog)), self.assertRaises(AssertionError):
                checker.load_cases()

    def test_parameter_occurrences_are_lexical_not_recursive_iterations(self):
        anonymous, numbered = self.case("anonymous-parameters"), self.case("numbered-parameters")
        self.assertEqual(checker.parameters(anonymous["sql"], "postgres"),
                         [("anonymous", i) for i in range(1, 6)])
        self.assertEqual(checker.parameters(numbered["sql"], "postgres"),
                         [("numbered", 2), ("numbered", 1), ("numbered", 3)])
        self.assertIn("EXECUTE recursive_parameters (2, 1, 5)", checker.capture(numbered, numbered["sql"])[1])
        self.assertEqual(checker.sqlite_bindings(numbered["sqlite_sql"], numbered["parameter_values"]),
                         {"1": 2, "2": 1, "3": 5})
        unused = self.case("unused-definition-parameters")
        self.assertEqual(len(checker.parameters(unused["sql"], "postgres")), 5)

    def test_static_report_requires_independent_metadata_and_evidence(self):
        row = self.case("unknown-null-anchor")
        good = {"status": "valid", "assurance": "declarative",
                "profile": check_assurance_cli.PROFILES["contract"], "evidence": "declarative-derivation",
                "catalogUnchanged": True, "typePrecision": "exact",
                "outputColumns": [{k: c[k] for k in ("name", "type", "nullable")} for c in row["output_columns"]]}
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

    def test_native_protocol_covers_four_states_and_exact_descriptors(self):
        sql = [r["sql"] for r in self.authored]
        script, expected = checker.postgres_script(self.authored, sql)
        self.assertEqual(len(expected), 400)
        self.assertEqual(script.count("TRUNCATE public.nodes,public.edges;"), 4)
        self.assertEqual(script.splitlines().count("SAVEPOINT recursive_case;"), 400)
        self.assertEqual(script.splitlines().count("ROLLBACK TO SAVEPOINT recursive_case;"), 400)
        self.assertTrue(script.endswith("ROLLBACK;"))
        self.assertIn("SET LOCAL statement_timeout = '5s';", script)
        descriptions, columns = checker.describe_script(self.authored, sql)
        self.assertEqual(len(columns), 116)
        self.assertEqual(descriptions.splitlines().count("\\gdesc"), 100)
        for descriptor in ("n|character varying(3)", "n|numeric(6,2)", "n|integer[]"):
            self.assertIn(descriptor, columns)
        for method in (checker.postgres_script, checker.describe_script, checker.sqlite_observations):
            with self.subTest(method=method), self.assertRaises(AssertionError):
                method(self.authored, sql[:-1])

    def test_native_evidence_rejects_missing_extra_width_and_duplicate_rows(self):
        _, expected = checker.postgres_script(self.authored, [r["sql"] for r in self.authored])
        actual = checker.parse_results(native_transcript(expected))
        checker.validate_native(actual, expected)
        checker.validate_ordered(actual, self.authored)
        key = next(iter(actual))
        for change in ("missing", "extra", "width", "duplicate"):
            mutated = deepcopy(actual)
            if change == "missing":
                mutated.pop(key)
            elif change == "extra":
                mutated["extra"] = (1, [])
            elif change == "width":
                mutated[key] = (2, mutated[key][1])
            else:
                mutated[key][1].append(mutated[key][1][0])
            with self.subTest(change=change), self.assertRaises(AssertionError):
                checker.validate_native(mutated, expected)

    def test_pagination_rejects_same_bag_in_different_order(self):
        _, expected = checker.postgres_script(self.authored, [r["sql"] for r in self.authored])
        actual = checker.parse_results(native_transcript(expected))
        key = checker.marker("recursive_both", 31, True, "postgres")
        actual[key][1].reverse()
        checker.validate_native(actual, expected)
        with self.assertRaises(AssertionError):
            checker.validate_ordered(actual, self.authored)

    def test_downloaded_queries_cannot_enter_native_execution_helpers(self):
        row = deepcopy(self.authored[0])
        row["source_kind"] = "concrete"
        for method, arguments in ((checker.capture, (row, row["sql"])),
                                  (checker.postgres_script, ([row], [row["sql"]])),
                                  (checker.describe_script, ([row], [row["sql"]])),
                                  (checker.sqlite_observations, ([row], [row["sqlite_sql"]]))):
            with self.subTest(method=method), self.assertRaises(AssertionError):
                method(*arguments)

    def test_sqlite_preflight_has_registered_successes_errors_and_exclusions(self):
        canonical = [None if row["sqlite_mode"] in ("render_unsupported", "input_excluded") else row["sqlite_sql"]
                     for row in self.authored]
        self.assertEqual(checker.sqlite_observations(self.authored, canonical), (312, 16))
        self.assertEqual(sum(sql is None for sql in canonical), 9)
        row = deepcopy(self.case("nested-derived-reference"))
        row["sqlite_error"] = "unreviewed error"
        with self.assertRaises(AssertionError):
            checker.sqlite_observations([row], [row["sqlite_sql"]])

    def test_sqlite_exclusions_require_exact_classification(self):
        for shape, code, status in (("array-growth", 1, "invalid"), ("text-growth", 3, "unsupported")):
            row = self.case(shape)
            good = {"status": status, "diagnostic": {"code": row["sqlite_diagnostic"]}}
            for change in (None, "exit", "status", "diagnostic"):
                report = deepcopy(good)
                exit_code = code
                if change == "exit":
                    exit_code = 0
                elif change == "status":
                    report["status"] = "valid"
                elif change == "diagnostic":
                    report["diagnostic"]["code"] = "different"
                with self.subTest(shape=shape, change=change), patch.object(checker, "invoke",
                        return_value=subprocess.CompletedProcess([], exit_code, json.dumps(report), "")):
                    if change is None:
                        self.assertIsNone(checker.sqlite_render(row))
                    else:
                        with self.assertRaises(AssertionError):
                            checker.sqlite_render(row)


if __name__ == "__main__":
    unittest.main()
