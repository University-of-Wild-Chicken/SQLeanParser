"""Independent fixture anchors and fail-closed CTE observation protocols."""
from collections import Counter
from contextlib import nullcontext, redirect_stdout
from copy import deepcopy
import io
import json
from pathlib import Path
import subprocess
import tempfile
import unittest
from unittest.mock import patch

import check_assurance_cli
import check_cte_contract_cli as checker
from check_postgresql_cli import NULL
from generate_cte_contract_examples import all_cases, cases, schema


def native_transcript(expected):
    lines = []
    for name, (width, rows) in expected.items():
        lines.extend((name, ",".join(f'"c{i}"' for i in range(width))))
        for row in rows:
            lines.append(",".join(NULL if value is None else
                                  '"' + value.replace('"', '""') + '"' for value in row))
    return "\n".join(lines) + "\n"


class CteContractCliTests(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        cls.authored, cls.sources = checker.load_cases()
        cls.registry = json.loads((checker.FIXTURES / "source_contracts.json").read_text())

    def case(self, shape):
        return next(row for row in self.authored if row["shape"] == shape)

    def fixture_copy(self, rows=None, sources=None, registry=None, catalog=None):
        temporary = tempfile.TemporaryDirectory()
        self.addCleanup(temporary.cleanup)
        root = Path(temporary.name)
        (root / "synthetic.json").write_text(json.dumps(self.authored if rows is None else rows))
        (root / "schema.json").write_text(json.dumps(schema() if catalog is None else catalog))
        (root / "source_contracts.json").write_text(json.dumps(self.registry if registry is None else registry))
        (root / "concrete.jsonl").write_text("".join(
            json.dumps(row) + "\n" for row in (self.sources if sources is None else sources)))
        return root

    def test_exact_fifty_authored_schemas_and_dialect_populations(self):
        self.assertEqual(self.authored, all_cases())
        self.assertEqual(len(self.authored), 50)
        self.assertEqual(sum(len(r["output_columns"]) for r in self.authored), 87)
        self.assertEqual(Counter(r["sqlite_mode"] for r in self.authored),
                         {"execute": 36, "analysis_error": 4,
                          "input_excluded": 7, "render_unsupported": 3})
        self.assertEqual(schema()["tables"][0]["schema"], "public")
        self.assertTrue(all(t["exposeUnqualified"] is True for t in schema()["tables"]))
        self.assertEqual(self.case("prefix-alias")["sqlite_error"], "table c has 2 values for 1 columns")
        self.assertEqual(self.case("later-name-outer")["expected_rows"], [[2]])
        self.assertEqual(self.case("later-name-outer")["sqlite_expected_rows"], [[3]])
        for name in ("duplicate-labels", "duplicate-aliases"):
            row = self.case(name)
            self.assertEqual([c["name"] for c in row["output_columns"]], ["x", "x"])
            self.assertEqual(row["sqlite_output_names"], ["x", "x:1"])
        self.assertEqual(self.case("varchar-modifier")["expected_rows"], [["abc"]])
        self.assertEqual(self.case("varchar-modifier")["sqlite_expected_rows"], [["abcd"]])
        self.assertEqual(self.case("numeric-modifier")["expected_rows"], [["1.23"]])
        self.assertEqual(self.case("numeric-modifier")["sqlite_expected_rows"], [[1.234]])

    def test_independent_join_bag_and_distinct_pagination_anchors(self):
        # An alternate authored population exercises unmatched rows, duplicate
        # matches, SQL NULL and zero, independently of the persisted seed data.
        altered = {"items": [[8, None, "N"], [9, 0, "Z"], [10, 0, "Q"]],
                   "labels": [[8, "A"], [8, "A"], [11, "B"]]}
        generated = {row["shape"]: row for row in cases(altered)}
        self.assertEqual(generated["coalesced-chain-0"]["expected_rows"], [[8, 0], [9, 0], [10, 0]])
        self.assertEqual(generated["left-on-0"]["expected_rows"],
                         [[8, "A"], [8, "A"], [9, None], [10, None]])
        self.assertEqual(generated["full-using-0"]["expected_rows"],
                         [[8, 8, "A"], [8, 8, "A"], [9, 9, None], [10, 10, None], [11, None, "B"]])
        self.assertEqual(generated["distinct-page-0"]["expected_rows"], [[0]])
        self.assertEqual(self.case("full-using-3")["expected_rows_by_state"]["labels_only"],
                         [[1, None, "A"], [1, None, "B"], [3, None, "C"], [5, None, "E"]])
        self.assertEqual(self.case("empty-body")["expected_rows_by_state"],
                         {state: [] for state in checker.STATES})

    def test_closed_source_registry_has_thirteen_queries_twenty_one_columns(self):
        registry = checker.source_registry()
        self.assertEqual(len(registry), 13)
        columns = [column for output in registry.values() for column in output]
        self.assertEqual((len(columns), Counter(c[1] for c in columns)),
                         (21, {"int32": 15, "text": 2, "bool": 4}))
        self.assertTrue(all(c[2] is False for c in columns))
        eligible = {r["id"] for r in self.sources if r["observed_syntax"]["source_free"]}
        self.assertEqual(eligible, set(registry))
        self.assertEqual(len(self.sources) - len(eligible), 37)
        self.assertTrue(all(r["parameter_types"] is None for r in self.sources))
        self.assertTrue(all(r["raw_sql"] == r["sql"] and not r["transformations"] for r in self.sources))

    def test_registry_rejects_missing_duplicate_reordered_and_wrong_metadata(self):
        for change in ("missing", "duplicate", "order", "id", "name", "type", "nullable", "nullable_int", "extra"):
            data = deepcopy(self.registry)
            if change == "missing":
                data.pop()
            elif change == "duplicate":
                data[1] = deepcopy(data[0])
            elif change == "order":
                data.reverse()
            elif change == "id":
                data[0]["id"] += "-different"
            elif change == "extra":
                data[0]["new_evidence"] = True
            else:
                key = "nullable" if change == "nullable_int" else change
                data[0]["output_columns"][0][key] = {
                    "name": "renamed", "type": "text", "nullable": True, "nullable_int": 0}[change]
            with self.subTest(change=change), patch.object(
                    checker, "FIXTURES", self.fixture_copy(registry=data)), self.assertRaises(AssertionError):
                checker.source_registry()

    def test_loader_rejects_fixture_binding_type_and_source_eligibility_changes(self):
        for change in ("count", "order", "value", "nullable_int", "schema_nullable_int",
                       "schema_exposure_int", "schema_type", "binding", "sqlite_value",
                       "source_count", "source_id", "source_raw", "source_sql_hash",
                       "source_transform", "source_types", "source_free", "source_free_int",
                       "source_parameters"):
            rows, sources, catalog = deepcopy(self.authored), deepcopy(self.sources), schema()
            if change == "count":
                rows.pop()
            elif change == "order":
                rows.reverse()
            elif change == "value":
                rows[0]["expected_rows_by_state"]["empty"] = [[99]]
            elif change == "nullable_int":
                rows[0]["output_columns"][0]["nullable"] = 0
            elif change == "schema_nullable_int":
                catalog["tables"][0]["columns"][0]["nullable"] = 0
            elif change == "schema_exposure_int":
                catalog["tables"][0]["exposeUnqualified"] = 1
            elif change == "schema_type":
                catalog["tables"][0]["columns"][0]["type"] = "text"
            elif change == "binding":
                rows[24]["parameter_values"].reverse()
            elif change == "sqlite_value":
                rows[15]["sqlite_expected_rows_by_state"]["both"] = [[2]]
            elif change == "source_count":
                sources.pop()
            elif change == "source_id":
                sources[1]["id"] = sources[0]["id"]
            elif change == "source_raw":
                sources[0]["raw_sql"] += " "
            elif change == "source_sql_hash":
                sources[0]["sql_sha256"] = "0" * 64
            elif change == "source_transform":
                sources[0]["transformations"] = ["rewrite"]
            elif change == "source_types":
                sources[0]["parameter_types"] = "int"
            elif change in ("source_free", "source_free_int"):
                source = next(r for r in sources if r["observed_syntax"]["source_free"])
                source["observed_syntax"]["source_free"] = False if change == "source_free" else 1
            else:
                source = next(r for r in sources if r["observed_syntax"]["source_free"])
                source["observed_parameter_slots"] = [1]
            with self.subTest(change=change), patch.object(checker, "FIXTURES", self.fixture_copy(
                    rows=rows, sources=sources, catalog=catalog)), self.assertRaises(AssertionError):
                checker.load_cases()

    def test_parameter_collection_counts_definitions_once_and_preserves_slot_identity(self):
        unused, repeated = self.case("unused-parameter"), self.case("repeated-reference")
        ordered, reordered = self.case("lexical-parameters"), self.case("reordered-numbered")
        self.assertEqual(checker.parameters(unused["sql"], "postgres"), [("anonymous", 1), ("anonymous", 2)])
        self.assertEqual(checker.parameters(repeated["sql"], "postgres"), [("anonymous", 1)])
        self.assertEqual(checker.parameters(ordered["sql"], "postgres"),
                         [("anonymous", i) for i in range(1, 7)])
        self.assertEqual(checker.parameters(reordered["sql"], "postgres"), [("numbered", 2), ("numbered", 1)])
        prepared = checker.capture(reordered, reordered["sql"])
        self.assertIn("SELECT $2 AS x", prepared[0])
        self.assertIn("SELECT $1 AS y", prepared[0])
        self.assertIn("EXECUTE cte_parameters (9, 7)", prepared[1])
        self.assertEqual(checker.sqlite_bindings(reordered["sqlite_sql"], reordered["parameter_values"]),
                         {"1": 9, "2": 7})

    def test_contract_requires_exact_declarative_output_evidence(self):
        row = self.case("unknown-null")
        good = {"status": "valid", "assurance": "declarative",
                "profile": check_assurance_cli.PROFILES["contract"], "evidence": "declarative-derivation",
                "catalogUnchanged": True, "typePrecision": "exact",
                "outputColumns": [{k: c[k] for k in ("name", "type", "nullable")}
                                  for c in row["output_columns"]]}
        for change in (None, "status", "assurance", "profile", "evidence",
                       "catalogUnchanged", "typePrecision", "columns", "nullable", "exit"):
            result, code = deepcopy(good), 0
            if change == "exit":
                code = 3
            elif change == "catalogUnchanged":
                result[change] = False
            elif change == "columns":
                result["outputColumns"] = []
            elif change == "nullable":
                result["outputColumns"][0]["nullable"] = False
            elif change:
                result[change] = "weaker"
            with self.subTest(change=change), patch.object(check_assurance_cli, "invoke",
                    return_value=subprocess.CompletedProcess([], code, json.dumps(result), "")):
                if change is None:
                    checker.validity(row)
                else:
                    with self.assertRaises(AssertionError):
                        checker.validity(row)

    def test_native_scripts_cover_all_states_and_exact_prepared_descriptors(self):
        canonical = [r["sql"] for r in self.authored]
        script, expected = checker.postgres_script(self.authored, canonical)
        self.assertEqual(len(expected), 400)
        self.assertEqual(script.count("PREPARE cte_parameters"), 400)
        self.assertEqual(script.splitlines().count("SAVEPOINT cte_case;"), 400)
        self.assertEqual(script.splitlines().count("ROLLBACK TO SAVEPOINT cte_case;"), 400)
        self.assertEqual(script.splitlines().count("RELEASE SAVEPOINT cte_case;"), 400)
        self.assertEqual(script.count("TRUNCATE public.items,public.labels;"), 4)
        self.assertTrue(script.endswith("ROLLBACK;"))
        descriptor_sql, descriptors = checker.describe_script(self.authored, canonical)
        self.assertEqual(len(descriptors), 174)
        self.assertEqual(descriptor_sql.count("\\gdesc"), 100)
        self.assertIn("x|character varying(3)", descriptors)
        self.assertIn("x|numeric(6,2)", descriptors)
        self.assertIn("x|integer[]", descriptors)
        self.assertEqual(descriptors.count("x|character varying(3)"), 2)
        self.assertEqual(descriptors[:4], ["x|integer", "x|integer", "doubled|text", "doubled|text"])
        for helper in (checker.postgres_script, checker.describe_script):
            with self.assertRaises(AssertionError):
                helper(self.authored, canonical[:-1])

    def test_native_rows_reject_missing_extra_wrong_arity_value_null_and_multiplicity(self):
        _, expected = checker.postgres_script(self.authored, [r["sql"] for r in self.authored])
        transcript = native_transcript(expected)
        actual = checker.parse_results(transcript)
        self.assertEqual(checker.validate_native(actual, expected), 400)
        key = next(k for k, (_, rows) in expected.items() if rows)
        null_key = next(k for k, (_, rows) in expected.items() if any(None in r for r in rows))
        for change in ("missing", "extra", "width", "value", "row_missing", "duplicate", "null_text"):
            damaged = deepcopy(actual)
            if change == "missing":
                damaged.pop(key)
            elif change == "extra":
                damaged["unexpected"] = damaged[key]
            elif change == "width":
                width, rows = damaged[key]
                damaged[key] = width + 1, rows
            elif change == "value":
                damaged[key][1][0][0] = "wrong"
            elif change == "row_missing":
                damaged[key][1].pop()
            elif change == "duplicate":
                damaged[key][1].append(deepcopy(damaged[key][1][0]))
            else:
                for row in damaged[null_key][1]:
                    if None in row:
                        row[row.index(None)] = "NULL"
                        break
            with self.subTest(change=change), self.assertRaises(AssertionError):
                checker.validate_native(damaged, expected)
        first = transcript.splitlines()[0]
        with self.assertRaisesRegex(ValueError, "Duplicate case marker"):
            checker.parse_results(transcript + first + '\n"c0"\n')

    def test_analysis_and_planning_states_are_observed_separately(self):
        boundaries = checker.boundary_cases()
        self.assertEqual(len(boundaries), 28)
        sql, states = checker.analysis_script()
        self.assertEqual(len(states), 56)
        self.assertEqual(sql.count("SELECT pg_temp.cte_stage("), 56)
        self.assertIn("IF execute_it THEN EXECUTE 'EXECUTE cte_probe'", sql)
        unused = next(r for r in boundaries if "WITH unused AS (SELECT r.id" in r["sql"])
        used = next(r for r in boundaries if "WITH c AS (SELECT r.id" in r["sql"])
        self.assertEqual((unused["status"], unused["prepare_state"], unused["execute_state"]),
                         ("unsupported", "00000", "00000"))
        self.assertEqual((used["status"], used["prepare_state"], used["execute_state"]),
                         ("unsupported", "00000", "0A000"))
        set_cte = next(r for r in boundaries if "SELECT 1 AS x UNION ALL SELECT 2" in r["sql"])
        self.assertEqual((set_cte["status"], set_cte["prepare_state"], set_cte["execute_state"]),
                         ("valid", "00000", "00000"))
        missing = next(r for r in boundaries if "unused AS (SELECT * FROM absent)" in r["sql"])
        self.assertEqual((missing["prepare_state"], missing["execute_state"]), ("42P01", "42P01"))
        with patch.object(checker, "assert_report") as observed:
            self.assertEqual(checker.boundaries(), 30)
        self.assertEqual(observed.call_count, 30)
        observed.assert_any_call(
            ["--assurance", "contract", "--schema", str(checker.FIXTURES / "schema.json"), set_cte["sql"]],
            "valid", "contract")

    def test_sqlite_exclusion_pairs_require_exact_exit_status_and_diagnostic(self):
        for shape, code, status, exitcode in (
                ("array-null-element", "input.parse", "invalid", 1),
                ("reference-alias", "coverage.sqlite.relation-column-aliases", "unsupported", 3),
                ("qualified-bypass-0", "coverage.sqlite.schema-qualification", "unsupported", 3)):
            row = self.case(shape)
            for change in (None, "exit", "status", "code"):
                report = {"status": status, "diagnostic": {"code": code}}
                result_code = exitcode
                if change == "exit":
                    result_code = 0
                elif change == "status":
                    report["status"] = "rendered"
                elif change == "code":
                    report["diagnostic"]["code"] = "different.boundary"
                with self.subTest(shape=shape, change=change), patch.object(checker, "invoke",
                        return_value=subprocess.CompletedProcess([], result_code, json.dumps(report), "")):
                    if change is None:
                        self.assertIsNone(checker.sqlite_render(row))
                    else:
                        with self.assertRaises(AssertionError):
                            checker.sqlite_render(row)

    def test_sqlite_native_source_oracles_and_rejections_cover_all_four_states(self):
        canonical = [r["sqlite_sql"] if r["sqlite_mode"] in ("execute", "analysis_error") else None
                     for r in self.authored]
        self.assertEqual(checker.sqlite_observations(self.authored, canonical), (288, 32))
        with patch.object(checker.sqlite3, "sqlite_version_info", (3, 38, 5)), self.assertRaises(AssertionError):
            checker.sqlite_observations([], [])
        with self.assertRaises(AssertionError):
            checker.sqlite_observations(self.authored, canonical[:-1])

    def test_sqlite_detects_wrong_binding_order_rows_labels_errors_and_missing_canonical(self):
        cases_ = [
            ("reordered-numbered", "WITH a AS (SELECT ?1 AS x), b AS (SELECT ?2 AS y) SELECT x,y FROM a CROSS JOIN b"),
            ("integer", "SELECT 99 AS x"),
            ("integer", "SELECT 1 AS wrong_label"),
            ("integer", "SELECT 1 AS x WHERE FALSE"),
            ("prefix-alias", "SELECT 1 AS a, 'z' AS y"),
            ("prefix-alias", "SELECT absent FROM missing_relation"),
        ]
        for shape, changed in cases_:
            with self.subTest(shape=shape, sql=changed), self.assertRaises(AssertionError):
                checker.sqlite_observations([self.case(shape)], [changed])
        with self.assertRaises(AssertionError):
            checker.sqlite_observations([self.case("integer")], [None])
        damaged = deepcopy(self.case("integer"))
        damaged["sqlite_expected_rows_by_state"]["both"] = [[1], [1]]
        with self.assertRaises(AssertionError):
            checker.sqlite_observations([damaged], [damaged["sqlite_sql"]])

    def main_mock(self, damage=None):
        rows, sources = deepcopy(self.authored), deepcopy(self.sources)
        for source in sources:
            source["sql"] = "/* SCRAPED_INPUT_NEVER_EXECUTE */ " + source["sql"]
        canonical = [r["sql"] for r in rows]
        _, expected = checker.postgres_script(rows, canonical)
        _, descriptors = checker.describe_script(rows, canonical)
        _, stages = checker.analysis_script()
        transcript = native_transcript(expected)
        if damage == "missing_values":
            expected.pop(next(iter(expected)))
            transcript = native_transcript(expected)
        elif damage == "wrong_value":
            key = next(k for k, (_, values) in expected.items() if values)
            expected[key][1][0][0] = "999"
            transcript = native_transcript(expected)
        elif damage == "missing_descriptor":
            descriptors.pop()
        elif damage == "wrong_descriptor":
            descriptors[0] = "x|bigint"
        elif damage == "renamed_descriptor":
            descriptors[0] = "renamed|integer"
        elif damage == "missing_stage":
            stages.pop()
        elif damage == "wrong_stage":
            stages[0] = "00000"
        replies = iter([transcript, "\n".join(descriptors) + "\n", "\n".join(stages) + "\n", "16.15\n"])
        executed = []

        def run(command, **kwargs):
            executed.append(kwargs.get("input", ""))
            return subprocess.CompletedProcess(command, 0, next(replies), "")

        with patch.object(checker, "load_cases", return_value=(rows, sources)), \
                patch.object(checker, "validity") as authored_checks, \
                patch.object(checker, "assert_report") as original_checks, \
                patch.object(checker, "replay", side_effect=lambda _, sql: {"sql": sql}) as rendered, \
                patch.object(checker, "sqlite_render", return_value=None), \
                patch.object(checker, "sqlite_observations", return_value=(288, 32)), \
                patch.object(checker, "boundaries", return_value=30), \
                patch.object(checker, "connection", return_value=nullcontext(["psql"])), \
                patch.object(checker, "run", side_effect=run), \
                patch("sys.argv", ["check_cte_contract_cli.py", "--local-bin", "/unused"]), \
                redirect_stdout(io.StringIO()):
            checker.main()
            self.assertEqual(authored_checks.call_count, 50)
            self.assertEqual(original_checks.call_count, 13)
            self.assertEqual(rendered.call_count, 200)
            self.assertEqual({call.args[0][-1] for call in original_checks.call_args_list},
                             {s["sql"] for s in sources if s["observed_syntax"]["source_free"]})
        self.assertTrue(executed)
        self.assertTrue(all("SCRAPED_INPUT_NEVER_EXECUTE" not in sql for sql in executed))

    def test_main_never_executes_any_original_source_and_checks_only_fixed_thirteen(self):
        self.main_mock()

    def test_main_rejects_missing_or_wrong_rows_descriptors_and_native_stage_evidence(self):
        for damage in ("missing_values", "wrong_value", "missing_descriptor", "wrong_descriptor",
                       "renamed_descriptor", "missing_stage", "wrong_stage"):
            with self.subTest(damage=damage), self.assertRaises(AssertionError):
                self.main_mock(damage)

    def test_failed_original_certificate_stops_before_native_execution(self):
        with patch.object(checker, "validity"), \
                patch.object(checker, "replay", side_effect=lambda _, sql: {"sql": sql}), \
                patch.object(checker, "sqlite_render", return_value=None), \
                patch.object(checker, "assert_report", side_effect=AssertionError("missing original certificate")), \
                patch.object(checker, "connection") as database, \
                patch("sys.argv", ["check_cte_contract_cli.py", "--local-bin", "/unused"]), \
                self.assertRaisesRegex(AssertionError, "missing original certificate"):
            checker.main()
        database.assert_not_called()


if __name__ == "__main__":
    unittest.main()
