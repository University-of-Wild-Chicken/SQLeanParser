"""Fail-closed certificate, dialect and native observation protocols."""
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
import check_null_predicates_cli as checker
from check_postgresql_cli import NULL, marker
from generate_null_predicate_examples import distinct_cases, null_cases


def transcript(category, fields):
    def field(value):
        return NULL if value is None else '"' + value.replace('"', '""') + '"'
    return "\n".join(line for form in ("source", "postgres") for line in (
        marker(category, 1, True, form), '"value","type"' if len(fields) == 2 else '"observation"',
        ",".join(map(field, fields)))) + "\n"


class NullPredicatesCliTests(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        cls.authored, cls.sources = checker.load_cases()
        cls.registry_data = json.loads((checker.FIXTURES / "null_predicates/source_contracts.json").read_text())

    def fixture_copy(self, *, rows=None, sources=None, registry=None):
        temporary = tempfile.TemporaryDirectory()
        self.addCleanup(temporary.cleanup)
        directory = Path(temporary.name)
        for factor in checker.FACTORS:
            path = directory / factor
            path.mkdir()
            selected = [r for r in (self.authored if rows is None else rows)
                        if r["id"].startswith(factor.replace("_", "-") + "-")]
            originals = [r for r in (self.sources if sources is None else sources) if r["factor"] == factor]
            (path / "synthetic.json").write_text(json.dumps(selected))
            (path / "concrete.jsonl").write_text("".join(json.dumps(r) + "\n" for r in originals))
        (directory / "null_predicates/source_contracts.json").write_text(json.dumps(
            self.registry_data if registry is None else registry))
        return directory

    def case(self, shape):
        return next(row for row in self.authored if row["shape"] == shape)

    def test_two_authored_populations_reproduce_and_separate_noninverse_row_tests(self):
        self.assertEqual(self.authored, distinct_cases() + null_cases())
        self.assertEqual((len(self.authored), len(self.sources)), (100, 100))
        self.assertTrue(all(r["expected_sql_null"] is False for r in self.authored))
        for shape in ("isnull-mixed-row", "notnull-mixed-row"):
            self.assertEqual(self.case(shape)["expected_value"], "false")
        for shape in ("isnull-empty-row", "notnull-empty-row"):
            self.assertEqual(self.case(shape)["expected_value"], "true")
        self.assertEqual(self.case("row-vs-raw-null")["expected_value"], "true")
        self.assertEqual(self.case("row-null-equality")["expected_value"], "false")
        self.assertEqual(sum(r["sqlite_supported"] for r in self.authored), 54)

    def test_exact_six_authored_sqlite_variants_and_independent_dialect_values(self):
        changed = [r for r in self.authored if r["sqlite_supported"] and r["sqlite_sql"] != r["sqlite_input"]]
        self.assertEqual([r["shape"] for r in changed],
                         ["numeric-widths", "float-nan", "char-padding",
                          "not-numeric-widths", "not-float-nan", "not-char-padding"])
        operands = {
            "numeric-widths": ("CAST(1 AS SMALLINT)", "CAST(1 AS BIGINT)"),
            "float-nan": ("CAST('NaN' AS DOUBLE PRECISION)", "CAST('NaN' AS DOUBLE PRECISION)"),
            "char-padding": ("CAST('abc ' AS CHAR(4))", "CAST('abc' AS TEXT)"),
        }
        for row in changed:
            negated = row["shape"].startswith("not-")
            left, right = operands[row["shape"].removeprefix("not-")]
            op = "IS NOT DISTINCT FROM" if negated else "IS DISTINCT FROM"
            self.assertEqual(row["sqlite_sql"], f"SELECT {left} {op} {right} AS v;")
        for shape in ("unknown-integer", "char-padding"):
            self.assertEqual((self.case(shape)["expected_value"], self.case(shape)["sqlite_expected_value"]),
                             ("false", 1))
            self.assertEqual((self.case("not-" + shape)["expected_value"],
                              self.case("not-" + shape)["sqlite_expected_value"]), ("true", 0))

    def test_closed_registry_preserves_all_47_queries_and_59_ordered_columns(self):
        registry = checker.source_registry()
        self.assertEqual({f: len(rs) for f, rs in registry.items()},
                         {"distinct_from": 25, "null_predicates": 22})
        columns = [c for entries in registry.values() for cs in entries.values() for c in cs]
        self.assertEqual((len(columns), Counter(c[1] for c in columns)), (59, {"bool": 57, "varchar": 2}))
        self.assertTrue(all(c[2] is False for c in columns))
        for factor in checker.FACTORS:
            eligible = {r["id"] for r in self.sources if r["factor"] == factor
                        and r["observed_syntax"]["source_free"] and r["source"] != "calcite"}
            self.assertEqual(eligible, registry[factor].keys())
        calcite = next(r for r in self.sources if r["source"] == "calcite")
        self.assertTrue(calcite["observed_syntax"]["source_free"])
        self.assertNotIn(calcite["id"], registry["null_predicates"])

    def test_registry_rejects_missing_duplicate_reordered_unknown_or_renamed_evidence(self):
        for change in ("empty", "missing", "duplicate", "reordered", "unknown", "columns_missing",
                       "label", "type", "nullable", "nullable_int", "extra", "factor"):
            data = deepcopy(self.registry_data)
            rows = data["null_predicates"]
            if change == "empty":
                rows.clear()
            elif change == "missing":
                rows.pop()
            elif change == "duplicate":
                rows[1] = deepcopy(rows[0])
            elif change == "reordered":
                rows.reverse()
            elif change == "unknown":
                rows[0]["id"] += "-changed"
            elif change == "columns_missing":
                rows[0]["output_columns"] = []
            elif change in {"label", "type", "nullable", "nullable_int"}:
                key = "name" if change == "label" else "nullable" if change == "nullable_int" else change
                rows[0]["output_columns"][0][key] = {
                    "label": "changed", "type": "text", "nullable": True, "nullable_int": 0}[change]
            elif change == "extra":
                rows[0]["unchecked"] = True
            else:
                data["extra_factor"] = []
            with self.subTest(change=change), patch.object(checker, "FIXTURES",
                    self.fixture_copy(registry=data)), self.assertRaises(AssertionError):
                checker.source_registry()

    def test_loader_rejects_population_metadata_binding_and_eligibility_mutations(self):
        for change in ("count", "source_count", "duplicate_id", "duplicate_sql", "order", "kind",
                       "name", "type", "nullable", "nullable_int", "value", "null_bit", "oid",
                       "display", "sqlite", "sqlite_value_bool", "sqlite_sql_missing",
                       "native_template", "sqlite_template", "unused_binding", "missing_binding",
                       "binding_types", "source_types", "source_raw", "source_transform",
                       "source_scope", "source_scope_int", "nested_row", "source_id"):
            rows, sources = deepcopy(self.authored), deepcopy(self.sources)
            row = rows[0]
            if change == "count":
                rows.pop()
            elif change == "source_count":
                sources.pop()
            elif change.startswith("duplicate_"):
                rows[1][change.removeprefix("duplicate_")] = row[change.removeprefix("duplicate_")]
            elif change == "order":
                rows[0], rows[1] = rows[1], rows[0]
            elif change == "kind":
                row["source_kind"] = "engine-regression"
            elif change in {"name", "type", "nullable", "nullable_int"}:
                key = "nullable" if change == "nullable_int" else change
                row["output_columns"][0][key] = {
                    "name": "changed", "type": "text", "nullable": True, "nullable_int": 0}[change]
            elif change == "value":
                row["expected_value"] = None
            elif change == "null_bit":
                row["expected_sql_null"] = 0
            elif change in {"oid", "display"}:
                row["postgres_type" if change == "oid" else "postgres_display_type"] = "text"
            elif change == "sqlite":
                row["sqlite_supported"] = False
            elif change == "sqlite_value_bool":
                row["sqlite_expected_value"] = False
            elif change == "sqlite_sql_missing":
                row["sqlite_sql"] = None
            elif change == "native_template":
                rows[6]["postgres_input"] = rows[6]["postgres_input"].replace("$2", "$1")
            elif change == "sqlite_template":
                rows[6]["sqlite_input"] = rows[6]["sqlite_input"].replace("?2", "?1")
            elif change == "unused_binding":
                row["parameter_types"], row["parameter_values"] = "integer", [1]
            elif change == "missing_binding":
                rows[6]["parameter_values"].pop()
            elif change == "binding_types":
                rows[6]["parameter_types"] = "integer"
            elif change == "source_types":
                sources[0]["parameter_types"] = "integer"
            elif change == "source_raw":
                sources[0]["raw_sql"] += " "
            elif change == "source_transform":
                sources[0]["transformations"] = ["rewrite"]
            elif change in {"source_scope", "source_scope_int"}:
                sources[0]["observed_syntax"]["source_free"] = False if change == "source_scope" else 1
            elif change == "nested_row":
                target = next(r for r in sources if r["source"] == "calcite")
                for entry in target["observed_syntax"]["null_predicates"]:
                    entry["nested_row"] = False
            else:
                sources[0]["id"] += "-changed"
            with self.subTest(change=change), patch.object(checker, "FIXTURES",
                    self.fixture_copy(rows=rows, sources=sources)), self.assertRaises(AssertionError):
                checker.load_cases()

    def test_parameter_reordering_anonymous_slots_and_null_values_survive_preparation(self):
        rows = [self.case(shape) for shape in ("reversed-parameters", "anonymous-parameters",
                                               "row-reversed-parameters", "isnull-reversed-parameters")]
        for row in rows:
            expected_style = "anonymous" if row["shape"] == "anonymous-parameters" else "numbered"
            expected_slots = [1, 2] if expected_style == "anonymous" else (
                [2, 1, 1, 2] if row["shape"] == "row-reversed-parameters" else [2, 1])
            self.assertEqual(checker.parameters(row["sql"], "postgres"),
                             [(expected_style, n) for n in expected_slots])
            sql, columns = checker.describe_script([row], [row["postgres_input"]])
            self.assertIn(row["postgres_input"].rstrip(";"), sql)
            self.assertEqual(columns, ["v|boolean"] * 2)
        sql, _ = checker.describe_script([rows[0]], [rows[0]["postgres_input"]])
        self.assertIn("EXECUTE array_description(NULL, 7)", sql)
        self.assertEqual(checker.sqlite_bindings(rows[0]["sqlite_sql"], rows[0]["parameter_values"]),
                         {"1": None, "2": 7})

    def test_contract_evidence_and_nonnullable_boolean_are_mandatory(self):
        row = self.authored[0]
        good = {"status": "valid", "assurance": "declarative",
                "profile": check_assurance_cli.PROFILES["contract"], "evidence": "declarative-derivation",
                "catalogUnchanged": True, "typePrecision": "exact", "outputColumns": row["output_columns"]}
        for change in (None, "status", "evidence", "profile", "catalogUnchanged", "typePrecision",
                       "outputColumns", "nullable_int", "nullable_true", "exit"):
            data, code = deepcopy(good), 0
            if change == "exit":
                code = 3
            elif change == "catalogUnchanged":
                data[change] = False
            elif change == "outputColumns":
                data[change] = {}
            elif change in {"nullable_int", "nullable_true"}:
                data["outputColumns"][0]["nullable"] = 0 if change == "nullable_int" else True
            elif change:
                data[change] = "weaker"
            with self.subTest(change=change), patch.object(check_assurance_cli, "invoke",
                    return_value=subprocess.CompletedProcess([], code, json.dumps(data), "")):
                if change is None:
                    checker.validity(row)
                else:
                    with self.assertRaises(AssertionError):
                        checker.validity(row)

    def test_native_analysis_matrix_keeps_parse_typing_and_runtime_failures_separate(self):
        matrix = checker.type_boundaries()
        self.assertEqual((len(matrix), Counter(r[1] for r in matrix)),
                         (3136, {"invalid": 2820, "valid": 312, "unsupported": 4}))
        self.assertTrue(all("JSON[]" in r[0] and r[2] == "00000" for r in matrix if r[1] == "unsupported"))
        sql, states = checker.analysis_script()
        self.assertEqual(Counter(states), {"00000": 661, "42883": 2823, "42601": 2, "22P02": 1, "22003": 1})
        self.assertEqual(sql.count("SELECT pg_temp.null_analysis("), 3488)
        self.assertIn("PREPARE null_boundary AS", sql)
        self.assertIn("DEALLOCATE null_boundary", sql)
        self.assertTrue(sql.endswith("ROLLBACK;"))
        failures = [r for r in checker.analysis_boundaries() if r[2] in {"22P02", "22003"}]
        self.assertTrue(all(r[1] == "valid" for r in failures))

    def test_postfix_labels_and_nonnull_bits_are_independent_of_operand_nullability(self):
        labels = checker.label_cases()
        self.assertEqual(len(labels), 12)
        sql, expected = checker.describe_script(labels, [r["sql"] for r in labels])
        self.assertEqual(expected, ["?column?|boolean"] * 16 + ["text|text"] * 4
                         + ["case|boolean"] * 2 + ["coalesce|boolean"] * 2)
        self.assertEqual(sql.count("\\gdesc"), 24)
        script, values = checker.null_script(self.authored[:1], [self.authored[0]["sql"]])
        self.assertEqual(len(values), 2)
        self.assertIn("IS NULL", script)

    def test_runtime_observations_do_not_confuse_success_null_and_sqlstate(self):
        errors = checker.runtime_cases()
        self.assertEqual([r["sqlstate"] for r in errors],
                         ["22P02", "22012", "22P02", "22012", "22P02", "2202E", "2202E", "22003"])
        sql, expected = checker.error_script(errors, [r["sql"] for r in errors])
        self.assertEqual(len(expected), 16)
        self.assertEqual(sql.count("RETURN ''unexpected-success''"), 16)
        self.assertEqual(sql.count("RETURN SQLSTATE"), 16)
        for helper, rows in ((checker.error_script, errors), (checker.describe_script, checker.label_cases()),
                             (checker.database_script, self.authored[:1]), (checker.null_script, self.authored[:1])):
            with self.subTest(helper=helper.__name__), self.assertRaises(AssertionError):
                helper(rows, [])

    def test_sqlite_requires_54_successes_and_46_exact_exclusions(self):
        excluded = [r for r in self.authored if not r["sqlite_supported"]]
        self.assertEqual(Counter(checker.sqlite_expectation(r) for r in excluded), {
            (1, "invalid", "input.parse"): 32,
            (3, "unsupported", "coverage.sqlite.PostgreSQL-type"): 14})
        for row in excluded:
            code, status, diagnostic = checker.sqlite_expectation(row)
            good = {"status": status, "diagnostic": {"code": diagnostic}, "evidence": "none"}
            with patch.object(checker, "invoke", return_value=subprocess.CompletedProcess(
                    [], code, json.dumps(good), "")) as invoke:
                self.assertIsNone(checker.sqlite_render(row))
            self.assertEqual(invoke.call_args.kwargs["stdin"], row["sqlite_input"])
            for change in ("exit", "status", "diagnostic", "evidence", "sql", "parameterMap", "theorems"):
                data, exit_ = deepcopy(good), code
                if change == "exit":
                    exit_ = 0
                elif change in {"status", "evidence"}:
                    data[change] = "rendered"
                elif change == "diagnostic":
                    data["diagnostic"]["code"] = "coverage.other"
                else:
                    data[change] = []
                with self.subTest(row=row["id"], change=change), patch.object(checker, "invoke",
                        return_value=subprocess.CompletedProcess([], exit_, json.dumps(data), "")), \
                        self.assertRaises(AssertionError):
                    checker.sqlite_render(row)
        with patch.object(checker, "replay", return_value={"sql": "canonical"}) as replay:
            self.assertEqual(checker.sqlite_render(self.authored[0]), "canonical")
        self.assertEqual(replay.call_args.args, ("sqlite", self.authored[0]["sqlite_input"]))

    def test_sqlite_executes_separate_native_inputs_and_demands_values_labels_and_counts(self):
        rows = [self.case(s) for s in ("unknown-integer", "char-padding")]
        canonical = [r["sqlite_sql"] for r in rows]
        self.assertEqual(checker.sqlite_observations(rows, canonical), 4)
        for change in ("length", "missing", "value", "label"):
            changed = deepcopy(canonical)
            if change == "length":
                changed.pop()
            elif change == "missing":
                changed[0] = None
            elif change == "value":
                changed[0] = "SELECT 0 AS v"
            else:
                changed[0] = "SELECT 1 AS renamed"
            with self.subTest(change=change), self.assertRaises(AssertionError):
                checker.sqlite_observations(rows, changed)

    def test_boundaries_require_exact_outcomes_and_parser_diagnostics(self):
        failure = subprocess.CompletedProcess([], 1, json.dumps({
            "status": "invalid", "diagnostic": {"code": "input.parse"}}), "")
        with patch.object(checker, "assert_report") as reports, \
                patch.object(checker, "invoke", return_value=failure) as invoke:
            self.assertEqual(checker.boundaries(), 3506)
        self.assertEqual(Counter(c.args[1] for c in reports.call_args_list),
                         {"valid": 660, "invalid": 2828, "unsupported": 10})
        self.assertEqual(invoke.call_count, 8)
        for status, exit_, diagnostic in (("rendered", 0, "input.parse"),
                                         ("unsupported", 3, "input.parse"), ("invalid", 1, "coverage.other")):
            with self.subTest(status=status), patch.object(checker, "assert_report"), \
                    patch.object(checker, "invoke", return_value=subprocess.CompletedProcess(
                        [], exit_, json.dumps({"status": status, "diagnostic": {"code": diagnostic}}), "")), \
                    self.assertRaises(AssertionError):
                checker.boundaries()

    def exercise_main(self, *, values=None, nulls=None, errors=None, metadata=None, analysis=None):
        row, runtime, label = self.authored[0], checker.runtime_cases()[0], checker.label_cases()[0]
        eligible_id = next(iter(checker.source_registry()["distinct_from"]))
        sources = [{"id": eligible_id, "sql": "SELECT 1 IS DISTINCT FROM 1 /* never_execute_source */"},
                   {"id": "render_only", "sql": "SELECT value ISNULL FROM never_execute_source"}]
        texts = [
            transcript("exact_types", ["false", "boolean"]) if values is None else values,
            transcript("json_null", ["false"]) if nulls is None else nulls,
            transcript("containment_error", ["22P02"]) if errors is None else errors,
            "v|boolean\n" * 2 + "?column?|boolean\n" * 2 if metadata is None else metadata,
            "\n".join(checker.analysis_script()[1]) + "\n" if analysis is None else analysis,
            "16.15\n",
        ]
        results = [subprocess.CompletedProcess([], 0, text, "") for text in texts]
        with patch.object(checker, "load_cases", return_value=([row], sources)), \
                patch.object(checker, "runtime_cases", return_value=[runtime]), \
                patch.object(checker, "label_cases", return_value=[label]), \
                patch.object(checker, "validity") as validity, patch.object(checker, "assert_report") as certs, \
                patch.object(checker, "replay", side_effect=lambda mode, sql: {"sql": sql}) as replay, \
                patch.object(checker, "sqlite_render", return_value=row["sqlite_sql"]), \
                patch.object(checker, "sqlite_observations", return_value=2), \
                patch.object(checker, "boundaries", return_value=3506), \
                patch.object(checker, "connection", return_value=nullcontext(["psql"])), \
                patch.object(checker, "run", side_effect=results) as run, \
                patch("sys.argv", ["check_null_predicates_cli.py", "--dsn", "unused"]), \
                redirect_stdout(io.StringIO()):
            checker.main()
        return run.call_args_list, validity.call_args_list, certs.call_args_list, replay.call_args_list

    def test_pipeline_never_executes_downloaded_inputs_and_certifies_fixed_columns(self):
        native, validity, certs, replays = self.exercise_main()
        self.assertEqual((len(native), len(validity), len(certs)), (6, 3, 1))
        self.assertEqual(certs[0].args[1:], ("valid", "contract", (("yes", "bool", False),)))
        self.assertEqual(sum("never_execute_source" in c.args[1] for c in replays), 4)
        for call in native[:5]:
            self.assertEqual(call.kwargs["timeout"], 120)
            self.assertIn("ON_ERROR_STOP=1", call.args[0])
            self.assertNotIn("never_execute_source", call.kwargs["input"])

    def test_pipeline_rejects_missing_duplicate_wrong_boolean_and_null_observations(self):
        good = transcript("exact_types", ["false", "boolean"])
        for output in ("", good + good, transcript("exact_types", ["true", "boolean"]),
                       transcript("exact_types", [None, "boolean"]), transcript("exact_types", ["false", "text"])):
            with self.subTest(output=output), self.assertRaises((AssertionError, ValueError)):
                self.exercise_main(values=output)
        for output in ("", transcript("json_null", ["true"]), transcript("json_null", [None])):
            with self.subTest(output=output), self.assertRaises(AssertionError):
                self.exercise_main(nulls=output)

    def test_pipeline_requires_exact_labels_states_and_all_native_analysis_rows(self):
        for metadata in ("", "v|boolean\n" * 2, "v|text\n" * 2 + "?column?|boolean\n" * 2,
                         "?column?|boolean\n" * 2 + "v|boolean\n" * 2):
            with self.subTest(metadata=metadata), self.assertRaises(AssertionError):
                self.exercise_main(metadata=metadata)
        for state in ("00000", "unexpected-success", "22003", "57014"):
            with self.subTest(state=state), self.assertRaises(AssertionError):
                self.exercise_main(errors=transcript("containment_error", [state]))
        states = checker.analysis_script()[1]
        for changed in ([], states[:-1], states + states[:1], ["57014", *states[1:]]):
            with self.subTest(changed_count=len(changed)), self.assertRaises(AssertionError):
                self.exercise_main(analysis="\n".join(changed) + "\n")


if __name__ == "__main__":
    unittest.main()
