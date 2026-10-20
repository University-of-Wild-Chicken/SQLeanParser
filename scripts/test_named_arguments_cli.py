"""Named/default-call protocol checks with independent finite expected evidence."""
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
import check_named_arguments_cli as checker
from check_postgresql_cli import NULL, marker
from generate_named_argument_examples import cases, SIGNATURES


def transcript(category, observations):
    def cell(value):
        return NULL if value is None else '"' + value.replace('"', '""') + '"'
    return "\n".join(line for index, fields in enumerate(observations, 1)
                     for form in ("source", "postgres") for line in (
                         marker(category, index, True, form),
                         '"value","type"' if len(fields) == 2 else '"observation"',
                         ",".join(map(cell, fields)))) + "\n"


class NamedArgumentsCliTests(unittest.TestCase):
    @staticmethod
    def case(shape="all-defaults"):
        return next(row for row in cases() if row["shape"] == shape)

    def fixtures(self, *, rows=None, sources=None, signature=None):
        temporary = tempfile.TemporaryDirectory()
        self.addCleanup(temporary.cleanup)
        path = Path(temporary.name)
        for name, value in (("synthetic.json", rows), ("function_signatures.json", signature)):
            if value is not None:
                (path / name).write_text(json.dumps(value))
        if sources is not None:
            (path / "concrete.jsonl").write_text("".join(json.dumps(r) + "\n" for r in sources))
        return path

    def test_fifty_authored_cases_preserve_exact_types_nulls_and_declared_bindings(self):
        rows, sources = checker.load_cases()
        self.assertEqual(rows, cases())
        self.assertEqual((len(rows), len(sources)), (50, 50))
        self.assertEqual([i for i, r in enumerate(rows, 1) if r["expected_sql_null"]], [42, 43, 49])
        self.assertEqual(self.case("interval-modifier")["postgres_display_type"],
                         "interval day to second(2)")
        self.assertEqual(self.case("numeric-seconds")["expected_value"], "00:00:01.125")
        self.assertEqual(self.case("strict-null-suppresses-infinity")["expected_value"], None)
        self.assertEqual(self.case("nullable-declaration")["parameter_types"], "float8?")

    def test_seven_source_registry_entries_use_only_two_real_interface_declarations(self):
        _, sources = checker.load_cases()
        registry = checker.source_registry()
        self.assertEqual(len(registry), 7)
        self.assertEqual(Counter(e["parameter_types"] for e in registry.values()),
                         {"": 5, "double precision": 1, "integer": 1})
        self.assertEqual(Counter(e["columns"] for e in registry.values()),
                         {(("make_interval", "interval", False),): 6,
                          (("?column?", "bool", False),): 1})
        self.assertEqual(sum(s["observed_syntax"]["source_free"] and s["id"] not in registry
                             for s in sources), 41)
        self.assertEqual(sum(not s["observed_syntax"]["source_free"] and s["id"] not in registry
                             for s in sources), 2)

    def test_loader_rejects_missing_duplicate_mistyped_and_forged_interface_records(self):
        original, concrete = checker.load_cases()
        for change in ("count", "source_count", "duplicate_id", "duplicate_sql", "order",
                       "kind", "name", "type", "nullable", "nullable_int", "arity", "oid",
                       "modifier", "value_type", "null_bit", "null_int", "sqlite", "source_scope",
                       "source_scope_int", "source_id", "raw", "extra_binding", "missing_binding",
                       "binding_types", "native_template", "sqlite_template", "declared_type",
                       "declaration_method", "declaration_hash", "declaration_line",
                       "declaration_sql", "invented_binding"):
            rows, sources = deepcopy(original), deepcopy(concrete)
            row = rows[0]
            bound = next(s for s in sources if s["parameter_types"] == "double precision")
            if change == "count":
                rows.pop()
            elif change == "source_count":
                sources.pop()
            elif change.startswith("duplicate_"):
                key = change.removeprefix("duplicate_")
                rows[1][key] = row[key]
            elif change == "order":
                rows[0], rows[1] = rows[1], rows[0]
            elif change == "kind":
                row["source_kind"] = "engine-regression"
            elif change in {"name", "type", "nullable", "nullable_int"}:
                row["output_columns"][0]["nullable" if change == "nullable_int" else change] = {
                    "name": "renamed", "type": "text", "nullable": True, "nullable_int": 0}[change]
            elif change == "arity":
                row["output_columns"] *= 2
            elif change == "oid":
                row["postgres_type"] = "text"
            elif change == "modifier":
                rows[46]["postgres_display_type"] = "interval"
            elif change == "value_type":
                row["expected_value"] = 0
            elif change == "null_bit":
                row["expected_sql_null"], row["expected_value"] = True, None
            elif change == "null_int":
                row["expected_sql_null"] = 0
            elif change == "sqlite":
                row["sqlite_supported"] = True
            elif change in {"source_scope", "source_scope_int"}:
                sources[0]["observed_syntax"]["source_free"] = False if change == "source_scope" else 1
            elif change == "source_id":
                sources[0]["id"] += "-wrong"
            elif change == "raw":
                sources[0]["raw_sql"] += " "
            elif change == "declared_type":
                bound["parameter_types"] = "integer"
            elif change.startswith("declaration_"):
                key = change.removeprefix("declaration_")
                if key == "sql":
                    bound["sql"] = bound["raw_sql"] = "SELECT make_interval(days => $1);"
                else:
                    bound["parameter_type_provenance"][{"hash": "sha256"}.get(key, key)] = (
                        1 if key == "line" else "wrong")
            elif change == "invented_binding":
                sources[0]["parameter_types"] = "integer"
            else:
                row = next(r for r in rows if r["shape"] == "numbered-reversed-slots")
                if change == "extra_binding":
                    row["parameter_values"].append(1)
                elif change == "missing_binding":
                    row["parameter_values"].pop()
                elif change == "binding_types":
                    row["parameter_types"] = "integer"
                elif change == "native_template":
                    row["postgres_input"] = "SELECT make_interval() AS v;"
                else:
                    row["sqlite_input"] = row["sql"]
            with self.subTest(change=change), patch.object(checker, "FIXTURES",
                    self.fixtures(rows=rows, sources=sources)), self.assertRaises((AssertionError, ValueError)):
                checker.load_cases()

    def test_catalog_checks_exact_names_defaults_types_and_strict_scalar_signature(self):
        sql, expected = checker.function_script()
        self.assertEqual(expected, ["t"])
        for fragment in ("p.pronargs=7", "p.pronargdefaults=7", "p.proisstrict",
                         "p.provolatile='i'", "NOT p.proretset", "p.provariadic=0", "p.prokind='f'",
                         "p.proargnames=ARRAY['years','months','weeks','days','hours','mins','secs']",
                         "pg_get_expr(p.proargdefaults,0)='0, 0, 0, 0, 0, 0, 0.0'",
                         "p.prorettype='interval'::regtype"):
            self.assertIn(fragment, sql)
        for change in ("missing", "duplicate", "name", "names", "inputs", "defaults", "output", "extra"):
            signature = deepcopy(SIGNATURES)
            if change == "missing":
                signature = []
            elif change == "duplicate":
                signature *= 2
            elif change == "extra":
                signature[0]["unchecked"] = True
            else:
                signature[0][change] = ["wrong"] if isinstance(signature[0][change], list) else "wrong"
            with self.subTest(change=change), patch.object(checker, "FIXTURES",
                    self.fixtures(signature=signature)), self.assertRaises(AssertionError):
                checker.function_script()

    def test_all_128_default_subsets_keep_seven_distinct_slots_and_written_reverse_order(self):
        rows = checker.default_cases()
        self.assertEqual(len(rows), len({r["sql"] for r in rows}))
        self.assertEqual(len(rows), 128)
        for mask, row in enumerate(rows):
            expected = [name for i, name in reversed(list(enumerate(checker.NAMES))) if mask & (1 << i)]
            prefix = row["sql"].split(") = INTERVAL", 1)[0]
            written = [part.strip().split(" => ")[0] for part in prefix.split("(", 1)[1].split(",")
                       if part.strip()]
            self.assertEqual(written, expected)
            self.assertEqual(row["expected_value"], "true")
        self.assertIn("INTERVAL '00:00:00'", rows[0]["sql"])
        self.assertIn("INTERVAL '8 days 00:00:00'", rows[12]["sql"])
        self.assertIn("INTERVAL '1 year 1 mon 8 days 01:01:01'", rows[-1]["sql"])

    def test_parameter_order_reuse_and_anonymous_binding_survive_native_preparation(self):
        expected = {
            "numbered-reversed-slots": [("numbered", 2), ("numbered", 1)],
            "anonymous-days-first": [("anonymous", 1), ("anonymous", 2)],
            "anonymous-seconds-first": [("anonymous", 1), ("anonymous", 2)],
            "reused-slot": [("numbered", 1), ("numbered", 1)],
            "numbered-lexical-order": [("numbered", 2), ("numbered", 1)],
        }
        for shape, uses in expected.items():
            row = self.case(shape)
            self.assertEqual(checker.parameters(row["sql"], "postgres"), uses)
            self.assertEqual(checker.question_parameters(row["sql"]), row["postgres_input"])
            script, descriptions = checker.describe_script([row], [row["postgres_input"]])
            self.assertIn(row["postgres_input"].rstrip(";"), script)
            self.assertIn("PREPARE array_description (" + row["parameter_types"] + ")", script)
            self.assertEqual(descriptions, ["v|interval"] * 2)
        script, _ = checker.describe_script([self.case("nullable-declaration")],
                                           [self.case("nullable-declaration")["sql"]])
        self.assertIn("EXECUTE array_description(NULL)", script)
        self.assertNotIn("(float8?)", script)

    def test_validity_demands_exact_evidence_and_output_schema(self):
        row = self.case()
        good = {"status": "valid", "assurance": "declarative",
                "profile": check_assurance_cli.PROFILES["contract"], "evidence": "declarative-derivation",
                "catalogUnchanged": True, "typePrecision": "exact",
                "outputColumns": row["output_columns"]}
        for change in (None, "evidence", "profile", "catalog", "precision", "type", "name", "nullable",
                       "container", "status", "exit"):
            report, code = deepcopy(good), 0
            if change == "exit":
                code = 3
            elif change in {"evidence", "profile", "status"}:
                report[change] = "wrong"
            elif change == "catalog":
                report["catalogUnchanged"] = False
            elif change == "precision":
                report["typePrecision"] = "family"
            elif change == "container":
                report["outputColumns"] = {}
            elif change in {"type", "name", "nullable"}:
                report["outputColumns"][0][change] = 0 if change == "nullable" else "wrong"
            with self.subTest(change=change), patch.object(check_assurance_cli, "invoke",
                    return_value=subprocess.CompletedProcess([], code, json.dumps(report), "")):
                if change is None:
                    checker.validity(row)
                else:
                    with self.assertRaises(AssertionError):
                        checker.validity(row)

    def test_type_and_named_binding_analysis_are_separate_from_runtime_success(self):
        types = checker.type_boundaries()
        self.assertEqual((len(types), Counter(status for _, status, _ in types)),
                         (147, {"valid": 18, "invalid": 129}))
        for name in checker.NAMES:
            allowed = [sql for sql, status, _ in types if f"({name} =>" in sql and status == "valid"]
            self.assertEqual(len(allowed), 6 if name == "secs" else 2)
        sql, states = checker.analysis_script()
        self.assertEqual(len(states), 159)
        self.assertEqual(Counter(states), {"00000": 19, "42883": 135, "42601": 2, "22P02": 2, "22003": 1})
        self.assertIn("PREPARE named_boundary AS", sql)
        self.assertTrue(sql.endswith("ROLLBACK;"))
        self.assertEqual(sql.count("SELECT pg_temp.named_analysis("), 159)

    def test_labels_and_runtime_failures_keep_exact_order_and_error_class(self):
        labels = checker.label_cases()
        _, expected = checker.describe_script(labels, [r["sql"] for r in labels])
        wanted = ["make_interval|interval"] * 5 + ["make_interval|text", "make_interval|interval",
                                                  "coalesce|interval", "array|interval[]", "make_interval|interval"]
        self.assertEqual(expected, [value for item in wanted for value in (item, item)])
        errors = checker.runtime_cases()
        self.assertEqual([r["sqlstate"] for r in errors],
                         ["22008", "22008", "22P02", "22003", "22012", "22P02"])
        self.assertTrue(errors[-1]["output_columns"][0]["nullable"])
        sql, expected = checker.error_script(errors, [r["sql"] for r in errors])
        self.assertEqual(len(expected), 12)
        self.assertEqual(sql.count("RETURN ''unexpected-success''"), 12)
        self.assertEqual(sql.count("RETURN SQLSTATE"), 12)
        for helper, rows in ((checker.error_script, errors), (checker.describe_script, labels),
                             (checker.database_script, [self.case()]), (checker.null_script, [self.case()])):
            with self.subTest(helper=helper.__name__), self.assertRaises(AssertionError):
                helper(rows, [])

    def test_sqlite_checks_eight_function_exclusions_and_42_exact_parse_boundaries(self):
        for index, row in enumerate(cases(), 1):
            expected = ((3, "unsupported", "coverage.sqlite.scalar-function-signatures")
                        if index <= 8 else (1, "invalid", "input.parse"))
            self.assertEqual(checker.sqlite_expectation(row), expected)
            code, status, diagnostic = expected
            good = {"status": status, "diagnostic": {"code": diagnostic}, "evidence": "none"}
            with patch.object(checker, "invoke", return_value=subprocess.CompletedProcess(
                    [], code, json.dumps(good), "")) as invoke:
                checker.reject_sqlite(row)
            self.assertEqual(invoke.call_args.kwargs["stdin"], row["sqlite_input"])
            for change in ("exit", "status", "diagnostic", "evidence", "sql", "parameterMap", "theorems"):
                report, exit_code = deepcopy(good), code
                if change == "exit":
                    exit_code = 0
                elif change in {"status", "evidence"}:
                    report[change] = "rendered"
                elif change == "diagnostic":
                    report["diagnostic"]["code"] = "coverage.unrelated"
                else:
                    report[change] = []
                with self.subTest(index=index, change=change), patch.object(checker, "invoke",
                        return_value=subprocess.CompletedProcess([], exit_code, json.dumps(report), "")), \
                        self.assertRaises(AssertionError):
                    checker.reject_sqlite(row)

    def test_static_boundaries_require_exact_parse_status_and_exit(self):
        failure = subprocess.CompletedProcess([], 1, json.dumps({
            "status": "invalid", "diagnostic": {"code": "input.parse"}}), "")
        with patch.object(checker, "assert_report") as reports, \
                patch.object(checker, "invoke", return_value=failure) as invoke:
            self.assertEqual(checker.boundaries(), 173)
        self.assertEqual(Counter(c.args[1] for c in reports.call_args_list),
                         {"valid": 22, "invalid": 137, "unsupported": 6})
        self.assertEqual(invoke.call_count, 8)
        for status, code, diagnostic in (("rendered", 0, "input.parse"), ("unsupported", 3, "input.parse"),
                                         ("invalid", 1, "coverage.other")):
            with self.subTest(status=status), patch.object(checker, "assert_report"), \
                    patch.object(checker, "invoke", return_value=subprocess.CompletedProcess(
                        [], code, json.dumps({"status": status, "diagnostic": {"code": diagnostic}}), "")), \
                    self.assertRaises(AssertionError):
                checker.boundaries()

    def exercise_main(self, *, values=None, nulls=None, errors=None, metadata=None, catalog=None, analysis=None):
        row, default = self.case(), checker.default_cases()[0]
        registry = checker.source_registry()
        closed = next(key for key, entry in registry.items() if not entry["parameter_types"])
        bound = next(key for key, entry in registry.items() if entry["parameter_types"] == "double precision")
        sources = [{"id": closed, "sql": "SELECT make_interval() /* never_execute_source */",
                    "observed_syntax": {"source_free": True}},
                   {"id": bound, "sql": "SELECT make_interval(secs => $1) /* never_execute_source */",
                    "observed_syntax": {"source_free": False}},
                   {"id": "unregistered", "sql": "SELECT dfunc(a => 1) /* never_execute_source */",
                    "observed_syntax": {"source_free": True}},
                   {"id": "unspecified-input", "sql": "SELECT plus(a => $1) /* never_execute_source */",
                    "observed_syntax": {"source_free": False}}]
        runtime, label = checker.runtime_cases()[0], checker.label_cases()[0]
        values = transcript("exact_types", [["00:00:00", "interval"], ["true", "boolean"]]) if values is None else values
        nulls = transcript("json_null", [["false"], ["false"]]) if nulls is None else nulls
        errors = transcript("containment_error", [["22008"]]) if errors is None else errors
        metadata = ("v|interval\n" * 2 + "v|boolean\n" * 2 + "make_interval|interval\n" * 2
                    if metadata is None else metadata)
        catalog = "t\n" if catalog is None else catalog
        analysis = "\n".join(checker.analysis_script()[1]) + "\n" if analysis is None else analysis
        results = [subprocess.CompletedProcess([], 0, text, "") for text in
                   (values, nulls, errors, metadata, catalog, analysis, "16.15\n")]
        with patch.object(checker, "load_cases", return_value=([row], sources)), \
                patch.object(checker, "default_cases", return_value=[default]), \
                patch.object(checker, "runtime_cases", return_value=[runtime]), \
                patch.object(checker, "label_cases", return_value=[label]), \
                patch.object(checker, "validity") as validity, patch.object(checker, "assert_report") as certs, \
                patch.object(checker, "replay", side_effect=lambda mode, sql: {"sql": sql}) as replay, \
                patch.object(checker, "reject_sqlite"), patch.object(checker, "boundaries", return_value=173), \
                patch.object(checker, "connection", return_value=nullcontext(["psql"])), \
                patch.object(checker, "run", side_effect=results) as run, \
                patch("sys.argv", ["check_named_arguments_cli.py", "--dsn", "unused"]), \
                redirect_stdout(io.StringIO()):
            checker.main()
        return run.call_args_list, validity.call_args_list, certs.call_args_list, replay.call_args_list

    def test_pipeline_certifies_fixed_sources_and_never_sends_them_to_postgresql(self):
        native, validity, certs, replays = self.exercise_main()
        self.assertEqual((len(native), len(validity), len(certs)), (7, 4, 3))
        self.assertEqual([c.args[1] for c in certs], ["valid", "valid", "unsupported"])
        self.assertIn("--param-types", certs[1].args[0])
        self.assertIn("double precision", certs[1].args[0])
        self.assertEqual(sum("never_execute_source" in call.args[1] for call in replays), 8)
        for call in native[:6]:
            self.assertEqual(call.kwargs["timeout"], 120)
            self.assertIn("ON_ERROR_STOP=1", call.args[0])
            self.assertNotIn("never_execute_source", call.kwargs["input"])

    def test_pipeline_rejects_missing_duplicate_values_wrong_oid_nulls_and_error_states(self):
        good = transcript("exact_types", [["00:00:00", "interval"], ["true", "boolean"]])
        for value in ("", good + good,
                      transcript("exact_types", [["wrong", "interval"], ["true", "boolean"]]),
                      transcript("exact_types", [["00:00:00", "text"], ["true", "boolean"]]),
                      transcript("exact_types", [[None, "interval"], ["true", "boolean"]])):
            with self.subTest(value=value), self.assertRaises((AssertionError, ValueError)):
                self.exercise_main(values=value)
        for nulls in ("", transcript("json_null", [["true"], ["false"]])):
            with self.subTest(nulls=nulls), self.assertRaises(AssertionError):
                self.exercise_main(nulls=nulls)
        for state in ("00000", "unexpected-success", "22003", "57014"):
            with self.subTest(state=state), self.assertRaises(AssertionError):
                self.exercise_main(errors=transcript("containment_error", [[state]]))

    def test_pipeline_requires_exact_descriptor_catalog_and_analysis_populations(self):
        for metadata in ("", "v|interval\n" * 2, "v|text\n" * 2 + "v|boolean\n" * 2 + "make_interval|interval\n" * 2):
            with self.subTest(metadata=metadata), self.assertRaises(AssertionError):
                self.exercise_main(metadata=metadata)
        for catalog in ("", "f\n", "t\nt\n"):
            with self.subTest(catalog=catalog), self.assertRaises(AssertionError):
                self.exercise_main(catalog=catalog)
        states = checker.analysis_script()[1]
        for changed in ([], states[:-1], list(reversed(states)), ["57014", *states[1:]]):
            with self.subTest(states=changed), self.assertRaises(AssertionError):
                self.exercise_main(analysis="\n".join(changed) + "\n")


if __name__ == "__main__":
    unittest.main()
