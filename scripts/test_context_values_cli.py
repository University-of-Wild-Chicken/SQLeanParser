"""Protocol regressions for fixed context environments and native NAME evidence."""
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

import check_context_values_cli as checker
from check_postgresql_cli import NULL, marker
from generate_context_value_examples import cases


def transcript(category, fields):
    def field(value):
        return NULL if value is None else '"' + value.replace('"', '""') + '"'
    return "\n".join(line for form in ("source", "postgres") for line in (
        marker(category, 1, True, form), '"value","type"' if len(fields) == 2 else '"observation"',
        ",".join(map(field, fields)))) + "\n"


class ContextValuesCliTests(unittest.TestCase):
    @staticmethod
    def case(shape="schema-keyword"):
        return next(row for row in cases() if row["shape"] == shape)

    def fixtures(self, *, rows=None, sources=None, catalog=None):
        temporary = tempfile.TemporaryDirectory()
        self.addCleanup(temporary.cleanup)
        path = Path(temporary.name)
        if rows is not None:
            (path / "synthetic.json").write_text(json.dumps(rows))
        if sources is not None:
            (path / "concrete.jsonl").write_text("".join(json.dumps(r) + "\n" for r in sources))
        for name, value in (catalog or {}).items():
            (path / name).write_text(json.dumps(value))
        return path

    def test_fifty_authored_cases_keep_exact_name_types_nullable_contexts_and_utf8_limits(self):
        rows, sources = checker.load_cases()
        self.assertEqual(rows, cases())
        self.assertEqual((len(rows), len(sources)), (50, 50))
        self.assertEqual([i for i, row in enumerate(rows, 1) if row["expected_sql_null"]], [13, 16, 49])
        for shape in ("schema-keyword", "schema-call", "qualified-schema-call", "quoted-schema-call"):
            row = self.case(shape)
            self.assertEqual(row["expected_value"], "pg_catalog")
            self.assertEqual(row["output_columns"], [{"name": "v", "type": "name", "nullable": True}])
        byte = self.case("name-byte-limit")
        unicode = self.case("name-unicode-byte-limit")
        self.assertEqual((len(byte["parameter_values"][0]), len(byte["expected_value"])), (70, 63))
        self.assertEqual((len(unicode["parameter_values"][0].encode()), len(unicode["expected_value"].encode())),
                         (80, 62))
        self.assertEqual(unicode["expected_value"], "é" * 31)
        self.assertEqual(self.case("explicit-varchar-cast")["postgres_display_type"], "character varying(3)")
        self.assertEqual(self.case("explicit-char-cast")["postgres_display_type"], "character(12)")

    def test_fixed_source_registries_separate_thirteen_certificates_from_nine_helper_boundaries(self):
        registry, unsupported = checker.source_registry(), checker.unsupported_source_free()
        self.assertEqual((len(registry), sum(map(len, registry.values())), len(unsupported)), (13, 15, 9))
        self.assertFalse(registry.keys() & unsupported)
        _, sources = checker.load_cases()
        self.assertEqual({r["id"] for r in sources if r["observed_syntax"]["source_free"]},
                         registry.keys() | unsupported)
        self.assertEqual(len([r for r in sources if not r["observed_syntax"]["source_free"]]), 28)
        nullable = [column for columns in registry.values() for column in columns if column[2]]
        self.assertEqual(Counter((name, type_) for name, type_, _ in nullable),
                         {("current_schema", "name"): 2, ("is_temp_schema", "bool"): 1})
        self.assertTrue(any(columns == (("coalesce", "name", False),) for columns in registry.values()))

    def test_loader_rejects_missing_duplicate_reordered_or_mistyped_populations(self):
        original, concrete = checker.load_cases()
        for change in ("count", "source_count", "duplicate_id", "duplicate_sql", "source_duplicate",
                       "order", "path", "kind", "type", "nullable", "nullable_int", "name", "arity",
                       "oid", "modifier", "value_bool", "null_state", "null_int", "sqlite", "source_scope",
                       "source_scope_int", "source_id", "unused_binding", "missing_binding",
                       "binding_types", "native_template", "sqlite_template"):
            rows, sources = deepcopy(original), deepcopy(concrete)
            row = rows[0]
            if change == "count":
                rows.pop()
            elif change == "source_count":
                sources.pop()
            elif change.startswith("duplicate_"):
                key = change.removeprefix("duplicate_")
                rows[1][key] = row[key]
            elif change == "source_duplicate":
                sources[1]["sql"] = sources[0]["sql"]
            elif change == "order":
                rows[0], rows[1] = rows[1], rows[0]
            elif change == "path":
                row["search_path"] = "public"
            elif change == "kind":
                row["source_kind"] = "engine-regression"
            elif change in {"type", "nullable", "nullable_int", "name"}:
                key = "nullable" if change == "nullable_int" else change
                row["output_columns"][0][key] = {
                    "type": "text", "nullable": False, "nullable_int": 1, "name": "renamed"}[change]
            elif change == "arity":
                row["output_columns"] *= 2
            elif change == "oid":
                row["postgres_type"] = "text"
            elif change == "modifier":
                rows[22]["postgres_display_type"] = "character varying"
            elif change == "value_bool":
                row["expected_value"] = True
            elif change == "null_state":
                row["expected_value"], row["expected_sql_null"] = None, True
            elif change == "null_int":
                row["expected_sql_null"] = 0
            elif change == "sqlite":
                row["sqlite_supported"] = True
            elif change.startswith("source_scope"):
                sources[0]["observed_syntax"]["source_free"] = True if change == "source_scope" else 0
            elif change == "source_id":
                next(r for r in sources if r["id"] in checker.source_registry())["id"] += "-wrong"
            else:
                row = next(r for r in rows if r["shape"] == "numbered-schemas")
                if change == "unused_binding":
                    row["parameter_values"].append(True)
                elif change == "missing_binding":
                    row["parameter_values"] = []
                elif change == "binding_types":
                    row["parameter_types"] = ""
                elif change == "native_template":
                    row["postgres_input"] = "SELECT current_schemas(FALSE) AS v;"
                else:
                    row["sqlite_input"] = row["sql"]
            with self.subTest(change=change), patch.object(checker, "FIXTURES", self.fixtures(
                    rows=rows, sources=sources)), self.assertRaises(AssertionError):
                checker.load_cases()

    def test_anonymous_and_nullable_parameters_remain_separate_from_context_values(self):
        anonymous = self.case("anonymous-schemas")
        self.assertEqual(checker.parameters(anonymous["sql"], "postgres"), [("anonymous", 1)])
        self.assertEqual(checker.question_parameters(anonymous["sql"]), anonymous["postgres_input"])
        script, _ = checker.describe_script([anonymous], [anonymous["postgres_input"]])
        self.assertIn("PREPARE array_description (bool)", script)
        self.assertIn("current_schemas($1)", script)
        self.assertIn("EXECUTE array_description(TRUE)", script)
        nullable = self.case("nullable-schemas-binding")
        script, expected = checker.describe_script([nullable], [nullable["sql"]])
        self.assertEqual(expected, ["v|name[]"] * 2)
        self.assertIn("EXECUTE array_description(NULL)", script)
        self.assertNotIn("(bool?)", script)

    def test_controlled_search_path_preserves_rollback_and_rejects_missing_transactions(self):
        script = "BEGIN;\nSELECT current_schema();\nROLLBACK;"
        self.assertEqual(checker.controlled_path(script),
                         "BEGIN;\nSET LOCAL search_path=pg_catalog;\nSELECT current_schema();\nROLLBACK;")
        for bad in ("SELECT 1;", "BEGIN;\nSELECT 1;", "BEGIN;\nBEGIN;\nROLLBACK;", "BEGIN;\nCOMMIT;"):
            with self.subTest(script=bad), self.assertRaises(AssertionError):
                checker.controlled_path(bad)

    def test_catalog_observations_pin_functions_btree_operators_casts_and_name_storage(self):
        sql, expected = checker.catalog_script()
        self.assertEqual(expected, [f"{i}|t" for i in range(58)])
        self.assertEqual(sql.count("JOIN pg_catalog.pg_amop"), 18)
        self.assertEqual(sql.count("a.amopopr=o.oprnegate"), 3)
        self.assertIn("'length(bytea,name)'::regprocedure", sql)
        # PostgreSQL marks even length(BYTEA, NAME) STABLE, not IMMUTABLE.
        self.assertEqual(sql.count("p.provolatile='s'"), 7)
        self.assertIn("t.typlen=64 AND NOT t.typbyval", sql)
        self.assertIn("AND NOT t.typispreferred", sql)
        self.assertIn("t.typcollation='\"C\"'::regcollation", sql)
        self.assertIn("a.oid='name[]'::regtype AND a.typelem=t.oid", sql)
        self.assertIn("c.castcontext='a'", sql)
        self.assertIn("c.castcontext='i'", sql)
        for predicate in ("p.proisstrict", "NOT p.proretset", "p.provariadic=0",
                          "p.pronargdefaults=0", "p.prokind='f'"):
            self.assertIn(predicate, sql)

    def test_catalog_fixture_changes_cannot_substitute_another_real_native_declaration(self):
        names = ("function_signatures.json", "operator_signatures.json", "cast_signatures.json")
        original = {name: json.loads((checker.FIXTURES / name).read_text()) for name in names}
        for name in names:
            keys = list(original[name][0])
            for change in ("missing", "duplicate", "extra", *keys):
                catalog = deepcopy(original)
                rows = catalog[name]
                if change == "missing":
                    rows.pop()
                elif change == "duplicate":
                    rows[1] = rows[0]
                elif change == "extra":
                    rows[0]["unchecked"] = True
                else:
                    rows[0][change] = ["integer"] if change == "inputs" else "wrong"
                with self.subTest(name=name, change=change), patch.object(checker, "FIXTURES",
                        self.fixtures(catalog=catalog)), self.assertRaises(AssertionError):
                    checker.catalog_script()

    def test_native_values_distinguish_name_oid_unicode_bytes_and_sql_null(self):
        for row, expected_value in ((self.case(), "pg_catalog"),
                                    (self.case("name-unicode-byte-limit"), "é" * 31),
                                    (self.case("nullif-context"), None)):
            script, expected = checker.database_script([row], [row["postgres_input"]])
            self.assertEqual(checker.validate_results(checker.parse_results(
                transcript("exact_types", [expected_value, "name"])), expected), 2)
            for fields in ([expected_value, "text"], ["NULL", "name"], ["wrong", "name"]):
                with self.subTest(shape=row["shape"], fields=fields), self.assertRaises(AssertionError):
                    checker.validate_results(checker.parse_results(transcript("exact_types", fields)), expected)
            self.assertIn("SET LOCAL statement_timeout = '5s'", script)
        row = self.case()
        _, expected = checker.null_script([row], [row["sql"]])
        self.assertEqual(checker.validate_results(checker.parse_results(
            transcript("json_null", ["false"])), expected), 2)
        with self.assertRaises(AssertionError):
            checker.validate_results(checker.parse_results(transcript("json_null", ["true"])), expected)

    def test_exact_descriptor_labels_include_keyword_spelling_and_retained_cast_typmods(self):
        labels = checker.label_cases()
        self.assertEqual(len(labels), 18)
        script, expected = checker.describe_script(labels, [r["sql"] for r in labels])
        wanted = [
            "current_schema|name", "current_catalog|name", "current_user|name", "user|name",
            "current_role|name", "session_user|name", "system_user|text",
            "current_schema|name", "current_database|name", "current_schemas|name[]",
            "current_user|name", "session_user|name", "system_user|text", "current_schema|text",
            "current_schema|character varying(20)", "coalesce|name", "current_schema|name", "array|name[]"]
        self.assertEqual(expected, [value for item in wanted for value in (item, item)])
        self.assertEqual(script.count("\\gdesc"), 36)
        self.assertNotIn("RETURNS TABLE", script)

    def test_runtime_errors_preserve_order_and_do_not_count_timeouts_as_evidence(self):
        rows = checker.runtime_cases()
        self.assertEqual([r["sqlstate"] for r in rows], ["22021", "22023", "2201B", "22012"])
        self.assertEqual(rows[0]["parameter_types"], "text,text")
        sql, expected = checker.error_script(rows, [r["sql"] for r in rows])
        self.assertEqual(len(expected), 8)
        self.assertEqual(sql.count("RETURN ''unexpected-success''"), 8)
        self.assertEqual(sql.count("RETURN SQLSTATE"), 8)
        self.assertIn("CAST(", sql)
        for helper, population in ((checker.error_script, rows), (checker.describe_script, checker.label_cases()),
                                   (checker.database_script, [self.case()]), (checker.null_script, [self.case()])):
            with self.subTest(helper=helper.__name__), self.assertRaises(AssertionError):
                helper(population, [])

    def test_sqlite_checks_all_fifty_specific_failures_and_rejects_success_evidence(self):
        groups = {
            "context-value": {1, 5, 6, 7, 8, 9, 10, *range(17, 27), *range(28, 39), 49},
            "scalar-function-signatures": {2, 3, 4, 11, 13, 14, 16, 44, 45},
            "input.parse": {12, 15, 40, 41, 42, 43, 46, 47, 48, 50},
            "PostgreSQL-type": {27}, "ILIKE": {39},
        }
        self.assertEqual({k: len(v) for k, v in groups.items()},
                         {"context-value": 29, "scalar-function-signatures": 9,
                          "input.parse": 10, "PostgreSQL-type": 1, "ILIKE": 1})
        for index, row in enumerate(cases(), 1):
            key = next(k for k, indexes in groups.items() if index in indexes)
            expected = ((1, "invalid", key) if key == "input.parse"
                        else (3, "unsupported", "coverage.sqlite." + key))
            self.assertEqual(checker.sqlite_expectation(row), expected)
            code, status, diagnostic = expected
            report = {"status": status, "diagnostic": {"code": diagnostic}, "evidence": "none"}
            with patch.object(checker, "invoke", return_value=subprocess.CompletedProcess(
                    [], code, json.dumps(report), "")) as invoke:
                checker.reject_sqlite(row)
            self.assertEqual(invoke.call_args.kwargs["stdin"], row["sqlite_input"])
            for change in ("code", "status", "diagnostic", "evidence", "sql", "parameterMap", "theorems"):
                bad, exit_code = deepcopy(report), code
                if change == "code":
                    exit_code = 0
                elif change == "status":
                    bad["status"] = "rendered"
                elif change == "diagnostic":
                    bad["diagnostic"]["code"] = "coverage.unrelated"
                elif change == "evidence":
                    bad["evidence"] = "checked-roundtrip"
                else:
                    bad[change] = [] if change != "sql" else row["sql"]
                with self.subTest(index=index, change=change), patch.object(checker, "invoke",
                        return_value=subprocess.CompletedProcess([], exit_code, json.dumps(bad), "")), \
                        self.assertRaises(AssertionError):
                    checker.reject_sqlite(row)

    def test_analysis_parse_errors_invalid_signatures_and_valid_name_controls_are_distinct(self):
        sql, states = checker.analysis_script()
        self.assertEqual(states, ["42883"] * 10 + ["42601"] * 2 + ["00000"] * 3)
        self.assertEqual(sql.count("SELECT pg_temp.context_analysis("), 15)
        self.assertIn("PREPARE context_boundary AS", sql)
        self.assertTrue(sql.endswith("ROLLBACK;"))
        failure = subprocess.CompletedProcess([], 1, json.dumps({
            "status": "invalid", "diagnostic": {"code": "input.parse"}}), "")
        with patch.object(checker, "assert_report") as reports, \
                patch.object(checker, "invoke", return_value=failure) as invoke:
            self.assertEqual(checker.boundaries(), 25)
        self.assertEqual(Counter(c.args[1] for c in reports.call_args_list),
                         {"invalid": 10, "valid": 4, "unsupported": 2, "checked": 1})
        self.assertEqual(len(invoke.call_args_list), 8)
        for status, code, diagnostic in (("rendered", 0, "input.parse"), ("unsupported", 3, "input.parse"),
                                         ("invalid", 1, "coverage.unsupported")):
            report = {"status": status, "diagnostic": {"code": diagnostic}}
            with self.subTest(status=status), patch.object(checker, "assert_report"), \
                    patch.object(checker, "invoke", return_value=subprocess.CompletedProcess(
                        [], code, json.dumps(report), "")), self.assertRaises(AssertionError):
                checker.boundaries()

    def exercise_main(self, *, values=None, nulls=None, errors=None, metadata=None, catalog=None, analysis=None):
        row = self.case()
        registry = checker.source_registry()
        certified = next(key for key, columns in registry.items() if len(columns) == 2)
        sources = [
            {"id": certified, "sql": "SELECT CURRENT_USER, current_database() /* never_execute_source */;"},
            {"id": next(iter(checker.unsupported_source_free())),
             "sql": "SELECT current_user, version() /* never_execute_source */;"},
            {"id": "catalog-dependent", "sql": "SELECT current_user FROM never_execute_source;"},
        ]
        runtime, label = checker.runtime_cases()[0], checker.label_cases()[0]
        values = transcript("exact_types", ["pg_catalog", "name"]) if values is None else values
        nulls = transcript("json_null", ["false"]) if nulls is None else nulls
        errors = transcript("containment_error", ["22021"]) if errors is None else errors
        metadata = "v|name\n" * 2 + "current_schema|name\n" * 2 if metadata is None else metadata
        catalog = "\n".join(checker.catalog_script()[1]) + "\n" if catalog is None else catalog
        analysis = "\n".join(checker.analysis_script()[1]) + "\n" if analysis is None else analysis
        results = [subprocess.CompletedProcess([], 0, value, "") for value in
                   (values, nulls, errors, metadata, catalog, analysis, "16.15\n")]
        with patch.object(checker, "load_cases", return_value=([row], sources)), \
                patch.object(checker, "runtime_cases", return_value=[runtime]), \
                patch.object(checker, "label_cases", return_value=[label]), \
                patch.object(checker, "validity") as validity, \
                patch.object(checker, "assert_report") as certificates, \
                patch.object(checker, "replay", side_effect=lambda mode, sql: {"sql": sql}) as replay, \
                patch.object(checker, "reject_sqlite"), patch.object(checker, "boundaries", return_value=25), \
                patch.object(checker, "connection", return_value=nullcontext(["psql"])), \
                patch.object(checker, "run", side_effect=results) as run, \
                patch("context_values_native_states.check_states", return_value={"state_queries": 10}) as states, \
                patch("sys.argv", ["check_context_values_cli.py", "--dsn", "unused"]), \
                redirect_stdout(io.StringIO()):
            checker.main()
            return run.call_args_list, validity.call_args_list, certificates.call_args_list, replay.call_args_list, states

    def test_pipeline_certifies_fixed_sources_but_never_executes_them_and_runs_native_states(self):
        native, validity, certificates, replays, states = self.exercise_main()
        self.assertEqual((len(native), len(validity), len(certificates)), (7, 3, 2))
        self.assertEqual(certificates[0].args[1:3], ("valid", "contract"))
        self.assertEqual(len(certificates[0].args[3]), 2)
        self.assertEqual(certificates[1].args[1:], ("unsupported", "contract"))
        self.assertEqual(sum("never_execute_source" in c.args[1] for c in replays), 6)
        states.assert_called_once_with(["psql"])
        for index, call in enumerate(native[:6]):
            self.assertEqual(call.kwargs["timeout"], 120)
            self.assertIn("ON_ERROR_STOP=1", call.args[0])
            self.assertNotIn("never_execute_source", call.kwargs["input"])
            if index < 4:
                self.assertIn("SET LOCAL search_path=pg_catalog;", call.kwargs["input"])
                self.assertTrue(call.kwargs["input"].endswith("ROLLBACK;"))

    def test_pipeline_rejects_missing_duplicate_wrong_name_oid_or_null_observations(self):
        good = transcript("exact_types", ["pg_catalog", "name"])
        for value in ("", good + good, transcript("exact_types", ["public", "name"]),
                      transcript("exact_types", [None, "name"]), transcript("exact_types", ["pg_catalog", "text"])):
            with self.subTest(value=value), self.assertRaises((AssertionError, ValueError)):
                self.exercise_main(values=value)
        for nulls in ("", transcript("json_null", ["true"]), transcript("json_null", [None])):
            with self.subTest(nulls=nulls), self.assertRaises(AssertionError):
                self.exercise_main(nulls=nulls)

    def test_pipeline_requires_exact_descriptors_catalog_coverage_and_sqlstates(self):
        for metadata in ("", "v|name\n" * 2, "v|text\n" * 2 + "current_schema|name\n" * 2,
                         "current_schema|name\n" * 2 + "v|name\n" * 2):
            with self.subTest(metadata=metadata), self.assertRaises(AssertionError):
                self.exercise_main(metadata=metadata)
        catalog = checker.catalog_script()[1]
        for changed in ([], catalog[:-1], catalog + [catalog[-1]], list(reversed(catalog)),
                        [*catalog[:-1], "57|f"]):
            with self.subTest(catalog=changed), self.assertRaises(AssertionError):
                self.exercise_main(catalog="\n".join(changed) + "\n")
        for error in ("00000", "unexpected-success", "22023", "57014"):
            with self.subTest(error=error), self.assertRaises(AssertionError):
                self.exercise_main(errors=transcript("containment_error", [error]))
        states = checker.analysis_script()[1]
        for changed in ([], states[:-1], list(reversed(states)), ["00000", *states[1:]],
                        [*states[:10], "42883", *states[11:]], [*states[:-1], "57014"]):
            with self.subTest(analysis=changed), self.assertRaises(AssertionError):
                self.exercise_main(analysis="\n".join(changed) + "\n")


if __name__ == "__main__":
    unittest.main()
