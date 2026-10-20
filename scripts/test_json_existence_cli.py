"""JSONB existence evidence, parameter identity, and source-execution isolation."""
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

import check_json_existence_cli as checker
from check_postgresql_cli import NULL, marker
from generate_json_existence_examples import cases, SIGNATURES


def transcript(category, values):
    def field(value):
        return NULL if value is None else '"' + value.replace('"', '""') + '"'
    lines = []
    for form in ("source", "postgres"):
        lines += [marker(category, 1, True, form),
                  '"value","type"' if len(values) == 2 else '"observation"',
                  ",".join(map(field, values))]
    return "\n".join(lines) + "\n"


class JsonExistenceCliTests(unittest.TestCase):
    @staticmethod
    def case(shape="object-key", kind="key"):
        return next(row for row in cases() if row["shape"] == shape and row["operator_kind"] == kind)

    def fixtures(self, rows=None, sources=None, signatures=None):
        temporary = tempfile.TemporaryDirectory()
        self.addCleanup(temporary.cleanup)
        directory = Path(temporary.name)
        if rows is not None:
            (directory / "synthetic.json").write_text(json.dumps(rows))
        if sources is not None:
            (directory / "concrete.jsonl").write_text("".join(json.dumps(row) + "\n" for row in sources))
        if signatures is not None:
            (directory / "function_signatures.json").write_text(json.dumps(signatures))
        return directory

    def test_frozen_populations_distinguish_outer_null_json_null_and_null_key_members(self):
        rows, sources = checker.load_cases()
        self.assertEqual(rows, cases())
        self.assertEqual((len(rows), len(sources)), (50, 50))
        self.assertEqual(Counter(row["operator_kind"] for row in rows), {"key": 20, "any": 15, "all": 15})
        self.assertEqual(sum(row["expected_sql_null"] for row in rows), 8)
        self.assertEqual(self.case("json-null-value")["expected_value"], "true")
        self.assertEqual(self.case("json-null-subject")["expected_value"], "false")
        self.assertEqual(self.case("scalar-string")["expected_value"], "true")
        for kind in ("any", "all"):
            for shape in ("null-member", "only-null-members"):
                row = self.case(shape, kind)
                self.assertIs(row["expected_sql_null"], False)
                self.assertIs(row["output_columns"][0]["nullable"], False)
            self.assertEqual(self.case("empty-keys", kind)["expected_value"],
                             "true" if kind == "all" else "false")
        for source in sources:
            self.assertEqual(source["sql"], source["raw_sql"])
            self.assertEqual(source["transformations"], [])
            self.assertIsNone(source["parameter_types"])

    def test_source_registry_is_fixed_ordered_and_has_exact_nullable_positions(self):
        registry = checker.source_registry()
        self.assertEqual((len(registry), sum(map(len, registry.values()))), (44, 50))
        self.assertEqual(sum(len(columns) == 2 for columns in registry.values()), 6)
        nullable = {key for key, columns in registry.items() if any(c[2] for c in columns)}
        prefix = "json_existence:materialize:test/sqllogictest/jsonb.slt:sqllogic-query-"
        self.assertEqual(nullable, {prefix + "663", prefix + "668"})
        self.assertTrue(all(name == "?column?" and type_ == "bool" and type(null) is bool
                            for columns in registry.values() for name, type_, null in columns))
        _, sources = checker.load_cases()
        self.assertEqual({source["id"] for source in sources if source["observed_syntax"]["source_free"]},
                         registry.keys())
        self.assertEqual(Counter(source["source"] for source in sources if source["id"] not in registry),
                         {"postgres": 5, "river": 1})

    def test_loader_rejects_population_metadata_binding_or_source_registry_mutations(self):
        original, source = checker.load_cases()
        for mutation in ("missing", "source_missing", "duplicate_id", "duplicate_sql", "source_duplicate",
                         "kind", "name", "type", "nullable", "arity", "oid", "display", "value",
                         "null_nonnull", "null_bool", "source_kind", "sqlite", "extra_binding",
                         "missing_binding", "types", "binding_order", "native_template",
                         "source_scope", "source_scope_bool", "source_id"):
            rows, sources = deepcopy(original), deepcopy(source)
            row = rows[0]
            if mutation == "missing":
                rows.pop()
            elif mutation == "source_missing":
                sources.pop()
            elif mutation.startswith("duplicate_"):
                field = mutation.removeprefix("duplicate_")
                rows[1][field] = rows[0][field]
            elif mutation == "source_duplicate":
                sources[1]["sql"] = sources[0]["sql"]
            elif mutation == "kind":
                row["operator_kind"] = "any"
            elif mutation in {"name", "type", "nullable"}:
                row["output_columns"][0][mutation] = {"name": "wrong", "type": "jsonb", "nullable": 0}[mutation]
            elif mutation == "arity":
                row["output_columns"] *= 2
            elif mutation in {"oid", "display"}:
                row["postgres_type" if mutation == "oid" else "postgres_display_type"] = "text"
            elif mutation == "value":
                row["expected_value"] = True
            elif mutation == "null_nonnull":
                row["expected_value"] = None
                row["expected_sql_null"] = True
            elif mutation == "null_bool":
                row["expected_sql_null"] = 0
            elif mutation == "source_kind":
                row["source_kind"] = "engine-regression"
            elif mutation == "sqlite":
                row["sqlite_supported"] = True
            elif mutation.startswith("source_scope"):
                sources[0]["observed_syntax"]["source_free"] = False if mutation == "source_scope" else 1
            elif mutation == "source_id":
                sources[0]["id"] += "-changed"
            else:
                row = next(row for row in rows if row["shape"] == "reordered-binding")
                if mutation == "extra_binding":
                    row["parameter_values"].append("unused")
                elif mutation == "missing_binding":
                    row["parameter_values"].pop()
                elif mutation == "types":
                    row["parameter_types"] = "jsonb"
                elif mutation == "binding_order":
                    row["sqlite_input"] = "SELECT (?1) ? (?2) AS v;"
                else:
                    row["postgres_input"] = "SELECT ($1) ? ($2) AS v;"
            with self.subTest(mutation=mutation), patch.object(checker, "FIXTURES",
                    self.fixtures(rows, sources)), self.assertRaises(AssertionError):
                checker.load_cases()

    def test_question_operators_never_consume_parameter_ordinals(self):
        expectations = [
            (self.case("anonymous"), [("anonymous", 1), ("anonymous", 2)], "SELECT $1 ? $2 AS v;"),
            (self.case("compact-anonymous"), [("anonymous", 1), ("anonymous", 2)],
             "SELECT CAST($1 AS JSONB)?$2 AS v;"),
            (self.case("repeated-binding"), [("numbered", 1), ("numbered", 1)], None),
            (self.case("reordered-binding"), [("numbered", 2), ("numbered", 1)], None),
        ]
        for row, uses, native in expectations:
            with self.subTest(shape=row["shape"]):
                self.assertEqual(checker.parameters(row["sql"], "postgres"), uses)
                # SQLite rejects this operator family. Its marker scanner is
                # deliberately not treated as a PostgreSQL binding oracle.
                self.assertEqual(row["sqlite_input"], row["sql"].replace("$", "?"))
                self.assertEqual(checker.question_parameters(row["sql"]), native or row["sql"])
        for kind, operator in (("any", "?|"), ("all", "?&")):
            row = self.case("anonymous", kind)
            self.assertEqual(checker.question_parameters(row["sql"]),
                             f"SELECT ($1) {operator} ($2) AS v;")
        self.assertEqual(checker.parameters(self.case("unicode-question-key")["sql"], "postgres"), [])

    def test_native_capture_binds_values_separately_and_preserves_operator_and_slot_order(self):
        row = self.case("reordered-binding")
        script, expected = checker.describe_script([row], [row["sql"]])
        self.assertEqual(expected, ["v|boolean"] * 2)
        self.assertEqual(script.count("SELECT ($2) ? ($1) AS v;"), 2)
        self.assertIn("PREPARE array_description (text,jsonb)", script)
        self.assertIn("""EXECUTE array_description('a', '{"a":1}')""", script)
        anonymous = self.case("compact-anonymous")
        script, _ = checker.database_script([anonymous], [anonymous["postgres_input"]])
        self.assertNotIn("CAST(? AS JSONB)", script)
        self.assertIn("CAST($1 AS JSONB)?$2", script)
        nullable = self.case("nullable-binding", "all")
        script, _ = checker.describe_script([nullable], [nullable["postgres_input"]])
        self.assertIn("PREPARE array_description (jsonb,text[])", script)
        self.assertIn("EXECUTE array_description('{}', NULL)", script)

    def test_native_declarations_include_strict_jsonb_functions_and_point_ambiguity(self):
        script, wanted = checker.operator_script()
        self.assertEqual(wanted, ["0|t", "1|t", "2|t", "3|t"])
        declarations = json.loads((checker.FIXTURES / "function_signatures.json").read_text())
        self.assertEqual(declarations, SIGNATURES)
        self.assertEqual(script.count("SELECT "), 8)
        for line in script.splitlines():
            for clause in ("o.oprnamespace='pg_catalog'::regnamespace",
                           "o.oprresult='boolean'::regtype", "p.prorettype='boolean'::regtype",
                           "p.pronamespace='pg_catalog'::regnamespace", "p.proisstrict",
                           "NOT p.proretset", "p.pronargs=2", "p.provariadic=0",
                           "p.provolatile='i'", "p.prokind='f'"):
                self.assertIn(clause, line)
        self.assertIn("o.oprleft='point'::regtype", script)
        self.assertIn("o.oprright='point'::regtype", script)
        self.assertIn("p.proname='point_vert'", script)
        for mutation in ("missing", "duplicate", "operator", "left", "right", "output", "function"):
            rows = deepcopy(declarations)
            if mutation == "missing":
                rows.pop()
            elif mutation == "duplicate":
                rows[1] = rows[0]
            else:
                rows[0][mutation] = "wrong"
            with self.subTest(mutation=mutation), patch.object(checker, "FIXTURES",
                    self.fixtures(signatures=rows)), self.assertRaises(AssertionError):
                checker.operator_script()

    def test_native_value_and_sql_null_observations_have_independent_exact_oracles(self):
        row = self.case()
        script, expected = checker.database_script([row], [row["sql"]])
        self.assertEqual(checker.validate_results(checker.parse_results(
            transcript("exact_types", ["true", "boolean"])), expected), 2)
        for values in (["false", "boolean"], [None, "boolean"], ["null", "boolean"],
                       ["t", "boolean"], ["true", "jsonb"]):
            with self.subTest(values=values), self.assertRaises(AssertionError):
                checker.validate_results(checker.parse_results(transcript("exact_types", values)), expected)
        null_sql, null_expected = checker.null_script([row], [row["sql"]])
        self.assertEqual(checker.validate_results(checker.parse_results(
            transcript("json_null", ["false"])), null_expected), 2)
        for values in (["true"], [None], ["f"], ["false", "false"]):
            with self.subTest(values=values), self.assertRaises(AssertionError):
                checker.validate_results(checker.parse_results(transcript("json_null", values)), null_expected)
        for command in (script, null_sql):
            self.assertIn("SET LOCAL statement_timeout = '5s'", command)
            self.assertTrue(command.endswith("ROLLBACK;"))

    def test_runtime_errors_remain_distinct_from_static_validity_and_timeouts(self):
        rows = checker.runtime_cases()
        self.assertEqual([row["sqlstate"] for row in rows], ["22P02", "22P05", "22P02", "22P02", "22012"])
        self.assertTrue(all(row["output_columns"][0]["nullable"] is False for row in rows))
        script, expected = checker.error_script(rows, [row["sql"] for row in rows])
        self.assertEqual(len(expected), 10)
        self.assertEqual(script.count("RETURN ''unexpected-success''"), 10)
        self.assertEqual(script.count("RETURN SQLSTATE"), 10)
        self.assertIn("1 / $1", script)
        self.assertIn("SET LOCAL statement_timeout = '5s'", script)
        for function, population in ((checker.database_script, [self.case()]),
                                     (checker.null_script, [self.case()]),
                                     (checker.describe_script, checker.label_cases()),
                                     (checker.error_script, rows)):
            with self.subTest(function=function.__name__), self.assertRaises(AssertionError):
                function(population, [])

    def test_descriptor_labels_nullability_and_precedence_results_remain_separate(self):
        labels = checker.label_cases()
        self.assertEqual(len(labels), 10)
        script, wanted = checker.describe_script(labels, [row["sql"] for row in labels])
        self.assertEqual(wanted, [value for item in (
            "?column?|boolean", "?column?|boolean", "?column?|boolean", "?column?|boolean",
            "?column?|boolean", "bool|boolean", "case|boolean", "?column?|text",
            "?column?|boolean", "?column?|boolean") for value in (item, item)])
        self.assertEqual([r["output_columns"][0]["nullable"] for r in labels],
                         [False, False, False, True, True, False, False, False, False, False])
        self.assertEqual(script.count("\\gdesc"), 20)
        self.assertNotIn("RETURNS TABLE", script)

    def test_sqlite_exclusion_requires_exact_status_code_and_no_success_evidence(self):
        # These closed fixture positions record the native CLI's earlier
        # input-parser boundaries, independently of reject_sqlite's shape rule.
        parse_indexes = {20, *range(21, 30), 31, 32, 33, *range(36, 45), 46, 47, 48}
        self.assertEqual(len(parse_indexes), 25)
        outcomes = Counter()
        for index, row in enumerate(cases(), 1):
            expected = ((1, "invalid", "input.parse") if index in parse_indexes else
                        (3, "unsupported", "coverage.sqlite.json-existence"))
            exit_code, status, diagnostic = expected
            outcomes[status] += 1
            good = {"status": status, "diagnostic": {"code": diagnostic}, "evidence": "none"}
            with self.subTest(index=index), patch.object(checker, "invoke",
                    return_value=subprocess.CompletedProcess([], exit_code, json.dumps(good), "")) as invoke:
                checker.reject_sqlite(row)
            self.assertEqual(invoke.call_args.kwargs["stdin"], row["sqlite_input"])
            for mutation in ("exit", "status", "diagnostic", "opposite", "evidence",
                             "sql", "parameterMap", "theorems"):
                report, code = deepcopy(good), exit_code
                if mutation == "exit":
                    code = 0
                elif mutation == "status":
                    report["status"] = "rendered"
                elif mutation == "diagnostic":
                    report["diagnostic"]["code"] = "coverage.unrelated"
                elif mutation == "opposite":
                    code, report["status"], report["diagnostic"]["code"] = (
                        (3, "unsupported", "coverage.sqlite.json-existence")
                        if index in parse_indexes else (1, "invalid", "input.parse"))
                elif mutation == "evidence":
                    report["evidence"] = "checked-roundtrip"
                else:
                    report[mutation] = [] if mutation != "sql" else row["sql"]
                with self.subTest(index=index, mutation=mutation), patch.object(checker, "invoke",
                        return_value=subprocess.CompletedProcess([], code, json.dumps(report), "")), \
                        self.assertRaises(AssertionError):
                    checker.reject_sqlite(row)
        self.assertEqual(outcomes, {"invalid": 25, "unsupported": 25})

    def test_analysis_distinguishes_point_ambiguity_signature_errors_and_valid_unknown_inputs(self):
        script, states = checker.boundary_script()
        self.assertEqual(states, ["42883"] * 21 + ["42725"] * 4 + ["00000"] * 6 + ["42883"])
        self.assertEqual(script.count("SELECT pg_temp.existence_analysis("), 32)
        self.assertIn("PREPARE existence_boundary AS", script)
        self.assertNotIn("EXPLAIN EXECUTE", script)
        self.assertTrue(script.endswith("ROLLBACK;"))
        parse_failure = subprocess.CompletedProcess([], 1, json.dumps({
            "status": "invalid", "diagnostic": {"code": "input.parse"}}), "")
        with patch.object(checker, "assert_report") as report, \
                patch.object(checker, "invoke", return_value=parse_failure) as invoke:
            self.assertEqual(checker.boundaries(), 45)
        self.assertEqual(Counter(call.args[1] for call in report.call_args_list),
                         {"invalid": 26, "valid": 6, "unsupported": 2, "rejected": 1})
        self.assertEqual(len(invoke.call_args_list), 10)
        for code, status, diagnostic in ((3, "unsupported", "input.parse"), (1, "invalid", "coverage.other"),
                                         (0, "rendered", "input.parse")):
            result = subprocess.CompletedProcess([], code, json.dumps({
                "status": status, "diagnostic": {"code": diagnostic}}), "")
            with self.subTest(status=status), patch.object(checker, "assert_report"), \
                    patch.object(checker, "invoke", return_value=result), self.assertRaises(AssertionError):
                checker.boundaries()

    def exercise_main(self, *, values=None, nulls=None, errors=None, metadata=None,
                      operators=None, analysis=None, rendered=None):
        row = self.case()
        registry = checker.source_registry()
        certified_id = next(key for key, columns in registry.items() if len(columns) == 2)
        sources = [
            {"id": certified_id, "sql": "SELECT '{}'::JSONB ? 'x', '{}'::JSONB ? 'y' /* never_execute_source */;"},
            {"id": "render-only-source", "sql": "SELECT j ? 'x' FROM never_execute_table;"},
        ]
        runtime, label = checker.runtime_cases()[0], checker.label_cases()[0]
        values = transcript("exact_types", ["true", "boolean"]) if values is None else values
        nulls = transcript("json_null", ["false"]) if nulls is None else nulls
        errors = transcript("containment_error", ["22P02"]) if errors is None else errors
        metadata = "v|boolean\n" * 2 + "?column?|boolean\n" * 2 if metadata is None else metadata
        operators = "0|t\n1|t\n2|t\n3|t\n" if operators is None else operators
        analysis = "\n".join(checker.boundary_script()[1]) + "\n" if analysis is None else analysis
        results = [subprocess.CompletedProcess([], 0, text, "") for text in
                   (values, nulls, errors, metadata, operators, analysis, "16.15\n")]
        with patch.object(checker, "load_cases", return_value=([row], sources)), \
                patch.object(checker, "runtime_cases", return_value=[runtime]), \
                patch.object(checker, "label_cases", return_value=[label]), \
                patch.object(checker, "validity") as validity, \
                patch.object(checker, "assert_report") as certificates, \
                patch.object(checker, "replay", side_effect=lambda profile, sql: {
                    "sql": rendered if rendered is not None and profile == "postgres" else sql}) as replay, \
                patch.object(checker, "reject_sqlite") as excluded, \
                patch.object(checker, "boundaries", return_value=45), \
                patch.object(checker, "connection", return_value=nullcontext(["psql"])), \
                patch.object(checker, "run", side_effect=results) as run, \
                patch("sys.argv", ["check_json_existence_cli.py", "--dsn", "unused"]), \
                redirect_stdout(io.StringIO()):
            checker.main()
            return run.call_args_list, validity.call_args_list, certificates.call_args_list, replay.call_args_list

    def test_pipeline_certifies_fixed_source_metadata_but_executes_only_authored_sql(self):
        calls, validity, certificates, replays = self.exercise_main()
        self.assertEqual((len(calls), len(validity), len(certificates)), (7, 3, 1))
        self.assertEqual(certificates[0].args[1:],
                         ("valid", "contract", (("?column?", "bool", False), ("?column?", "bool", False))))
        self.assertEqual(sum("never_execute" in call.args[1] for call in replays), 4)
        for call in calls[:6]:
            self.assertEqual(call.kwargs["timeout"], 120)
            self.assertIn("ON_ERROR_STOP=1", call.args[0])
            self.assertNotIn("never_execute", call.kwargs["input"])
        with self.assertRaises(AssertionError):
            self.exercise_main(rendered="SELECT ? ? ? AS v;")

    def test_pipeline_rejects_missing_duplicate_wrong_boolean_or_oid_observations(self):
        good = transcript("exact_types", ["true", "boolean"])
        for values in ("", good + good, transcript("exact_types", ["false", "boolean"]),
                       transcript("exact_types", [None, "boolean"]), transcript("exact_types", ["true", "jsonb"])):
            with self.subTest(values=values), self.assertRaises((AssertionError, ValueError)):
                self.exercise_main(values=values)
        for nulls in ("", transcript("json_null", ["true"]), transcript("json_null", [None]),
                      transcript("json_null", ["false"]) * 2):
            with self.subTest(nulls=nulls), self.assertRaises((AssertionError, ValueError)):
                self.exercise_main(nulls=nulls)

    def test_pipeline_requires_exact_metadata_and_all_four_catalog_observations(self):
        for metadata in ("", "v|boolean\n" * 2, "v|jsonb\n" * 2 + "?column?|boolean\n" * 2,
                         "?column?|boolean\n" * 2 + "v|boolean\n" * 2,
                         "v|boolean\n" * 2 + "renamed|boolean\n" * 2):
            with self.subTest(metadata=metadata), self.assertRaises(AssertionError):
                self.exercise_main(metadata=metadata)
        for operators in ("", "0|t\n1|t\n2|t\n", "0|t\n1|t\n2|t\n3|f\n",
                          "0|t\n1|t\n2|t\n3|t\n3|t\n", "3|t\n2|t\n1|t\n0|t\n"):
            with self.subTest(operators=operators), self.assertRaises(AssertionError):
                self.exercise_main(operators=operators)

    def test_pipeline_rejects_wrong_runtime_states_and_analysis_ambiguity_or_timeout(self):
        for errors in ("", transcript("containment_error", ["00000"]),
                       transcript("containment_error", ["unexpected-success"]),
                       transcript("containment_error", ["57014"]), transcript("containment_error", ["22P05"])):
            with self.subTest(errors=errors), self.assertRaises(AssertionError):
                self.exercise_main(errors=errors)
        states = checker.boundary_script()[1]
        bad = [[], states[:-1], states + [states[0]], list(reversed(states))]
        for index, state in ((0, "00000"), (21, "42883"), (21, "00000"), (25, "42725"), (31, "57014")):
            changed = states.copy()
            changed[index] = state
            bad.append(changed)
        for analysis in bad:
            with self.subTest(analysis=analysis), self.assertRaises(AssertionError):
                self.exercise_main(analysis="\n".join(analysis) + "\n")


if __name__ == "__main__":
    unittest.main()
