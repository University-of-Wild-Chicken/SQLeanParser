"""Finite LEFT/RIGHT native observations, bindings and certificate protocol."""
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
import check_keyword_functions_cli as checker
from check_postgresql_cli import NULL, marker
from generate_keyword_function_examples import cases, SIGNATURES


def transcript(category, fields):
    def field(value):
        return NULL if value is None else '"' + value.replace('"', '""') + '"'
    return "\n".join(line for form in ("source", "postgres") for line in (
        marker(category, 1, True, form), '"value","type"' if len(fields) == 2 else '"observation"',
        ",".join(map(field, fields)))) + "\n"


class KeywordFunctionsCliTests(unittest.TestCase):
    @staticmethod
    def case(shape="left-ascii"):
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

    def test_fifty_authored_values_keep_padding_unicode_and_nulls_distinct(self):
        rows, sources = checker.load_cases()
        self.assertEqual(rows, cases())
        self.assertEqual((len(rows), len(sources)), (50, 50))
        self.assertEqual([i for i, r in enumerate(rows, 1) if r["expected_sql_null"]],
                         [*range(15, 20), *range(40, 45)])
        self.assertEqual(self.case("left-unicode")["expected_value"], "é😀")
        self.assertEqual(self.case("right-unicode")["expected_value"], "bc")
        self.assertEqual(self.case("left-combining-codepoints")["expected_value"], "e")
        self.assertEqual(self.case("left-char-padding")["expected_value"], "a")
        self.assertEqual(self.case("left-varchar-padding")["expected_value"], "a ")
        self.assertEqual(self.case("right-varchar-padding")["expected_value"], "  ")
        self.assertEqual(self.case("left-zero")["expected_value"], "")
        self.assertIsNone(self.case("left-null-subject")["expected_value"])
        self.assertTrue(all("-2147483648" not in row["sql"] for row in rows))

    def test_closed_source_registry_does_not_invent_river_catalog_or_parameters(self):
        _, sources = checker.load_cases()
        registry = checker.source_registry()
        self.assertEqual((len(registry), sum(map(len, registry.values()))), (49, 50))
        self.assertEqual(sum(column[2] for columns in registry.values() for column in columns), 4)
        self.assertEqual({r["id"] for r in sources}, registry.keys() | {checker.external_source_id()})
        external = next(r for r in sources if r["id"] == checker.external_source_id())
        self.assertIsNone(external["parameter_types"])
        self.assertFalse(external["observed_syntax"]["source_free"])
        self.assertEqual(external["observed_parameter_slots"], [1, 2])
        self.assertEqual(checker.parameters(external["sql"], "postgres"),
                         [("numbered", 1), ("numbered", 2), ("numbered", 1), ("numbered", 1)])

    def test_loader_rejects_population_schema_binding_and_source_metadata_mutations(self):
        original, concrete = checker.load_cases()
        for change in ("count", "source_count", "duplicate_id", "duplicate_sql", "source_id", "order",
                       "kind", "name", "type", "nullable", "nullable_int", "arity", "oid", "display",
                       "value_type", "null_bit", "null_int", "sqlite", "source_scope", "source_scope_int",
                       "source_types", "source_raw", "source_transform", "unused_binding", "missing_binding",
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
            elif change == "source_id":
                sources[0]["id"] += "-unknown"
            elif change == "order":
                rows[0], rows[1] = rows[1], rows[0]
            elif change == "kind":
                row["source_kind"] = "engine-regression"
            elif change in {"name", "type", "nullable", "nullable_int"}:
                key = "nullable" if change == "nullable_int" else change
                row["output_columns"][0][key] = {
                    "name": "renamed", "type": "name", "nullable": True, "nullable_int": 0}[change]
            elif change == "arity":
                row["output_columns"] *= 2
            elif change in {"oid", "display"}:
                row["postgres_type" if change == "oid" else "postgres_display_type"] = "name"
            elif change == "value_type":
                row["expected_value"] = 1
            elif change == "null_bit":
                row["expected_value"], row["expected_sql_null"] = None, True
            elif change == "null_int":
                row["expected_sql_null"] = 0
            elif change == "sqlite":
                row["sqlite_supported"] = True
            elif change in {"source_scope", "source_scope_int"}:
                sources[0]["observed_syntax"]["source_free"] = False if change == "source_scope" else 1
            elif change == "source_types":
                sources[0]["parameter_types"] = "text"
            elif change == "source_raw":
                sources[0]["raw_sql"] += " "
            elif change == "source_transform":
                sources[0]["transformations"] = ["rename"]
            else:
                row = next(r for r in rows if r["shape"] == "left-numbered-reversed")
                if change == "unused_binding":
                    row["parameter_values"].append(1)
                elif change == "missing_binding":
                    row["parameter_values"].pop()
                elif change == "binding_types":
                    row["parameter_types"] = "integer"
                elif change == "native_template":
                    row["postgres_input"] = "SELECT left('changed',1) AS v;"
                else:
                    row["sqlite_input"] = row["sql"]
            with self.subTest(change=change), patch.object(checker, "FIXTURES",
                    self.fixtures(rows=rows, sources=sources)), self.assertRaises(AssertionError):
                checker.load_cases()

    def test_native_catalog_requires_exact_binary_strict_nonnamed_scalar_declarations(self):
        sql, expected = checker.function_script()
        self.assertEqual(expected, ["0|t", "1|t"])
        for name in ("left", "right"):
            self.assertIn(f"'pg_catalog.{name}(text,integer)'::regprocedure", sql)
        for condition in ("p.pronargs=2", "p.prorettype='text'::regtype", "p.proisstrict",
                          "p.proargnames IS NULL", "p.pronargdefaults=0", "p.provariadic=0",
                          "p.provolatile='i'", "p.prokind='f'", "NOT p.proretset"):
            self.assertEqual(sql.count(condition), 2)
        for change in ("missing", "duplicate", "order", "name", "inputs", "output", "extra"):
            signature = deepcopy(SIGNATURES)
            if change == "missing":
                signature.pop()
            elif change == "duplicate":
                signature[1] = signature[0]
            elif change == "order":
                signature.reverse()
            elif change == "extra":
                signature[0]["unchecked"] = True
            else:
                signature[0][change] = ["text", "bigint"] if change == "inputs" else "wrong"
            with self.subTest(change=change), patch.object(checker, "FIXTURES",
                    self.fixtures(signature=signature)), self.assertRaises(AssertionError):
                checker.function_script()

    def test_parameter_lexical_order_and_native_values_survive_preparation(self):
        for function in ("left", "right"):
            reversed_ = self.case(function + "-numbered-reversed")
            anonymous = self.case(function + "-anonymous")
            self.assertEqual(checker.parameters(reversed_["sql"], "postgres"),
                             [("numbered", 2), ("numbered", 1)])
            self.assertEqual(checker.parameters(anonymous["sql"], "postgres"),
                             [("anonymous", 1), ("anonymous", 2)])
            for row in (reversed_, anonymous):
                self.assertEqual(checker.question_parameters(row["sql"]), row["postgres_input"])
                sql, expected = checker.describe_script([row], [row["postgres_input"]])
                self.assertIn(row["postgres_input"].rstrip(";"), sql)
                self.assertIn("PREPARE array_description (" + row["parameter_types"] + ")", sql)
                self.assertEqual(expected, ["v|text"] * 2)
        row = self.case("left-nullable-count")
        sql, _ = checker.describe_script([row], [row["postgres_input"]])
        self.assertIn("PREPARE array_description (integer,text)", sql)
        self.assertIn("EXECUTE array_description(NULL, 'abc')", sql)

    def test_contract_protocol_cannot_accept_weaker_evidence_or_equal_integer_nullable(self):
        row = self.case()
        good = {"status": "valid", "assurance": "declarative",
                "profile": check_assurance_cli.PROFILES["contract"], "evidence": "declarative-derivation",
                "catalogUnchanged": True, "typePrecision": "exact", "outputColumns": row["output_columns"]}
        for mutation in (None, "evidence", "profile", "catalogUnchanged", "typePrecision",
                         "outputColumns", "type", "nullable", "exit"):
            report, code = deepcopy(good), 0
            if mutation == "exit":
                code = 3
            elif mutation == "catalogUnchanged":
                report[mutation] = False
            elif mutation == "outputColumns":
                report[mutation] = {}
            elif mutation in {"type", "nullable"}:
                report["outputColumns"][0][mutation] = "name" if mutation == "type" else 0
            elif mutation:
                report[mutation] = "weaker"
            with self.subTest(mutation=mutation), patch.object(check_assurance_cli, "invoke",
                    return_value=subprocess.CompletedProcess([], code, json.dumps(report), "")):
                if mutation is None:
                    checker.validity(row)
                else:
                    with self.assertRaises(AssertionError):
                        checker.validity(row)

    def test_exact_type_matrix_preserves_two_input_positions_and_cast_boundaries(self):
        matrix = checker.type_boundaries()
        self.assertEqual((len(matrix), Counter(status for _, status, _ in matrix)),
                         (1250, {"valid": 16, "invalid": 1234}))
        allowed = [sql for sql, status, _ in matrix if status == "valid"]
        self.assertEqual(sum("AS NAME)" in sql for sql in allowed), 4)
        self.assertTrue(all("AS INTEGER)" in sql or "AS SMALLINT)" in sql for sql in allowed))
        self.assertTrue(all("AS BIGINT)" not in sql for sql in allowed))
        sql, states = checker.analysis_script()
        self.assertEqual(len(states), 1266)
        self.assertEqual(Counter(states), {"00000": 22, "42883": 1240, "22P02": 2, "22003": 2})
        self.assertEqual(sql.count("SELECT pg_temp.keyword_analysis("), 1266)
        self.assertIn("PREPARE keyword_boundary AS", sql)
        self.assertTrue(sql.endswith("ROLLBACK;"))

    def test_labels_retain_case_else_preference_and_explicit_typmods(self):
        labels = checker.label_cases()
        self.assertEqual(len(labels), 12)
        sql, expected = checker.describe_script(labels, [r["sql"] for r in labels])
        wanted = [value for name in ("left", "right") for value in (
            name + "|text", name + "|text", name + "|character varying(2)",
            "case|text", name + "|text", "coalesce|text")]
        self.assertEqual(expected, [value for item in wanted for value in (item, item)])
        self.assertEqual(sql.count("\\gdesc"), 24)
        self.assertNotIn("RETURNS TABLE", sql)

    def test_runtime_null_arguments_do_not_hide_errors_in_other_arguments(self):
        errors = checker.runtime_cases()
        self.assertEqual([r["sqlstate"] for r in errors],
                         ["22P02", "22003", "22012", "22P02"] * 2)
        self.assertEqual([r["output_columns"][0]["nullable"] for r in errors],
                         [False, False, False, True] * 2)
        sql, expected = checker.error_script(errors, [r["sql"] for r in errors])
        self.assertEqual(len(expected), 16)
        self.assertEqual(sql.count("RETURN ''unexpected-success''"), 16)
        self.assertEqual(sql.count("RETURN SQLSTATE"), 16)
        for helper, rows in ((checker.error_script, errors), (checker.describe_script, checker.label_cases()),
                             (checker.database_script, [self.case()]), (checker.null_script, [self.case()])):
            with self.subTest(helper=helper.__name__), self.assertRaises(AssertionError):
                helper(rows, [])

    def test_sqlite_requires_48_parse_boundaries_and_two_specific_qualified_exclusions(self):
        for index, row in enumerate(cases(), 1):
            expected = ((3, "unsupported", "coverage.sqlite.scalar-function-signatures")
                        if index in {24, 49} else (1, "invalid", "input.parse"))
            self.assertEqual(checker.sqlite_expectation(row), expected)
            code, status, diagnostic = expected
            good = {"status": status, "diagnostic": {"code": diagnostic}, "evidence": "none"}
            with patch.object(checker, "invoke", return_value=subprocess.CompletedProcess(
                    [], code, json.dumps(good), "")) as invoke:
                checker.reject_sqlite(row)
            self.assertEqual(invoke.call_args.kwargs["stdin"], row["sqlite_input"])
            for mutation in ("exit", "status", "diagnostic", "evidence", "sql", "parameterMap", "theorems"):
                bad, exit_code = deepcopy(good), code
                if mutation == "exit":
                    exit_code = 0
                elif mutation in {"status", "evidence"}:
                    bad[mutation] = "rendered"
                elif mutation == "diagnostic":
                    bad["diagnostic"]["code"] = "coverage.unrelated"
                else:
                    bad[mutation] = []
                with self.subTest(index=index, mutation=mutation), patch.object(checker, "invoke",
                        return_value=subprocess.CompletedProcess([], exit_code, json.dumps(bad), "")), \
                        self.assertRaises(AssertionError):
                    checker.reject_sqlite(row)

    def test_boundary_classification_requires_exact_parser_status_and_exit(self):
        failure = subprocess.CompletedProcess([], 1, json.dumps({
            "status": "invalid", "diagnostic": {"code": "input.parse"}}), "")
        with patch.object(checker, "assert_report") as reports, \
                patch.object(checker, "invoke", return_value=failure) as invoke:
            self.assertEqual(checker.boundaries(), 1279)
        self.assertEqual(Counter(c.args[1] for c in reports.call_args_list),
                         {"valid": 26, "invalid": 1240, "unsupported": 7})
        self.assertEqual(invoke.call_count, 6)
        for status, code, diagnostic in (("rendered", 0, "input.parse"), ("unsupported", 3, "input.parse"),
                                         ("invalid", 1, "coverage.other")):
            with self.subTest(status=status), patch.object(checker, "assert_report"), \
                    patch.object(checker, "invoke", return_value=subprocess.CompletedProcess(
                        [], code, json.dumps({"status": status, "diagnostic": {"code": diagnostic}}), "")), \
                    self.assertRaises(AssertionError):
                checker.boundaries()

    def exercise_main(self, *, values=None, nulls=None, errors=None, metadata=None, catalog=None, analysis=None):
        row, runtime, label = self.case(), checker.runtime_cases()[0], checker.label_cases()[0]
        registry = checker.source_registry()
        pg = next(key for key, columns in registry.items() if len(columns) == 2)
        sources = [{"id": pg, "sql": "SELECT left('x',1),right('x',1) /* never_execute_source */"},
                   {"id": checker.external_source_id(), "sql": "SELECT left(name,1) FROM never_execute_source"}]
        values = transcript("exact_types", ["ab", "text"]) if values is None else values
        nulls = transcript("json_null", ["false"]) if nulls is None else nulls
        errors = transcript("containment_error", ["22P02"]) if errors is None else errors
        metadata = "v|text\n" * 2 + "left|text\n" * 2 if metadata is None else metadata
        catalog = "0|t\n1|t\n" if catalog is None else catalog
        analysis = "\n".join(checker.analysis_script()[1]) + "\n" if analysis is None else analysis
        results = [subprocess.CompletedProcess([], 0, text, "") for text in
                   (values, nulls, errors, metadata, catalog, analysis, "16.15\n")]
        with patch.object(checker, "load_cases", return_value=([row], sources)), \
                patch.object(checker, "runtime_cases", return_value=[runtime]), \
                patch.object(checker, "label_cases", return_value=[label]), \
                patch.object(checker, "validity") as validity, patch.object(checker, "assert_report") as certs, \
                patch.object(checker, "replay", side_effect=lambda mode, sql: {"sql": sql}) as replay, \
                patch.object(checker, "reject_sqlite"), patch.object(checker, "boundaries", return_value=1279), \
                patch.object(checker, "connection", return_value=nullcontext(["psql"])), \
                patch.object(checker, "run", side_effect=results) as run, \
                patch("sys.argv", ["check_keyword_functions_cli.py", "--dsn", "unused"]), \
                redirect_stdout(io.StringIO()):
            checker.main()
        return run.call_args_list, validity.call_args_list, certs.call_args_list, replay.call_args_list

    def test_pipeline_executes_only_authored_sql_and_certifies_ordered_source_columns(self):
        native, validity, certs, replays = self.exercise_main()
        self.assertEqual((len(native), len(validity), len(certs)), (7, 3, 1))
        self.assertEqual(certs[0].args[1:3], ("valid", "contract"))
        self.assertEqual(certs[0].args[3], (("left", "text", False), ("right", "text", False)))
        self.assertEqual(sum("never_execute_source" in call.args[1] for call in replays), 4)
        for call in native[:6]:
            self.assertEqual(call.kwargs["timeout"], 120)
            self.assertIn("ON_ERROR_STOP=1", call.args[0])
            self.assertNotIn("never_execute_source", call.kwargs["input"])

    def test_pipeline_rejects_wrong_empty_null_padding_and_unicode_value_observations(self):
        good = transcript("exact_types", ["ab", "text"])
        for value in ("", good + good, transcript("exact_types", ["", "text"]),
                      transcript("exact_types", [None, "text"]), transcript("exact_types", ["ab ", "text"]),
                      transcript("exact_types", ["ab", "name"]), transcript("exact_types", ["é😀", "text"])):
            with self.subTest(value=value), self.assertRaises((AssertionError, ValueError)):
                self.exercise_main(values=value)
        for nulls in ("", transcript("json_null", ["true"]), transcript("json_null", [None])):
            with self.subTest(nulls=nulls), self.assertRaises(AssertionError):
                self.exercise_main(nulls=nulls)

    def test_pipeline_requires_exact_descriptors_signatures_sqlstates_and_all_1266_analysis_rows(self):
        for metadata in ("", "v|text\n" * 2, "v|name\n" * 2 + "left|text\n" * 2,
                         "left|text\n" * 2 + "v|text\n" * 2):
            with self.subTest(metadata=metadata), self.assertRaises(AssertionError):
                self.exercise_main(metadata=metadata)
        for catalog in ("", "0|t\n", "1|t\n0|t\n", "0|t\n1|f\n", "0|t\n1|t\n1|t\n"):
            with self.subTest(catalog=catalog), self.assertRaises(AssertionError):
                self.exercise_main(catalog=catalog)
        for state in ("00000", "unexpected-success", "22003", "57014"):
            with self.subTest(state=state), self.assertRaises(AssertionError):
                self.exercise_main(errors=transcript("containment_error", [state]))
        states = checker.analysis_script()[1]
        for changed in ([], states[:-1], list(reversed(states)), ["57014", *states[1:]]):
            with self.subTest(states=changed), self.assertRaises(AssertionError):
                self.exercise_main(analysis="\n".join(changed) + "\n")


if __name__ == "__main__":
    unittest.main()
