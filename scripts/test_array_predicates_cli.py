"""Evidence integrity for strict, same-element array predicates."""
from contextlib import nullcontext, redirect_stdout
from copy import deepcopy
import io
import json
from pathlib import Path
import subprocess
import tempfile
import unittest
from unittest.mock import patch

import check_array_predicates_cli as checker
from check_postgresql_cli import NULL
from generate_array_predicate_examples import containment_cases, overlap_cases


def transcript(category, values, index=1):
    def field(value):
        return NULL if value is None else '"' + value.replace('"', '""') + '"'
    result = []
    for form in ("source", "postgres"):
        result += [checker.marker(category, index, True, form),
                   '"value","type"' if len(values) == 2 else '"observation"',
                   ",".join(map(field, values))]
    return "\n".join(result) + "\n"


class ArrayPredicatesCliTests(unittest.TestCase):
    def fixture_directory(self, *, populations=None, predicates=None, equality=None):
        temporary = tempfile.TemporaryDirectory()
        self.addCleanup(temporary.cleanup)
        directory = Path(temporary.name)
        if populations is not None:
            for factor, (rows, source) in populations.items():
                path = directory / factor
                path.mkdir(parents=True, exist_ok=True)
                (path / "synthetic.json").write_text(json.dumps(rows))
                (path / "concrete.jsonl").write_text("".join(json.dumps(row) + "\n" for row in source))
        path = directory / "array_containment"
        path.mkdir(parents=True, exist_ok=True)
        if predicates is not None:
            (path / "operator_signatures.json").write_text(json.dumps(predicates))
        if equality is not None:
            (path / "element_equality_signatures.json").write_text(json.dumps(equality))
        return directory

    @staticmethod
    def populations():
        result = {}
        for factor, rows in (("array_containment", containment_cases()), ("array_overlap", overlap_cases())):
            # Source harvesting is independently tested; these placeholders
            # isolate the loader's fixed population and metadata protocol.
            source = [{"id": f"{factor}-source-{i}", "sql": f"SELECT {i} /* {factor} */;",
                       "observed_syntax": {"source_free": i < {"array_containment": 6, "array_overlap": 5}[factor]}}
                      for i in range(50)]
            result[factor] = (rows, source)
        return result

    @staticmethod
    def case():
        return {
            "sql": "SELECT CAST($2 AS INTEGER[]) && $1 AS v;",
            "parameter_types": "integer[],integer[]",
            "parameter_values": ["{2}", "{1,2}"],
            "output_columns": [{"name": "v", "type": "bool", "nullable": False}],
            "postgres_type": "boolean", "postgres_display_type": "boolean",
            "expected_value": "true", "sqlite_input": "SELECT CAST(?2 AS INTEGER[]) && ?1 AS v;",
        }

    def test_fifty_each_are_persisted_authored_distinct_oracles(self):
        for factor, rows in (("array_containment", containment_cases()), ("array_overlap", overlap_cases())):
            self.assertEqual(json.loads((checker.FIXTURES / factor / "synthetic.json").read_text()), rows)
            self.assertEqual(len(rows), 50)
            self.assertEqual(len({row["sql"] for row in rows}), 50)
            self.assertEqual(len({row["id"] for row in rows}), 50)
            self.assertTrue(all(row["source_kind"] == "synthetic" for row in rows))
        with patch.object(checker, "FIXTURES", self.fixture_directory(populations=self.populations())):
            rows, sources = checker.load_cases()
        self.assertEqual((len(rows), len(sources)), (100, 100))

    def test_real_sources_retain_six_containment_and_five_overlap_certifiable_queries(self):
        rows, sources = checker.load_cases()
        self.assertEqual((len(rows), len(sources)), (100, 100))
        self.assertEqual(checker.SOURCE_FREE_COUNTS, {"array_containment": 6, "array_overlap": 5})
        for factor, expected in (("array_containment", 6), ("array_overlap", 5)):
            selected = [row for row in sources if row["factor"] == factor]
            self.assertEqual(len(selected), 50)
            self.assertEqual(sum(row["observed_syntax"]["source_free"] for row in selected), expected)
            self.assertTrue(all(row["raw_sql"] == row["sql"] and row["transformations"] == []
                                for row in selected))

    def test_empty_null_elements_and_outer_null_have_different_results(self):
        contained = {row["shape"]: row for row in containment_cases()}
        overlap = {row["shape"]: row for row in overlap_cases()}
        for direction in ("contains", "contained"):
            for shape in ("empty", "empty-right", "duplicates", "null-left-member"):
                self.assertEqual(contained[f"{direction}-{shape}"]["expected_value"], "true")
            for shape in ("null-members", "null-right-member"):
                row = contained[f"{direction}-{shape}"]
                self.assertEqual(row["expected_value"], "false")
                self.assertFalse(row["output_columns"][0]["nullable"])
            self.assertIsNone(contained[f"{direction}-sql-null-left"]["expected_value"])
        for shape in ("empty-both", "empty-left", "empty-right", "null-members"):
            self.assertEqual(overlap[shape]["expected_value"], "false")
            self.assertFalse(overlap[shape]["output_columns"][0]["nullable"])
        for shape in ("sql-null-left", "sql-null-right", "sql-null-both"):
            self.assertIsNone(overlap[shape]["expected_value"])
            self.assertTrue(overlap[shape]["output_columns"][0]["nullable"])
        self.assertEqual(overlap["jsonb-not-containment"]["expected_value"], "false")
        self.assertEqual(overlap["jsonb-equality"]["expected_value"], "true")
        self.assertTrue(overlap["slice"]["output_columns"][0]["nullable"])

    def test_directional_anonymous_binding_swap_and_numbered_identity(self):
        rows = containment_cases()
        left = next(row for row in rows if row["shape"] == "contains-anonymous")
        right = next(row for row in rows if row["shape"] == "contained-anonymous")
        self.assertEqual(left["parameter_values"], list(reversed(right["parameter_values"])))
        for case in (left, right):
            script, _ = checker.database_script([case], [case["sql"]])
            self.assertIn("CAST($1 AS INTEGER[])", script)
            self.assertIn("CAST($2 AS INTEGER[])", script)
            self.assertNotIn("CAST(? AS INTEGER[])", script)
        case = self.case()
        script, wanted = checker.describe_script([case], [case["sql"]])
        self.assertEqual(script.count("SELECT CAST($2 AS INTEGER[]) && $1 AS v;"), 2)
        self.assertIn("EXECUTE array_description('{2}', '{1,2}')", script)
        self.assertEqual(wanted, ["v|boolean"] * 2)
        repeated = next(row for row in overlap_cases() if row["shape"] == "repeated")
        script, _ = checker.describe_script([repeated], [repeated["sql"]])
        self.assertEqual(script.count("$1"), 4)
        self.assertIn("PREPARE array_description (integer[])", script)
        nullable = next(row for row in overlap_cases() if row["shape"] == "nullable-binding")
        script, _ = checker.describe_script([nullable], [nullable["sql"]])
        self.assertIn("EXECUTE array_description(NULL)", script)
        self.assertNotIn("(integer[]?)", script)

    def test_loader_rejects_missing_duplicate_forged_metadata_and_binding_order(self):
        for mutation in ("missing", "source_missing", "duplicate_id", "duplicate_sql", "source_duplicate",
                         "name", "type", "nullable", "arity", "native_type", "display_type", "value",
                         "null_nonnull", "source_kind", "sqlite", "extra_binding", "missing_binding",
                         "binding_order", "scope_not_bool", "scope_count"):
            populations = self.populations()
            rows, source = populations["array_overlap"]
            if mutation == "missing":
                rows.pop()
            elif mutation == "source_missing":
                source.pop()
            elif mutation.startswith("duplicate_"):
                key = mutation.removeprefix("duplicate_")
                rows[1][key] = rows[0][key]
            elif mutation == "source_duplicate":
                source[1]["sql"] = source[0]["sql"]
            elif mutation in ("name", "type", "nullable"):
                rows[0]["output_columns"][0][mutation] = {"name": "wrong", "type": "text", "nullable": 0}[mutation]
            elif mutation == "arity":
                rows[0]["output_columns"].append(rows[0]["output_columns"][0])
            elif mutation in ("native_type", "display_type"):
                rows[0]["postgres_type" if mutation == "native_type" else "postgres_display_type"] = "bool"
            elif mutation == "value":
                rows[0]["expected_value"] = False
            elif mutation == "null_nonnull":
                rows[0]["expected_value"] = None
            elif mutation == "source_kind":
                rows[0]["source_kind"] = "engine-regression"
            elif mutation == "sqlite":
                rows[0]["sqlite_supported"] = True
            elif mutation == "scope_not_bool":
                source[0]["observed_syntax"]["source_free"] = 1
            elif mutation == "scope_count":
                source[0]["observed_syntax"]["source_free"] = False
            else:
                row = next(row for row in rows if row["shape"] == "reordered")
                if mutation == "extra_binding":
                    row["parameter_values"].append("unused")
                elif mutation == "missing_binding":
                    row["parameter_values"].pop()
                else:
                    row["sqlite_input"] = "SELECT ?1 && ?2 AS v;"
            with self.subTest(mutation=mutation), patch.object(
                    checker, "FIXTURES", self.fixture_directory(populations=populations)), self.assertRaises(AssertionError):
                checker.load_cases()

    def test_catalog_requires_strict_anyarray_and_nineteen_element_equality_mappings(self):
        script, wanted = checker.operator_script()
        self.assertEqual(wanted, [f"{i}|t" for i in range(23)])
        self.assertEqual(script.count("AND p.proisstrict"), 22)
        self.assertNotIn("anycompatible", script)
        for operator, function in (("@>", "arraycontains"), ("<@", "arraycontained"), ("&&", "arrayoverlap")):
            matching = next(line for line in script.splitlines() if f"p.proname='{function}'" in line)
            for clause in (f"o.oprname='{operator}'", "o.oprleft='anyarray'::regtype",
                           "o.oprright='anyarray'::regtype", "o.oprresult='boolean'::regtype",
                           "p.prorettype='boolean'::regtype", "p.proargtypes[0]='anyarray'::regtype",
                           "p.proargtypes[1]='anyarray'::regtype", "NOT p.proretset",
                           "p.pronargs=2", "p.prokind='f'", "p.pronamespace='pg_catalog'::regnamespace"):
                self.assertIn(clause, matching)
        self.assertIn("castsource='varchar'::regtype", script)
        self.assertIn("casttarget='text'::regtype AND castcontext='i' AND castmethod='b'", script)
        self.assertNotIn("p.proname='json_eq'", script)
        self.assertIn("p.proname='jsonb_eq'", script)

    def test_catalog_inventory_rejects_replaced_generic_or_element_types(self):
        predicates = json.loads((checker.FIXTURES / "array_containment/operator_signatures.json").read_text())
        equality = json.loads((checker.FIXTURES / "array_containment/element_equality_signatures.json").read_text())
        mutations = [
            (predicates[:-1], equality), (predicates + predicates[:1], equality),
            (predicates[:-1] + predicates[:1], equality), (predicates, equality[:-1]),
            (predicates, equality[:-1] + equality[:1]),
        ]
        for key, value in (("left", "anycompatiblearray"), ("right", "anycompatiblearray"),
                           ("output", "text"), ("function", "array_cat"), ("operator", "||")):
            bad = deepcopy(predicates)
            bad[0][key] = value
            mutations.append((bad, equality))
        for key, value in (("element", "json"), ("left", "varchar"), ("right", "varchar"),
                           ("operator", "<>"), ("output", "integer")):
            bad = deepcopy(equality)
            bad[-1][key] = value
            mutations.append((predicates, bad))
        for p, e in mutations:
            with self.subTest(predicates=p, equality=e), patch.object(
                    checker, "FIXTURES", self.fixture_directory(predicates=p, equality=e)), self.assertRaises(AssertionError):
                checker.operator_script()

    def test_value_oracle_does_not_confuse_false_null_or_nonboolean_outputs(self):
        case = self.case()
        script, wanted = checker.database_script([case], [case["sql"]])
        self.assertEqual(checker.validate_results(checker.parse_results(
            transcript("exact_types", ["true", "boolean"])), wanted), 2)
        for values in (["false", "boolean"], [None, "boolean"], ["null", "boolean"],
                       ["true", "text"], ["true", "jsonb"], ["t", "boolean"]):
            with self.subTest(values=values), self.assertRaises(AssertionError):
                checker.validate_results(checker.parse_results(transcript("exact_types", values)), wanted)
        self.assertIn("v::text, pg_typeof(v)::text", script)
        self.assertIn("SET LOCAL statement_timeout = '5s'", script)
        self.assertTrue(script.endswith("ROLLBACK;"))

    def test_json_equality_gaps_remain_outside_static_certificates(self):
        errors, gaps = checker.runtime_cases(), checker.equality_gap_cases()
        self.assertEqual([row["sqlstate"] for row in errors], ["22P02", "22003"] * 3)
        self.assertTrue(all(not row["output_columns"][0]["nullable"] for row in errors))
        self.assertEqual(len(gaps), 3)
        self.assertTrue(all(row["sqlstate"] == "42883" for row in gaps))
        self.assertTrue(all(row["parameter_values"] == ["{}"] for row in gaps))
        self.assertTrue(all("output_columns" not in row for row in gaps))
        all_cases = errors + gaps
        script, wanted = checker.error_script(all_cases, [row["sql"] for row in all_cases])
        self.assertEqual(len(wanted), 18)
        self.assertEqual(script.count("RETURN SQLSTATE"), 18)
        self.assertEqual(script.count("RETURN ''unexpected-success''"), 18)
        self.assertEqual(script.count("PREPARE pagination_parameters (TEXT)"), 18)
        self.assertIn("CAST($1 AS JSON[])", script)
        self.assertTrue(script.endswith("ROLLBACK;"))

    def test_missing_canonical_lists_fail_before_zip_truncation(self):
        row = self.case()
        for function in (checker.database_script, checker.describe_script):
            with self.subTest(function=function.__name__), self.assertRaises(AssertionError):
                function([row], [])
        with self.assertRaises(AssertionError):
            checker.error_script(checker.runtime_cases(), [])

    def test_sqlite_rejection_requires_paired_exit_status_and_feature(self):
        for code, status, diagnostic in (
            (1, "invalid", "input.parse"), (3, "unsupported", "coverage.sqlite.containment"),
            (3, "unsupported", "coverage.sqlite.overlap"),
        ):
            result = subprocess.CompletedProcess([], code, json.dumps({
                "status": status, "diagnostic": {"code": diagnostic}}), "")
            with patch.object(checker, "invoke", return_value=result) as invoke:
                checker.reject_sqlite(self.case())
            self.assertEqual(invoke.call_args.kwargs["stdin"], self.case()["sqlite_input"])
        for code, status, diagnostic in (
            (0, "rendered", "coverage.sqlite.overlap"), (1, "unsupported", "coverage.sqlite.overlap"),
            (3, "invalid", "input.parse"), (3, "unsupported", "input.parse"),
            (3, "unsupported", "resource.depth"), (3, "unsupported", "coverage.sqlite.array-type"),
        ):
            result = subprocess.CompletedProcess([], code, json.dumps({
                "status": status, "diagnostic": {"code": diagnostic}}), "")
            with self.subTest(status=status, diagnostic=diagnostic), patch.object(
                    checker, "invoke", return_value=result), self.assertRaises(AssertionError):
                checker.reject_sqlite(self.case())

    def test_exact_prepared_labels_preserve_boolean_text_and_nullable_boundaries(self):
        labels = checker.label_cases()
        script, wanted = checker.describe_script(labels, [row["sql"] for row in labels])
        self.assertEqual(len(labels), 9)
        self.assertEqual(wanted, [f"?column?|{t}" for t in
                                 ["boolean"] * 5 + ["text", "text", "boolean", "boolean"] for _ in range(2)])
        self.assertEqual([row["output_columns"][0]["nullable"] for row in labels],
                         [False, False, False, True, True, False, False, False, False])
        self.assertEqual(script.count("\\gdesc"), 18)
        self.assertNotIn("RETURNS TABLE", script)

    def exercise_main(self, *, values=None, errors=None, metadata=None, operators=None):
        row, runtime, gap, label = (self.case(), checker.runtime_cases()[0],
                                   checker.equality_gap_cases()[0], checker.label_cases()[0])
        source = [
            {"sql": "SELECT ARRAY[1] && ARRAY[1] /* never_execute_literal_source */;",
             "observed_syntax": {"source_free": True}},
            {"sql": "SELECT * FROM never_execute_table_source WHERE a && '{1}';",
             "observed_syntax": {"source_free": False}},
        ]
        values = transcript("exact_types", ["true", "boolean"]) if values is None else values
        errors = (transcript("array_predicate_error", ["22P02"]) +
                  transcript("array_predicate_error", ["42883"], 2)) if errors is None else errors
        metadata = "v|boolean\n" * 2 + "?column?|boolean\n" * 2 if metadata is None else metadata
        operators = "".join(f"{i}|t\n" for i in range(23)) if operators is None else operators
        results = [subprocess.CompletedProcess(["psql"], 0, text, "") for text in
                   (values, errors, metadata, operators, "16.15\n")]
        with patch.object(checker, "load_cases", return_value=([row], source)), \
                patch.object(checker, "runtime_cases", return_value=[runtime]), \
                patch.object(checker, "equality_gap_cases", return_value=[gap]), \
                patch.object(checker, "label_cases", return_value=[label]), \
                patch.object(checker, "validity") as validity, \
                patch.object(checker, "assert_report") as certificates, \
                patch.object(checker, "replay", side_effect=lambda profile, sql: {"sql": sql}) as replay, \
                patch.object(checker, "reject_sqlite"), \
                patch.object(checker, "boundaries", return_value=0), \
                patch.object(checker, "connection", return_value=nullcontext(["psql"])), \
                patch.object(checker, "run", side_effect=results) as run, \
                patch("sys.argv", ["check_array_predicates_cli.py", "--dsn", "unused"]), \
                redirect_stdout(io.StringIO()):
            checker.main()
            return run.call_args_list, validity.call_args_list, certificates.call_args_list, replay.call_args_list

    def test_pipeline_never_executes_source_queries_or_certifies_json_equality_gaps(self):
        calls, validity, certificates, replays = self.exercise_main()
        self.assertEqual(len(calls), 5)
        for call in calls[:4]:
            self.assertIn("ON_ERROR_STOP=1", call.args[0])
            self.assertEqual(call.kwargs["timeout"], 120)
            self.assertNotIn("never_execute_", call.kwargs["input"])
        self.assertEqual(len(validity), 3)
        self.assertFalse(any("JSON[]" in call.args[0]["sql"] for call in validity))
        self.assertEqual([call.args[1] for call in certificates], ["valid", "unsupported"])
        self.assertEqual(sum("never_execute_" in call.args[1] for call in replays), 4)
        self.assertEqual(sum("JSON[]" in call.args[1] for call in replays), 1)

    def test_pipeline_rejects_missing_duplicate_false_null_and_wrong_oid_values(self):
        good = transcript("exact_types", ["true", "boolean"])
        for value in ("", good + good, transcript("exact_types", ["false", "boolean"]),
                      transcript("exact_types", [None, "boolean"]), transcript("exact_types", ["true", "text"])):
            with self.subTest(value=value), self.assertRaises((AssertionError, ValueError)):
                self.exercise_main(values=value)

    def test_pipeline_rejects_missing_renamed_reordered_or_wrong_descriptors(self):
        for metadata in ("", "v|boolean\n" * 2 + "?column?|boolean\n",
                         "v|text\n" * 2 + "?column?|boolean\n" * 2,
                         "v|boolean\n" * 2 + "renamed|boolean\n" * 2,
                         "?column?|boolean\n" * 2 + "v|boolean\n" * 2):
            with self.subTest(metadata=metadata), self.assertRaises(AssertionError):
                self.exercise_main(metadata=metadata)

    def test_pipeline_rejects_missing_false_duplicate_predicate_equality_or_varchar_cast_evidence(self):
        good = [f"{i}|t" for i in range(23)]
        bad = [[], good[:-1], good[1:], good + good[:1], list(reversed(good))]
        for index in (0, 1, 2, 3, 21, 22):
            changed = good[:]
            changed[index] = f"{index}|f"
            bad.append(changed)
        for operators in bad:
            with self.subTest(operators=operators), self.assertRaises(AssertionError):
                self.exercise_main(operators="\n".join(operators) + "\n")

    def test_pipeline_requires_both_conversion_and_equality_error_observations(self):
        conversion = transcript("array_predicate_error", ["22P02"])
        equality = transcript("array_predicate_error", ["42883"], 2)
        for errors in ("", conversion, equality, conversion + equality + equality,
                       conversion + transcript("array_predicate_error", ["unexpected-success"], 2),
                       conversion + transcript("array_predicate_error", ["57014"], 2),
                       transcript("array_predicate_error", ["42883"]) + equality):
            with self.subTest(errors=errors), self.assertRaises((AssertionError, ValueError)):
                self.exercise_main(errors=errors)

    def test_exact_result_arity_rows_cases_and_markers_are_required(self):
        expected = {"case": (2, [["true", "boolean"]])}
        for actual in ({}, {**expected, "extra": expected["case"]},
                       {"case": (1, [["true"]])}, {"case": (2, [["true", "boolean"]] * 2)}):
            with self.subTest(actual=actual), self.assertRaises(AssertionError):
                checker.validate_results(actual, expected)
        good = transcript("exact_types", ["true", "boolean"])
        with self.assertRaisesRegex(ValueError, "Duplicate case marker"):
            checker.parse_results(good + good)

    def test_boundaries_keep_incompatible_element_types_separate_from_unsupported_json(self):
        good = subprocess.CompletedProcess([], 1, json.dumps({
            "status": "invalid", "diagnostic": {"code": "input.parse"}}), "")
        with patch.object(checker, "assert_report") as reports, \
                patch.object(checker, "invoke", return_value=good) as invoke:
            self.assertEqual(checker.boundaries(), 41)
        self.assertEqual(sum(call.args[1] == "invalid" for call in reports.call_args_list), 18)
        self.assertEqual(sum(call.args[1] == "unsupported" for call in reports.call_args_list), 9)
        self.assertEqual(sum(call.args[1] == "valid" for call in reports.call_args_list), 7)
        self.assertEqual(sum(call.args[1] == "rejected" for call in reports.call_args_list), 3)
        self.assertEqual(len(invoke.call_args_list), 4)
        scalar_calls = [call for call in reports.call_args_list
                        if call.args[0][-1].endswith("(SELECT ARRAY[1])")]
        self.assertEqual(len(scalar_calls), 3)
        self.assertTrue(all(call.args[1:] == ("valid", "contract", (("?column?", "bool", True),))
                            for call in scalar_calls))
        bad = subprocess.CompletedProcess([], 3, json.dumps({
            "status": "unsupported", "diagnostic": {"code": "input.parse"}}), "")
        with patch.object(checker, "assert_report"), patch.object(checker, "invoke", return_value=bad), \
                self.assertRaises(AssertionError):
            checker.boundaries()


if __name__ == "__main__":
    unittest.main()
