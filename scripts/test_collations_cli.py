"""Evidence-protocol tests for exact COLLATE metadata and native observations."""
from copy import deepcopy
from collections import Counter
import json
from pathlib import Path
import subprocess
import tempfile
import unittest
from unittest.mock import patch

import check_assurance_cli
import check_collations_cli as checker
from generate_collation_examples import all_cases, cases, schema
from test_set_operations_cli import native_transcript


class CollationsCliTests(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        cls.rows = all_cases()
        cls.sources = [json.loads(line) for line in (checker.FIXTURES / "concrete.jsonl").read_text().splitlines()]

    def case(self, shape):
        return next(row for row in self.rows if row["shape"] == shape)

    def fixture_copy(self, rows, sources, catalog):
        temporary = tempfile.TemporaryDirectory()
        self.addCleanup(temporary.cleanup)
        root = Path(temporary.name)
        (root / "synthetic.json").write_text(json.dumps(rows))
        (root / "schema.json").write_text(json.dumps(catalog))
        (root / "concrete.jsonl").write_text("".join(json.dumps(row) + "\n" for row in sources))
        return root

    def test_fifty_authored_and_fifty_unchanged_sources(self):
        rows, sources = checker.load_cases()
        self.assertEqual(rows, self.rows)
        self.assertEqual(len(sources), 50)
        self.assertEqual(len({r["shape"] for r in rows}), 50)
        self.assertTrue(all(set(row["expected_rows_by_state"]) == set(checker.STATES) for row in rows))
        self.assertTrue(all("COLLATE" in row["sql"].upper() for row in rows))
        self.assertEqual(Counter(row["sqlite_mode"] for row in rows),
                         {"render_unsupported": 44, "parse_invalid": 6})
        self.assertEqual(Counter(row["sqlite_diagnostic"] for row in rows), {
            "coverage.sqlite.collation": 39, "input.parse": 6,
            "coverage.sqlite.scalar-function-signatures": 4, "coverage.sqlite.PostgreSQL-type": 1,
        })

    def test_preregistered_rows_preserve_duplicates_nulls_and_population(self):
        source = {"words": [["b"], ["b"], ["x"]], "labels": [["b"], ["b"], ["z"]]}
        rows = {row["shape"]: row for row in cases(source)}
        self.assertEqual(rows["using-join"]["expected_rows"], [["b"]] * 4)
        self.assertEqual(rows["nullable-side-custom-object"]["expected_rows"], [["b"]] * 4 + [[None]])
        self.assertEqual(rows["recursive-base-collation"]["expected_rows"],
                         [["b"], ["b"], ["x"], ["bx"], ["bx"], ["xx"]])
        self.assertEqual(self.case("nullable-side-custom-object")["expected_rows_by_state"]["words_only"],
                         [[None], [None], [None]])
        self.assertEqual(self.case("recursive-base-collation")["expected_rows_by_state"]["empty"], [])

    def test_identities_are_not_equated_with_types_or_locale_behavior(self):
        self.assertEqual(self.case("literal-c")["output_columns"][0]["collation"], "C")
        self.assertEqual(self.case("literal-posix")["output_columns"][0]["collation"], "POSIX")
        self.assertEqual(self.case("unknown-to-integer")["output_columns"][0]["collation"], None)
        self.assertEqual(self.case("name-posix")["output_columns"][0]["collation"], "POSIX")
        self.assertEqual(self.case("recursive-name")["output_columns"][0]["collation"], "C")
        self.assertEqual(self.case("ordering-does-not-change-output")["output_columns"][0]["collation"], "default")
        self.assertEqual(self.case("qualified-custom-object")["output_columns"][0]["collation"], "custom:c_order")
        self.assertEqual(self.case("array-slice")["output_columns"][0]["type"], "text[]")
        self.assertTrue(self.case("array-slice")["output_columns"][0]["nullable"])

    def test_fixture_loader_rejects_drift_and_source_modification(self):
        for mutation in ("count", "sql", "collation", "nullable", "parameter", "state",
                         "catalog_identity", "field_default", "sqlite_mode", "sqlite_diagnostic",
                         "source_raw", "source_hash", "source_rewrite"):
            rows, sources, catalog = deepcopy(self.rows), deepcopy(self.sources), schema()
            if mutation == "count":
                rows.pop()
            elif mutation == "sql":
                rows[0]["sql"] += " "
            elif mutation == "collation":
                rows[0]["output_columns"][0]["collation"] = "POSIX"
            elif mutation == "nullable":
                rows[0]["output_columns"][0]["nullable"] = 0
            elif mutation == "parameter":
                rows[40]["parameter_values"] = ["other"]
            elif mutation == "state":
                rows[0]["expected_rows_by_state"].pop("empty")
            elif mutation == "catalog_identity":
                catalog["collations"]["entries"][1]["id"] = "POSIX"
            elif mutation == "field_default":
                catalog["tables"][0].pop("columnCollations")
            elif mutation == "sqlite_mode":
                rows[25]["sqlite_mode"] = "render_unsupported"
            elif mutation == "sqlite_diagnostic":
                rows[21]["sqlite_diagnostic"] = "coverage.sqlite.collation"
            elif mutation == "source_raw":
                sources[0]["raw_sql"] += " "
            elif mutation == "source_hash":
                sources[0]["sql_sha256"] = "0" * 64
            else:
                sources[0]["transformations"] = ["modified"]
            with self.subTest(mutation=mutation), patch.object(
                    checker, "FIXTURES", self.fixture_copy(rows, sources, catalog)), self.assertRaises(AssertionError):
                checker.load_cases()

    def test_exact_metadata_and_independent_evidence_are_required(self):
        row = self.case("literal-c")
        expected = {"status": "valid", "assurance": "declarative",
                    "profile": check_assurance_cli.PROFILES["contract"], "evidence": "declarative-derivation",
                    "catalogUnchanged": True, "typePrecision": "exact",
                    "outputColumns": [{key: col[key] for key in ("name", "type", "nullable")}
                                      for col in row["output_columns"]],
                    "outputCollations": ["C"]}
        for mutation in (None, "assurance", "profile", "evidence", "catalogUnchanged", "typePrecision",
                         "nullable", "missing_collations", "wrong_identity", "extra_identity"):
            report = deepcopy(expected)
            if mutation == "nullable":
                report["outputColumns"][0]["nullable"] = True
            elif mutation == "missing_collations":
                report.pop("outputCollations")
            elif mutation == "wrong_identity":
                report["outputCollations"] = ["POSIX"]
            elif mutation == "extra_identity":
                report["outputCollations"] = ["C", None]
            elif mutation is not None:
                report[mutation] = "weaker"
            with self.subTest(mutation=mutation), patch.object(check_assurance_cli, "invoke",
                    return_value=subprocess.CompletedProcess([], 0, json.dumps(report), "")):
                if mutation is None:
                    checker.validity(row)
                else:
                    with self.assertRaises(AssertionError):
                        checker.validity(row)

    def test_binding_is_separate_and_lexical_slots_are_preserved(self):
        numbered = self.case("numbered-parameter-order")
        self.assertEqual(checker.parameters(numbered["sql"], "postgres"), [("numbered", 2), ("numbered", 1)])
        capture = checker.capture(numbered, numbered["sql"])
        self.assertIn("$2", capture[0])
        self.assertIn("$1", capture[0])
        self.assertIn("EXECUTE collation_parameters (''''b'''', ''''a'''')", capture[1])
        anonymous = self.case("nullable-anonymous-parameters")
        self.assertEqual(checker.parameters(anonymous["sql"], "postgres"), [("anonymous", 1), ("anonymous", 2)])
        capture = checker.capture(anonymous, anonymous["sql"])
        self.assertIn("$1", capture[0])
        self.assertIn("$2", capture[0])
        self.assertIn("NULL", capture[1])

    def test_collation_observer_retains_typed_empty_projection_and_parameters(self):
        row = self.case("numbered-parameter-order")
        query = checker.collation_query(row, row["sql"])
        self.assertIn("pg_collation_for(q.c0)", query)
        self.assertIn("LEFT JOIN (" + row["sql"].removesuffix(";") + ") q(c0) ON TRUE LIMIT 1", query)
        self.assertEqual(checker.parameters(query, "postgres"), checker.parameters(row["sql"], "postgres"))
        noncollatable = self.case("unknown-to-integer")
        query = checker.collation_query(noncollatable, noncollatable["sql"])
        self.assertTrue(query.startswith("SELECT NULL::TEXT FROM"))
        self.assertNotIn("pg_collation_for", query)
        self.assertNotIn("CREATE VIEW", query)

    def test_native_script_registers_all_rows_collations_and_exact_descriptors(self):
        canonical = [row["sql"] for row in self.rows]
        script, expected = checker.postgres_script(self.rows, canonical)
        self.assertEqual(len(expected), 800)
        self.assertEqual(script.count("TRUNCATE public.words,public.labels;"), 4)
        self.assertEqual(script.splitlines().count("SAVEPOINT collation_case;"), 800)
        self.assertEqual(script.splitlines().count("ROLLBACK TO SAVEPOINT collation_case;"), 800)
        self.assertTrue(script.endswith("ROLLBACK;"))
        self.assertIn("SET LOCAL statement_timeout = '5s';", script)
        self.assertIn('CREATE COLLATION fixture.c_order FROM pg_catalog."C";', script)
        descriptions, columns = checker.describe_script(self.rows, canonical)
        self.assertEqual(len(columns), 100)
        self.assertEqual(descriptions.splitlines().count("\\gdesc"), 100)
        self.assertIn("v|character varying(3)", columns)
        self.assertIn("v|character(3)", columns)
        self.assertIn("v|numeric(6,2)", columns)
        self.assertIn("v|name", columns)
        self.assertIn("v|text[]", columns)
        for method in (checker.postgres_script, checker.describe_script):
            with self.subTest(method=method), self.assertRaises(AssertionError):
                method(self.rows, canonical[:-1])

    def test_native_protocol_rejects_omission_extra_width_duplicates_and_wrong_identity(self):
        _, expected = checker.postgres_script(self.rows, [row["sql"] for row in self.rows])
        actual = checker.parse_results(native_transcript(expected))
        checker.validate_native(actual, expected)
        checker.validate_ordered(actual, self.rows)
        key = next(iter(actual))
        for mutation in ("missing", "extra", "width", "duplicate", "collation"):
            changed = deepcopy(actual)
            if mutation == "missing":
                changed.pop(key)
            elif mutation == "extra":
                changed["extra"] = (1, [])
            elif mutation == "width":
                changed[key] = (2, changed[key][1])
            elif mutation == "duplicate":
                changed[key][1].append(changed[key][1][0])
            else:
                collation = checker.marker("collation_empty_collations", 1, False, "postgres")
                changed[collation] = (1, [['"POSIX"']])
            with self.subTest(mutation=mutation), self.assertRaises(AssertionError):
                checker.validate_native(changed, expected)

    def test_same_row_bag_cannot_replace_required_order(self):
        _, expected = checker.postgres_script(self.rows, [row["sql"] for row in self.rows])
        actual = checker.parse_results(native_transcript(expected))
        key = checker.marker("collation_both_rows", 40, True, "postgres")
        actual[key][1].reverse()
        checker.validate_native(actual, expected)
        with self.assertRaises(AssertionError):
            checker.validate_ordered(actual, self.rows)

    def test_downloaded_statements_cannot_enter_execution_helpers(self):
        row = deepcopy(self.rows[0])
        row["source_kind"] = "concrete"
        for method, arguments in ((checker.capture, (row, row["sql"])),
                                  (checker.collation_query, (row, row["sql"])),
                                  (checker.postgres_script, ([row], [row["sql"]])),
                                  (checker.describe_script, ([row], [row["sql"]]))):
            with self.subTest(method=method), self.assertRaises(AssertionError):
                method(*arguments)

    def test_sqlite_exclusion_is_a_precise_dialect_boundary(self):
        for shape, expected_exit, status, diagnostic in (
                ("literal-c", 3, "unsupported", "coverage.sqlite.collation"),
                ("greatest", 3, "unsupported", "coverage.sqlite.scalar-function-signatures"),
                ("recursive-name", 3, "unsupported", "coverage.sqlite.PostgreSQL-type"),
                ("substring", 1, "invalid", "input.parse")):
            row = self.case(shape)
            for mutation in (None, "exit", "status", "diagnostic", "other_stage"):
                report = {"status": status, "diagnostic": {"code": diagnostic}}
                exit_code = expected_exit
                if mutation == "exit":
                    exit_code = 0
                elif mutation == "status":
                    report["status"] = "valid"
                elif mutation == "diagnostic":
                    report["diagnostic"]["code"] = "other"
                elif mutation == "other_stage":
                    exit_code = 3 if expected_exit == 1 else 1
                    report["status"] = "unsupported" if status == "invalid" else "invalid"
                with self.subTest(shape=shape, mutation=mutation), patch.object(checker, "invoke",
                        return_value=subprocess.CompletedProcess([], exit_code, json.dumps(report), "")):
                    if mutation is None:
                        checker.sqlite_render(row)
                    else:
                        with self.assertRaises(AssertionError):
                            checker.sqlite_render(row)


if __name__ == "__main__":
    unittest.main()
