"""Offline checks for application-source extraction and provenance."""
import json
from pathlib import Path
import unittest

from extract_application_corpus import (
    DIRECTORY, decode_constants, first_sql_text, formatted_constants, sql_code, verify_sources,
)


class ApplicationCorpusTests(unittest.TestCase):
    def test_go_literal_concatenation_preserves_backticks_and_parameter_slots(self):
        source = 'const query = `-- use ` + "`" + `value` + "`" + `\nSELECT $2, $1, $2\n`\n'
        records = list(decode_constants(source))
        self.assertEqual(len(records), 1)
        self.assertEqual(records[0]["raw_sql"], "-- use `value`\nSELECT $2, $1, $2\n")
        self.assertTrue(records[0]["go_constant_folding"])

    def test_comments_and_sql_text_do_not_create_go_constants(self):
        source = '''// const fake = `SELECT 9`
/* const other = "SELECT 8" */
const query = `SELECT 'const inside = "SELECT 7"'
)`
'''
        records = list(decode_constants(source))
        self.assertEqual([record["symbol"] for record in records], ["query"])
        self.assertEqual(records[0]["line"], 3)

    def test_const_blocks_references_and_continuations(self):
        source = '''const (
  columns = `id, name`
  query = `SELECT ` + columns +
    ` FROM users WHERE id=$1`
  literal = "SELECT \\"quoted\\""
)
'''
        records = {record["symbol"]: record for record in decode_constants(source)}
        self.assertEqual(records["query"]["raw_sql"], "SELECT id, name FROM users WHERE id=$1")
        self.assertEqual(records["literal"]["raw_sql"], 'SELECT "quoted"')

    def test_unsupported_expressions_are_explicit_not_evaluated(self):
        source = '''const (
  dynamic = fmt.Sprintf("SELECT %s", runtimeName)
  missing = unknown + ` FROM t`
  cyclic = cyclic + "x"
  escaped = "SELECT '\\\\x41'"
)
'''
        records = {record["symbol"]: record for record in decode_constants(source)}
        for name in ("dynamic", "missing", "cyclic"):
            self.assertIn("decode_error", records[name])
            self.assertNotIn("raw_sql", records[name])
        self.assertEqual(records["escaped"]["raw_sql"], "SELECT '\\x41'")

    def test_named_bind_observer_ignores_literals_identifiers_and_nested_comments(self):
        sql = """-- name: Query :many
SELECT ':literal', ":identifier", $$:body$$, $tag$:body$tag$, value::text, :binding
/* :outer /* :inner */ :outer */"""
        masked = sql_code(sql)
        self.assertIn(":binding", masked)
        self.assertIn("value::text", masked)
        for name in (":many", ":literal", ":identifier", ":body", ":outer", ":inner"):
            self.assertNotIn(name, masked)

    def test_format_detection_uses_go_calls_not_percent_in_sql_data(self):
        source = '''const query = `SELECT '%s', 'fmt.Sprintf(fake, x)'`
// fmt.Sprintf(alsoFake, x)
value := fmt.Sprintf(
  realTemplate, name,
)
'''
        self.assertEqual(formatted_constants(source), {"realTemplate"})

    def test_leading_sqlc_comments_do_not_hide_statement_kind(self):
        self.assertEqual(first_sql_text("-- name: Query :one\n/* schema default */ SELECT $1"),
                         "SELECT $1")

    def test_actual_vendored_sources_and_licenses_match_pins(self):
        manifest = json.loads((DIRECTORY / "application_sources.json").read_text())
        verify_sources(manifest)
        self.assertEqual(manifest["river"]["license"], "MPL-2.0")
        self.assertEqual(manifest["temporal"]["license"], "MIT")

    def test_exact_application_population_and_record_provenance(self):
        for app, count, candidates in (("river", 56, 57), ("temporal", 116, 196)):
            rows = [json.loads(line) for line in (DIRECTORY / f"{app}.jsonl").read_text().splitlines()]
            self.assertEqual(len(rows), count)
            self.assertEqual(len({row["id"] for row in rows}), count)
            self.assertEqual(len({row["sql"] for row in rows}), count)
            for row in rows:
                self.assertEqual(row["source"], app)
                self.assertEqual(row["sql"], row["raw_sql"])
                self.assertEqual(row["transformations"], [])
                self.assertIn("/blob/" + row["commit"] + "/", row["source_url"])
                self.assertTrue(row["source_url"].endswith(f'#L{row["line"]}'))
            ledger = json.loads((DIRECTORY / f"{app}_extraction.json").read_text())
            self.assertEqual(ledger["candidate_count"], candidates)
            self.assertEqual(ledger["included"], count)
            self.assertEqual(len(ledger["dispositions"]), candidates)
            included = {entry["id"] for entry in ledger["dispositions"] if entry["disposition"] == "included"}
            self.assertEqual(included, {row["id"] for row in rows})
            for entry in ledger["dispositions"]:
                if entry["disposition"] == "excluded":
                    self.assertTrue(entry["reason"])
                    self.assertTrue("raw_sql" in entry or "source_expression" in entry)

    def test_sqlc_binary_copy_command_is_an_explicit_exclusion(self):
        ledger = json.loads((DIRECTORY / "river_extraction.json").read_text())
        excluded = [entry for entry in ledger["dispositions"] if entry["disposition"] == "excluded"]
        self.assertEqual(len(excluded), 1)
        self.assertIn("JobInsertFastManyCopyFrom", excluded[0]["id"])
        self.assertIn(":copyfrom", excluded[0]["raw_sql"])
        self.assertIn("binary-copy API", excluded[0]["reason"])


if __name__ == "__main__":
    unittest.main()
