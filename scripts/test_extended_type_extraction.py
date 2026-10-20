"""Offline checks for the unchanged extended-type source corpus."""
from copy import deepcopy
import json
import unittest

from extract_extended_type_corpus import (
    DIRECTORY, NEW_FAMILIES, extract, parameter_slots, render, select_sql,
    sql_code, sql_spans, validate_population,
)


class ExtendedTypeExtractionTests(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        cls.manifest = json.loads((DIRECTORY / "concrete_sources.json").read_text())
        cls.records = extract(cls.manifest)

    def test_all_fifty_source_statements_reproduce_exactly(self):
        self.assertEqual(render(self.records), (DIRECTORY / "concrete.jsonl").read_text())
        self.assertEqual(len(self.records), 50)
        self.assertEqual(len({row["sql"] for row in self.records}), 50)
        self.assertEqual({family for row in self.records for family in row["new_type_families"]},
                         NEW_FAMILIES)
        self.assertEqual(sum(row["source_kind"] == "application-constant"
                             for row in self.records), 20)
        self.assertEqual(sum(row["source_kind"] == "compiler-regression"
                             for row in self.records), 1)
        self.assertEqual(sum(row["source_kind"] == "engine-regression"
                             for row in self.records), 29)

    def test_records_keep_provenance_and_do_not_invent_application_bindings(self):
        for row in self.records:
            self.assertEqual(row["raw_sql"], row["sql"])
            self.assertEqual(row["transformations"], [])
            self.assertIsNone(row["parameter_types"])
            self.assertNotIn("parameter_values", row)
            self.assertEqual(row["application_schema_validity"], "not-claimed")
            self.assertIn(f'/blob/{row["commit"]}/{row["source_file"]}', row["source_url"])
            self.assertTrue(row["source_url"].endswith(f'#L{row["line"]}'))
        app = next(row for row in self.records if row.get("symbol") == "getStreamPayload")
        self.assertEqual(app["observed_parameter_slots"], [1, 2, 3, 4])
        self.assertEqual(app["new_type_families"], ["timestamptz", "uuid"])
        self.assertTrue(app["sql"].startswith("-- name: GetStreamPayload"))

    def test_escaped_quotes_and_semicolons_do_not_split_statements(self):
        source = "SELECT E'it\\'s;still data', 'a'';b'::json;\nSELECT 'x'::jsonb;"
        spans = sql_spans(source)
        self.assertEqual(len(spans), 2)
        self.assertEqual(source[slice(*spans[0])],
                         "SELECT E'it\\'s;still data', 'a'';b'::json;")
        self.assertEqual(source[slice(*spans[1])], "SELECT 'x'::jsonb;")

    def test_ordinary_backslash_does_not_escape_a_quote(self):
        # standard_conforming_strings=on: the slash is string data.
        source = "SELECT '\\'::text; SELECT 1;"
        self.assertEqual(len(sql_spans(source)), 2)

    def test_nested_comments_dollar_quotes_and_quoted_identifiers_are_masked(self):
        source = """-- $99; SELECT fake
SELECT $body$' ; $1 $body$, "semi;name", 'doubled'';quote'
/* outer ; /* inner ; $3 */ tail */ LIMIT $2;
SELECT 4;
"""
        self.assertEqual(len(sql_spans(source)), 2)
        masked = sql_code(source)
        self.assertIn("LIMIT $2;", masked)
        for text in ("$99", "$1", "$3", "fake", "semi;name", "doubled"):
            self.assertNotIn(text, masked)

    def test_unterminated_lexical_regions_fail_explicitly(self):
        for sql in ("SELECT 'x", "SELECT E'x\\", 'SELECT "x',
                    "SELECT $tag$x", "SELECT 1 /* outer /* inner */"):
            with self.subTest(sql=sql), self.assertRaises(ValueError):
                sql_code(sql)

    def test_parameter_slots_preserve_first_occurrence_and_ignore_data(self):
        source = """SELECT price$1, '$8', "$7", E'$6\\';quoted', $tag$$5$tag$,
                   $3::uuid, $1::uuid, $3::uuid /* $9 */ -- $10
                   , $2::timestamp"""
        self.assertEqual(parameter_slots(source), [3, 1, 2])

    def test_complete_statement_slice_and_line_are_checked(self):
        source = "-- header\nSELECT 'x'::uuid;\nSELECT 'y'::json;"
        start, end = sql_spans(source)[1]
        selector = {"kind": "sql_slice", "start": start, "end": end, "statement_index": 1}
        sql, line, _ = select_sql(source, selector)
        self.assertEqual(sql, "SELECT 'y'::json;")
        self.assertEqual(line, 3)
        with self.assertRaisesRegex(ValueError, "complete statement"):
            select_sql(source, {**selector, "end": end - 1})
        with self.assertRaisesRegex(ValueError, "must be integers"):
            select_sql(source, {**selector, "statement_index": True})

    def test_missing_or_duplicate_queries_cannot_inflate_the_count(self):
        with self.assertRaisesRegex(ValueError, "expected 50"):
            validate_population(self.records[:-1])
        rows = deepcopy(self.records)
        rows[1]["sql"] = rows[0]["sql"]
        with self.assertRaisesRegex(ValueError, "duplicate extended-type sql"):
            validate_population(rows)
        rows[1]["sql"] = "\n" + rows[0]["sql"].upper() + " "
        with self.assertRaisesRegex(ValueError, "case/whitespace duplicate"):
            validate_population(rows)

    def test_fabricated_types_slots_or_rewritten_sql_are_rejected(self):
        for field, value, message in (
            ("parameter_types", "uuid,uuid", "must not invent"),
            ("observed_parameter_slots", [999], "parameter-slot"),
            ("transformations", ["rename application table"], "text was changed"),
            ("new_type_families", ["invented"], "invalid new-type"),
        ):
            rows = deepcopy(self.records)
            rows[0][field] = value
            with self.subTest(field=field), self.assertRaisesRegex(ValueError, message):
                validate_population(rows)

    def test_losing_a_type_family_is_not_silently_accepted(self):
        rows = deepcopy(self.records)
        for row in rows:
            if row["new_type_families"] == ["int2"]:
                row["new_type_families"] = ["uuid"]
        with self.assertRaisesRegex(ValueError, "twelve new built-in type families"):
            validate_population(rows)

    def test_modified_sources_selected_bytes_and_unpinned_revisions_fail(self):
        manifest = deepcopy(self.manifest)
        manifest["sources"]["hatchet"]["files"][0]["sha256"] = "0" * 64
        with self.assertRaisesRegex(ValueError, "source hash mismatch"):
            extract(manifest)
        manifest = deepcopy(self.manifest)
        manifest["selections"][0]["sql_sha256"] = "0" * 64
        with self.assertRaisesRegex(ValueError, "selected SQL hash mismatch"):
            extract(manifest)
        manifest = deepcopy(self.manifest)
        manifest["sources"]["postgres"]["commit"] = "REL_16_STABLE"
        with self.assertRaisesRegex(ValueError, "full commit pin"):
            extract(manifest)


if __name__ == "__main__":
    unittest.main()
