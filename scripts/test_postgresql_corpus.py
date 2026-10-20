"""Offline harness checks; the optional pglast dependency is not imported."""
import json
from pathlib import Path
import subprocess
import tempfile
import unittest
from unittest.mock import patch

from audit_postgresql_corpus import (
    ACCEPTED_REPORT, failure_catalog, features, load_cases, oracle_case,
    run_sqlean, summarize,
)


class CorpusAuditTests(unittest.TestCase):
    def test_bad_inventory_fails_and_duplicates_are_visible(self):
        with tempfile.TemporaryDirectory() as directory:
            path = Path(directory) / "cases.jsonl"
            a = dict(id="a", source="sample", sql="SELECT 1", source_url="https://example.org/a")
            b = {**a, "id": "b"}
            path.write_text("\n".join(json.dumps(x) for x in (a, b)) + "\n")
            cases = load_cases([path])
            self.assertIsNone(cases[0]["duplicate_of"])
            self.assertEqual(cases[1]["duplicate_of"], "a")
            path.write_text("\n".join(json.dumps(x) for x in (a, a)) + "\n")
            with self.assertRaisesRegex(ValueError, "duplicate id"):
                load_cases([path])
            path.write_text(json.dumps(a) + "\n\n")
            with self.assertRaisesRegex(ValueError, "blank record"):
                load_cases([path])

    def test_success_requires_exact_syntax_evidence(self):
        good = subprocess.CompletedProcess([], 0, json.dumps(ACCEPTED_REPORT), "")
        with patch("audit_postgresql_corpus.subprocess.run", return_value=good) as call:
            self.assertEqual(run_sqlean(Path("/parser"), "SELECT 1", 5)["status"], "accepted")
            self.assertEqual(call.call_args.kwargs["input"], "SELECT 1")
            self.assertNotIn("shell", call.call_args.kwargs)
        for stdout, stderr in (("{}", ""), (good.stdout, "unexpected warning")):
            with patch("audit_postgresql_corpus.subprocess.run",
                       return_value=subprocess.CompletedProcess([], 0, stdout, stderr)):
                self.assertEqual(run_sqlean(Path("/parser"), "SELECT 1", 5)["status"],
                                 "infrastructure_error")

    def test_crash_timeout_and_io_error_are_not_syntax_rejections(self):
        for code, diagnostic, status in (
            (1, "parse error: 2:7: expected expression\n", "rejected"),
            (1, "out of memory", "infrastructure_error"),
            (-11, "segmentation fault", "infrastructure_error"),
        ):
            with patch("audit_postgresql_corpus.subprocess.run",
                       return_value=subprocess.CompletedProcess([], code, "", diagnostic)):
                self.assertEqual(run_sqlean(Path("/parser"), "SELECT 1", 5)["status"], status)
        for error, status in ((subprocess.TimeoutExpired("sqlean", 5), "timeout"),
                              (FileNotFoundError("sqlean"), "infrastructure_error")):
            with patch("audit_postgresql_corpus.subprocess.run", side_effect=error):
                self.assertEqual(run_sqlean(Path("/parser"), "SELECT 1", 5)["status"], status)

    def test_ast_tags_do_not_match_keywords_inside_string_literals(self):
        tree = {"stmts": [{"stmt": {"SelectStmt": {
            "targetList": [{"A_Const": {"sval": {"sval": "CASE now() OVER ARRAY"}}}]
        }}}]}
        self.assertEqual(features(tree), [])
        tree["stmts"][0]["stmt"]["SelectStmt"]["targetList"].append(
            {"FuncCall": {"funcname": [{"String": {"sval": "now"}}], "over": {"location": 7}}})
        self.assertEqual(features(tree), ["general-function-call", "window-function"])

    def test_list_valued_type_names_do_not_crash_or_hide_nested_nodes(self):
        # Actual pglast JSON shape for CREATE TYPE mood AS ENUM ('sad', 'ok').
        enum = {"stmts": [{"stmt": {"CreateEnumStmt": {
            "typeName": [{"String": {"sval": "mood"}}],
            "vals": [{"String": {"sval": "sad"}}, {"String": {"sval": "ok"}}],
        }}}]}
        self.assertEqual(features(enum), ["statement:CreateEnumStmt"])
        # DROP FUNCTION sample(uuid) contains real TypeName nodes nested in
        # list-valued fields; traversing those lists must retain their tags.
        tree = {"stmts": [{"stmt": {"DropStmt": {
            "removeType": "OBJECT_FUNCTION",
            "objects": [{"ObjectWithArgs": {
                "objname": [{"String": {"sval": "sample"}}],
                "objargs": [{"TypeName": {
                    "names": [{"String": {"sval": "uuid"}}],
                }}],
            }}],
        }}}]}
        self.assertEqual(features(tree), ["extended-type", "non-table-ddl"])
        # Scalar fields sharing a node-like name are also data, not nodes.
        tree["stmts"][0]["stmt"]["DropStmt"]["FuncCall"] = "quoted metadata"
        self.assertEqual(features(tree), ["extended-type", "non-table-ddl"])

    def test_oracle_failures_and_scripts_do_not_enter_valid_denominator(self):
        class Parser:
            class ParseError(Exception):
                pass

            @staticmethod
            def parse_sql_json(sql):
                if sql == "bad":
                    raise Parser.ParseError("bad syntax")
                return '{"stmts":[]}'
        self.assertEqual(oracle_case({"sql": "bad"}, Parser)["postgres"]["status"], "rejected")
        self.assertEqual(oracle_case({"sql": ""}, Parser)["postgres"]["status"], "extraction_error")
        rows = [
            dict(source="s", sql_sha256=str(i), postgres={"status": pg},
                 sqlean={"status": sq}, candidate_features=tags)
            for i, (pg, sq, tags) in enumerate((
                ("accepted", "rejected", ["case", "function"]),
                ("rejected", "rejected", []), ("accepted", "accepted", [])))
        ]
        summary = summarize(rows)
        self.assertEqual(summary["postgres_accepted"], 2)
        self.assertEqual(summary["sqlean_on_postgres_accepted"], {"accepted": 1, "rejected": 1})
        self.assertEqual(summary["candidate_features_in_rejected_queries"], {"case": 1, "function": 1})

    def test_failure_catalog_preserves_sql_and_uses_safe_fence(self):
        row = dict(id="a", source="s", sql="SELECT '```';", source_url="https://example.org",
                   postgres={"status": "accepted"}, candidate_features=[], duplicate_of=None,
                   sqlean={"status": "rejected", "diagnostic": "parse error: 1:1: test"})
        text = failure_catalog([row])
        self.assertIn("````sql\nSELECT '```';\n````", text)
        self.assertIn("parse error: 1:1: test", text)


if __name__ == "__main__":
    unittest.main()
