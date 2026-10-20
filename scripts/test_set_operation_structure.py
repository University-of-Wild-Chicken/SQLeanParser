"""Independent set grouping anchors and strict structural/native evidence."""
from contextlib import nullcontext, redirect_stdout
from copy import deepcopy
import io
import itertools
import json
from pathlib import Path
import sqlite3
import subprocess
import sys
import tempfile
import types
import unittest
from unittest.mock import patch

import check_set_operation_structure as checker


class SetOperationStructureTests(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        cls.rows, cls.gaps = checker.load_cases()

    def test_fixed_126_sources_cover_every_operator_pair_and_three_associations(self):
        ops = ("UNION", "UNION ALL", "INTERSECT", "INTERSECT ALL", "EXCEPT", "EXCEPT ALL")
        sources = [r["sql"] for r in self.rows]
        expected = [sql for a, b in itertools.product(ops, repeat=2) for sql in (
            f"SELECT 1 {a} SELECT 2 {b} SELECT 3",
            f"(SELECT 1 {a} SELECT 2) {b} SELECT 3",
            f"SELECT 1 {a} (SELECT 2 {b} SELECT 3)")]
        self.assertEqual(sources[:108], expected)
        self.assertEqual(len(sources), 126)
        self.assertIn("SELECT NULL UNION ALL (SELECT NULL UNION ALL SELECT 1)", sources)
        self.assertIn("(SELECT NULL UNION ALL SELECT NULL) UNION ALL SELECT 1", sources)
        self.assertTrue(all(r["source_kind"] == "synthetic" for r in self.rows + self.gaps))
        self.assertEqual([r["postgres16_sqlstate"] for r in self.gaps], ["00000"] * 4)
        self.assertEqual([r["pglast17_accepts"] for r in self.gaps], [True, True, False, False])

    def test_fixture_hash_rejects_missing_reordered_or_changed_boundary_evidence(self):
        original = json.loads(checker.FIXTURE.read_text())
        for change in ("missing", "duplicate", "order", "sql", "source", "wrapper_state",
                       "wrapper_pg17", "scope"):
            data = deepcopy(original)
            if change == "missing":
                data["postgres_raw_ast"].pop()
            elif change == "duplicate":
                data["postgres_raw_ast"][1] = deepcopy(data["postgres_raw_ast"][0])
            elif change == "order":
                data["postgres_raw_ast"].reverse()
            elif change == "sql":
                data["postgres_raw_ast"][0]["sql"] += " LIMIT 1"
            elif change == "source":
                data["postgres_raw_ast"][0]["source_kind"] = "downloaded"
            elif change == "wrapper_state":
                data["postgres16_wrapper_gaps"][0]["postgres16_sqlstate"] = "42601"
            elif change == "wrapper_pg17":
                data["postgres16_wrapper_gaps"][2]["pglast17_accepts"] = True
            else:
                data["scope"] = "universal semantic equivalence"
            with tempfile.TemporaryDirectory() as directory:
                path = Path(directory) / "structure.json"
                path.write_text(json.dumps(data))
                with self.subTest(change=change), patch.object(checker, "FIXTURE", path), \
                        self.assertRaises(AssertionError):
                    checker.load_cases()

    def test_independent_sqlite_bag_model_and_native_precedence_divergence(self):
        cases = checker.sqlite_cases()
        self.assertEqual(len(cases), 16)
        self.assertEqual(checker.apply_set("UNION ALL", [1, 1], [1, 2]), [1, 1, 1, 2])
        self.assertEqual(checker.apply_set("UNION", [1, 1], [1, 2]), [1, 2])
        self.assertEqual(checker.apply_set("INTERSECT", [1, 1], [1, 2]), [1])
        self.assertEqual(checker.apply_set("EXCEPT", [1, 1, 2], [1]), [2])
        with sqlite3.connect(":memory:") as database:
            for sql, expected in cases:
                self.assertEqual(checker.sqlite_observation(database, sql), expected)
            for sql, pg, sqlite in checker.ANCHORS:
                self.assertNotEqual(pg, sqlite)
                self.assertEqual(checker.sqlite_observation(database, sql), sqlite)
            for malformed in ("SELECT 1 AS renamed", "SELECT 1.0 AS v", "SELECT NULL AS v",
                              "SELECT 1 AS v,2 AS another"):
                with self.assertRaises(AssertionError):
                    checker.sqlite_observation(database, malformed)
            with self.assertRaises(sqlite3.OperationalError):
                checker.sqlite_observation(database,
                    "WITH RECURSIVE t(v) AS (SELECT 1 UNION ALL SELECT v+1 FROM t) SELECT v FROM t")
        with patch.object(checker, "replay", side_effect=lambda mode, sql: {"sql": sql}), \
                patch.object(checker, "rejected") as reject:
            self.assertEqual(checker.check_sqlite(), (32, 5))
        self.assertEqual([call.args for call in reject.call_args_list],
                         [(sql, "sqlite", status, code) for sql, status, code in checker.SQLITE_EXCLUSIONS])
        with patch.object(checker, "replay", return_value={"sql": "SELECT 99 AS v"}), \
                self.assertRaises(AssertionError):
            checker.check_sqlite()

    def test_gap_protocol_rejects_wrong_classification_or_success_evidence(self):
        for mode, status, code in (("postgres", "invalid", "input.parse"),
                                   ("sqlite", "unsupported", "coverage.sqlite.operand-local-clauses")):
            good = {"mode": mode, "status": status, "diagnostic": {"code": code}, "evidence": "none"}
            for change in (None, "exit", "mode", "status", "diagnostic", "evidence",
                           "sql", "parameterMap", "theorems", "stderr"):
                report = deepcopy(good)
                exit_code, stderr = (1 if status == "invalid" else 3), ""
                if change == "exit":
                    exit_code = 0
                elif change == "diagnostic":
                    report["diagnostic"]["code"] = "other"
                elif change == "stderr":
                    stderr = "unexpected output"
                elif change in ("mode", "status", "evidence"):
                    report[change] = "wrong"
                elif change:
                    report[change] = "forbidden evidence"
                result = subprocess.CompletedProcess([], exit_code, json.dumps(report), stderr)
                with self.subTest(mode=mode, change=change), patch.object(
                        checker.subprocess, "run", return_value=result) as invoke:
                    if change is None:
                        checker.rejected("SELECT 1", mode, status, code)
                    else:
                        with self.assertRaises(AssertionError):
                            checker.rejected("SELECT 1", mode, status, code)
                self.assertEqual(invoke.call_args.kwargs["input"], "SELECT 1")

    def test_parameter_transport_preserves_lexical_order_and_wrapper_gaps(self):
        queries = [
            {"sql": "SELECT ? UNION ALL SELECT ?"},
            {"sql": "SELECT $3 EXCEPT (SELECT $1 UNION ALL SELECT $3) LIMIT $2"},
        ]
        def rendering(mode, sql):
            if mode == "identity":
                return {"sql": sql}
            return {"sql": sql if "?" not in sql else "SELECT $1 UNION ALL SELECT $2"}
        with patch.object(checker, "replay", side_effect=rendering) as replay, \
                patch.object(checker, "rejected") as rejected:
            canonical = checker.postgres_renderings(queries, self.gaps)
        self.assertEqual(canonical[0], "SELECT $1 UNION ALL SELECT $2")
        self.assertEqual([call.args for call in replay.call_args_list],
                         [(mode, row["sql"]) for row in queries for mode in ("identity", "postgres")])
        self.assertEqual([call.args for call in rejected.call_args_list],
                         [(r["sql"], "postgres", "invalid", "input.parse") for r in self.gaps])
        with patch.object(checker, "replay", return_value={"sql": "SELECT $2 UNION ALL SELECT $1"}), \
                self.assertRaises(AssertionError):
            checker.postgres_renderings(queries[:1], [])

    def test_raw_ast_comparison_keeps_grouping_clauses_and_parameter_identity(self):
        source = {"SelectStmt": {"op": "SETOP_UNION", "all": True, "location": 10,
                  "larg": {"SelectStmt": {"parameter": 1}},
                  "rarg": {"SelectStmt": {"parameter": 2, "limitCount": 1}},
                  "sortClause": [{"sortby_dir": "SORTBY_DEFAULT", "location": 20}]}}
        target = deepcopy(source)
        target["SelectStmt"]["location"] = 99
        target["SelectStmt"]["sortClause"][0]["sortby_dir"] = "SORTBY_ASC"
        self.assertEqual(checker.clean_pg_tree(source), checker.clean_pg_tree(target))
        for field, value in (("all", False), ("op", "SETOP_EXCEPT"),
                             ("rarg", {"SelectStmt": {"parameter": 1}})):
            wrong = deepcopy(target)
            wrong["SelectStmt"][field] = value
            self.assertNotEqual(checker.clean_pg_tree(source), checker.clean_pg_tree(wrong))
        class ParseError(Exception):
            pass
        def parse(sql):
            if sql in {r["sql"] for r in self.gaps[2:]}:
                raise ParseError("PG17 multiple limit options")
            return json.dumps(source if sql == "source" else target)
        fake = types.SimpleNamespace(__version__="v7.21", get_postgresql_version=lambda: (17, 7),
            parser=types.SimpleNamespace(parse_sql_json=parse, ParseError=ParseError))
        with patch.dict(sys.modules, {"pglast": fake}):
            self.assertEqual(checker.check_postgres_ast([{"sql": "source"}], ["canonical"], self.gaps), (1, 4))
            with self.assertRaises(AssertionError):
                checker.check_postgres_ast([{"sql": "source"}], [], self.gaps)
            target["SelectStmt"]["all"] = False
            with self.assertRaises(AssertionError):
                checker.check_postgres_ast([{"id": "wrong", "sql": "source"}], ["canonical"], self.gaps)

    def test_native_pg16_wrapper_and_value_evidence_is_exact_and_not_pg17(self):
        script = checker.native_script(self.gaps, [source for source, _, _ in checker.ANCHORS])
        self.assertEqual(script.count("SELECT pg_temp.set_analysis("), 4)
        self.assertEqual(script.count("SELECT COALESCE(json_agg"), 4)
        self.assertIn("EXECUTE 'PREPARE set_probe AS ' || q", script)
        self.assertNotIn("EXECUTE set_probe", script)
        self.assertTrue(script.endswith("ROLLBACK;"))
        expected = ["00000"] * 4 + ["[1,2]", "[1,2]", "[1]", "[1]"]
        checker.validate_native("\n".join(expected) + "\n", self.gaps)
        for changed in (expected[:-1], expected + ["[]"], ["42601"] + expected[1:],
                        expected[:4] + ["[2]"] + expected[5:],
                        expected[:4] + ["[true,2]"] + expected[5:],
                        expected[:4] + ["[1.0,2]"] + expected[5:]):
            with self.assertRaises(AssertionError):
                checker.validate_native("\n".join(changed), self.gaps)
        with self.assertRaises(AssertionError):
            checker.native_script(self.gaps, [])

    def test_default_main_requires_all_tree_and_sqlite_observations_without_pg_dependency(self):
        output = io.StringIO()
        with patch.object(checker, "postgres_renderings", return_value=["canonical"] * 126) as render, \
                patch.object(checker, "check_sqlite", return_value=(32, 5)) as sqlite, \
                patch.object(checker, "connection") as connection, \
                patch("sys.argv", ["check_set_operation_structure.py"]), redirect_stdout(output):
            checker.main()
        render.assert_called_once_with(self.rows, self.gaps)
        sqlite.assert_called_once_with()
        connection.assert_not_called()
        self.assertIn("126 authored PostgreSQL tree roundtrips", output.getvalue())
        self.assertIn("4 explicit typed-parser wrapper gaps", output.getvalue())
        self.assertIn("32 source/canonical observations", output.getvalue())
        self.assertIn("no cross-dialect semantic equivalence claim", output.getvalue())
        for failure in ("postgres_renderings", "check_sqlite"):
            with patch.object(checker, "postgres_renderings", return_value=[]), \
                    patch.object(checker, "check_sqlite", return_value=(32, 5)), \
                    patch.object(checker, failure, side_effect=AssertionError("missing evidence")), \
                    patch("sys.argv", ["check_set_operation_structure.py"]), self.assertRaises(AssertionError):
                checker.main()


if __name__ == "__main__":
    unittest.main()
