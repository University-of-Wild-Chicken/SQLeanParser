"""Protocol regressions for authored context values under real session changes."""
from copy import deepcopy
import json
from types import SimpleNamespace
import unittest
from unittest.mock import patch

import context_values_native_states as checker
from check_postgresql_cli import NULL


METADATA = {"current": "owner", "session": "owner", "database": "db",
            "system": None, "superuser": True}


def transcript(expected):
    lines = []
    for key, (arity, rows) in expected.items():
        lines += [key, ",".join(f'"column_{i}"' for i in range(arity))]
        for row in rows:
            lines.append(",".join(NULL if value is None else
                                  '"' + value.replace('"', '""') + '"' for value in row))
    return "\n".join(lines) + "\n"


class ContextNativeStateTests(unittest.TestCase):
    def test_script_distinguishes_role_session_schema_null_and_empty_array(self):
        script, expected = checker.state_script(METADATA, checker.SOURCE, "private_role", "private_session")
        self.assertEqual(len(expected), 11)
        rows = list(expected.values())
        self.assertEqual(rows[0][1][0][:6], ["pg_catalog", "pg_catalog", "owner", "owner", "owner", "owner"])
        self.assertEqual(rows[2][1][0][:2], [None, None])
        self.assertEqual(rows[2][1][0][8:10], ["{}", "{pg_catalog}"])
        self.assertEqual(rows[4][1][0][2:6], ["private_role"] * 3 + ["owner"])
        self.assertEqual(rows[6][1][0][2:6], ["private_session"] * 4)
        self.assertEqual(rows[8][1][0][2:6], ["owner"] * 4)
        self.assertEqual(rows[-1], (2, [["t", "t"]]))
        self.assertEqual(script.count("CREATE ROLE "), 2)
        self.assertEqual(script.count("ROLLBACK;"), 1)
        self.assertNotIn("COMMIT", script)
        self.assertIn('SET LOCAL SESSION AUTHORIZATION "private_session";', script)
        self.assertLess(script.index("ROLLBACK;"), script.index("AS restored"))
        self.assertIn("SET LOCAL statement_timeout = '5s';", script)

    def test_owner_and_role_names_are_quoted_as_data(self):
        metadata = {**METADATA, "current": "o'wner", "session": "o'wner"}
        script, expected = checker.state_script(metadata, checker.SOURCE, 'a"b', 'c"d')
        self.assertIn('CREATE ROLE "a""b" NOLOGIN', script)
        self.assertIn('SET LOCAL SESSION AUTHORIZATION "c""d";', script)
        self.assertIn("CURRENT_USER = 'o''wner'", script)
        self.assertEqual(list(expected.values())[0][1][0][2], "o'wner")

    def test_privilege_failure_is_explicit_not_a_skipped_observation(self):
        for metadata in ({**METADATA, "superuser": False}, {**METADATA, "current": "other"},
                         {**METADATA, "superuser": 1}):
            with self.subTest(metadata=metadata), patch.object(checker, "run",
                    return_value=SimpleNamespace(stdout=json.dumps(metadata))), self.assertRaises(RuntimeError):
                checker.setup_identity(["psql"])

    def test_setup_metadata_is_complete_and_nullable_system_identity_is_exact(self):
        with patch.object(checker, "run", return_value=SimpleNamespace(stdout=json.dumps(METADATA))):
            self.assertEqual(checker.setup_identity(["psql"]), METADATA)
        for key in METADATA:
            broken = dict(METADATA)
            del broken[key]
            with self.subTest(key=key), patch.object(checker, "run",
                    return_value=SimpleNamespace(stdout=json.dumps(broken))), self.assertRaises(AssertionError):
                checker.setup_identity(["psql"])
        named = {**METADATA, "system": "scram-sha-256:owner"}
        _, expected = checker.state_script(named, checker.SOURCE, "role", "session")
        self.assertTrue(all(row[1][0][-1] == named["system"] for row in list(expected.values())[:-1]))

    def pipeline(self, mutation=None):
        suffix = "0123456789abcdef"
        _, expected = checker.state_script(METADATA, "SELECT canonical;", "sqlean_context_role_" + suffix,
                                           "sqlean_context_session_" + suffix)
        actual = deepcopy(expected)
        if mutation:
            mutation(actual)
        with patch.object(checker, "setup_identity", return_value=METADATA), \
                patch.object(checker, "assert_report") as certify, \
                patch.object(checker, "replay", side_effect=[
                    {"sql": "SELECT identity;"}, {"sql": "SELECT canonical;"}]) as render, \
                patch.object(checker.uuid, "uuid4", return_value=SimpleNamespace(hex=suffix)), \
                patch.object(checker, "run", return_value=SimpleNamespace(stdout=transcript(actual))) as native:
            counts = checker.check_states(["psql"])
            self.assertEqual(certify.call_count, 2)
            self.assertEqual(certify.call_args_list[0].args[3], checker.COLUMNS)
            self.assertEqual(certify.call_args_list[1].args[0][-1], "SELECT canonical;")
            self.assertEqual([call.args[0] for call in render.call_args_list], ["identity", "postgres"])
            self.assertEqual(native.call_count, 1)
            self.assertEqual(native.call_args.kwargs["input"].count("SELECT canonical"), 5)
            return counts

    def test_all_five_states_and_both_forms_are_required_with_exact_counts(self):
        self.assertEqual(self.pipeline(), {
            "state_queries": 10, "state_values": 110, "static_queries": 2,
            "render_profiles": 2, "restoration_checks": 1, "role_cleanup_checks": 1})

    def test_missing_extra_or_duplicate_native_evidence_fails(self):
        def missing(records):
            del records[next(iter(records))]
        def extra(records):
            records["__SQLEAN_CASE_unexpected_1_1_source"] = (1, [["x"]])
        for mutate in (missing, extra):
            with self.subTest(mutate=mutate), self.assertRaises(AssertionError):
                self.pipeline(mutate)
        _, expected = checker.state_script(METADATA, checker.SOURCE, "role", "session")
        with self.assertRaises(ValueError):
            checker.parse_results(transcript(expected) + transcript(expected))

    def test_wrong_null_identity_and_failed_cleanup_are_detected(self):
        for index, column, value in [(2, 0, ""), (2, 8, None), (4, 5, "private_role"),
                                      (6, 2, "owner"), (8, 2, "private_role"), (10, 1, "f")]:
            def mutate(records, index=index, column=column, value=value):
                key = list(records)[index]
                records[key][1][0][column] = value
            with self.subTest(index=index, column=column), self.assertRaises(AssertionError):
                self.pipeline(mutate)


if __name__ == "__main__":
    unittest.main()
