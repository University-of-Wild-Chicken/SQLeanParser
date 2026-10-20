"""The authored precedence guard must reject missing or wrong native evidence."""
from copy import deepcopy
import json
import sqlite3
import subprocess
import unittest
from unittest.mock import patch

import check_null_predicate_precedence as checker


def report(sql='SELECT 1;', mode='sqlite'):
    return {'mode': mode, 'profile': checker.PROFILES[mode],
            'assurance': 'checked-roundtrip', 'semanticPreservation': False,
            'status': 'rendered', 'parameterMap': [], 'sql': sql}


class NullPredicatePrecedenceTests(unittest.TestCase):
    def database(self):
        database = sqlite3.connect(':memory:')
        self.addCleanup(database.close)
        return database

    def test_exact_authored_populations_and_operator_interactions(self):
        sqlite, postgres = checker.sqlite_cases(), checker.postgres_cases()
        self.assertEqual((len(sqlite), len(postgres), len(checker.spelling_pairs())), (680, 252, 72))
        self.assertEqual(sqlite, sorted(set(sqlite)))
        self.assertEqual(postgres, sorted(set(postgres)))
        self.assertIn('SELECT 1 IS NULL || 0', sqlite)
        self.assertIn('SELECT 1 IS DISTINCT FROM 2 < 0', sqlite)
        self.assertIn('SELECT NOT 1 = 2 ISNULL', postgres)
        self.assertIn('SELECT 1 IS DISTINCT FROM 2 IS NULL', postgres)
        for spelling in checker.POSTFIX:
            self.assertTrue(any(spelling in sql for sql in sqlite))
        self.assertTrue(all(sql.startswith('SELECT ') and ';' not in sql for sql in sqlite + postgres))

    def test_native_boolean_special_cases_and_authored_value_anchors(self):
        database = self.database()
        for source, expected in checker.ANCHORS.items():
            self.assertEqual(checker.observation(database, source), ('int', expected))
        for source, alias in checker.spelling_pairs():
            checker.compare_sqlite(database, source, alias)
        self.assertNotEqual(checker.observation(database, 'SELECT 2 IS TRUE'),
                            checker.observation(database, 'SELECT 2 IS +TRUE'))

    def test_wrong_precedence_is_detected_for_null_tail_and_distinct_inequality(self):
        database = self.database()
        for original, wrong in (
            ('SELECT 1 IS NULL || 0', 'SELECT (1 IS NULL) || 0'),
            ('SELECT 1 IS DISTINCT FROM 2 < 0', 'SELECT (1 IS DISTINCT FROM 2) < 0'),
            ('SELECT 2 IS NOT NULL + NULL', 'SELECT (2 IS NOT NULL) + NULL'),
            ('SELECT 1 LIKE 2 = 0', 'SELECT 1 LIKE (2 = 0)'),
            ('SELECT 0 BETWEEN 0 AND 0 = 2', 'SELECT 0 BETWEEN 0 AND (0 = 2)'),
        ):
            with self.subTest(original=original), self.assertRaises(AssertionError):
                checker.compare_sqlite(database, original, wrong)

    def test_native_observations_do_not_collapse_null_text_integer_or_real(self):
        database = self.database()
        values = [checker.observation(database, sql) for sql in (
            'SELECT NULL', "SELECT 'NULL'", 'SELECT 1', 'SELECT 1.0', "SELECT '1'")]
        self.assertEqual(len(set(values)), 5)
        with self.assertRaises(AssertionError):
            checker.compare_sqlite(database, 'SELECT 1', 'SELECT 1.0')

    def test_missing_extra_rows_or_columns_fail(self):
        database = self.database()
        for sql in ('SELECT 1 WHERE FALSE', 'SELECT 1 UNION ALL SELECT 1', 'SELECT 1, 1'):
            with self.subTest(sql=sql), self.assertRaises(AssertionError):
                checker.observation(database, sql)

    def test_native_vm_budget_rejects_nonterminating_renderer_output(self):
        database = self.database()
        with self.assertRaises(sqlite3.OperationalError):
            checker.observation(database, 'WITH RECURSIVE t(n) AS '
                '(SELECT 1 UNION ALL SELECT n+1 FROM t) SELECT MAX(n) FROM t')
        self.assertEqual(checker.observation(database, 'SELECT 1'), ('int', 1))

    def test_invoke_checks_json_protocol_and_preserves_exact_input(self):
        source = 'SELECT NULL /* authored gap */ ISNULL'
        result = report('SELECT (NULL IS NULL);')
        with patch.object(checker.subprocess, 'run', return_value=subprocess.CompletedProcess(
                [], 0, json.dumps(result), '')) as command:
            self.assertEqual(checker.invoke(source, 'sqlite'), result)
        self.assertEqual(command.call_args.args[0][-1], source)
        self.assertEqual(command.call_args.args[0][1:3], ['--render-assurance', 'sqlite'])

    def test_renderer_protocol_mutations_fail_instead_of_becoming_missing_cases(self):
        changes = {
            'mode': 'identity', 'profile': 'another-profile', 'assurance': 'syntax',
            'semanticPreservation': True, 'status': 'unsupported',
            'parameterMap': [{'source': 1, 'target': 1}], 'sql': '',
        }
        for field, value in changes.items():
            value_report = report()
            value_report[field] = value
            with self.subTest(field=field), patch.object(checker.subprocess, 'run',
                    return_value=subprocess.CompletedProcess([], 0, json.dumps(value_report), '')):
                with self.assertRaises(AssertionError):
                    checker.invoke('SELECT 1', 'sqlite')
        for code, stdout, stderr in ((1, json.dumps(report()), ''),
                                     (0, json.dumps(report()), 'unexpected warning'),
                                     (0, json.dumps(report()) + '\n{}', '')):
            with patch.object(checker.subprocess, 'run',
                    return_value=subprocess.CompletedProcess([], code, stdout, stderr)):
                with self.assertRaises((AssertionError, json.JSONDecodeError)):
                    checker.invoke('SELECT 1', 'sqlite')

    def test_only_explicit_native_parse_rejection_is_accepted_for_pg_oracle(self):
        invalid = report(mode='identity')
        invalid.update(status='invalid', diagnostic={'code': 'input.parse'})
        for code, status, diagnostic, succeeds in ((1, 'invalid', 'input.parse', True),
                (0, 'invalid', 'input.parse', False), (1, 'invalid', 'representation.bad', False),
                (3, 'unsupported', 'input.parse', False)):
            changed = deepcopy(invalid)
            changed.update(status=status, diagnostic={'code': diagnostic})
            with patch.object(checker.subprocess, 'run',
                    return_value=subprocess.CompletedProcess([], code, json.dumps(changed), '')):
                if succeeds:
                    self.assertEqual(checker.invoke('SELECT 1 IS DISTINCT FROM', 'identity'), changed)
                else:
                    with self.assertRaises(AssertionError):
                        checker.invoke('SELECT 1 IS DISTINCT FROM', 'identity')

    def test_pg_tree_cleanup_removes_only_source_positions(self):
        original = {'version': 170007, 'stmts': [{'stmt_location': 0, 'stmt_len': 20,
            'stmt': {'A_Expr': {'location': 10, 'kind': 'AEXPR_DISTINCT', 'value': 1}}}]}
        expected = {'stmts': [{'stmt': {'A_Expr': {'kind': 'AEXPR_DISTINCT', 'value': 1}}}]}
        self.assertEqual(checker.clean_pg_tree(original), expected)
        wrong = deepcopy(original)
        wrong['stmts'][0]['stmt']['A_Expr']['kind'] = 'AEXPR_NOT_DISTINCT'
        self.assertNotEqual(checker.clean_pg_tree(original), checker.clean_pg_tree(wrong))

    def test_complete_default_pipeline_requires_all_authored_renderer_results(self):
        calls = []
        def identity(source, mode, executable):
            calls.append((source, mode))
            return report(source, mode)
        with patch.object(checker, 'invoke', side_effect=identity):
            self.assertEqual(checker.check_sqlite(), (680, 72, 19))
        self.assertEqual([source for source, _ in calls], checker.sqlite_cases() + list(checker.ANCHORS))
        self.assertEqual({mode for _, mode in calls}, {'sqlite'})

    def test_pipeline_fails_on_wrong_result_or_missing_rendering(self):
        for broken in (report('SELECT NULL'), {'status': 'unsupported'}):
            with patch.object(checker, 'invoke', return_value=broken):
                with self.assertRaises(AssertionError):
                    checker.check_sqlite()

    def test_sqlite_version_gate_is_explicit(self):
        with patch.object(checker.sqlite3, 'sqlite_version_info', (3, 38, 5)):
            with self.assertRaisesRegex(AssertionError, 'SQLite 3.39'):
                checker.check_sqlite()


if __name__ == '__main__':
    unittest.main()
