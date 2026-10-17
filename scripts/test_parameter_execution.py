#!/usr/bin/env python3
"""Offline wiring/oracle regressions; these do NOT execute PostgreSQL."""
import copy
import unittest
from unittest.mock import patch

import check_parameter_execution as checker
from check_postgresql_cli import NULL, marker, parse_results
from test_postgresql_results import wire


class ParameterExecutionTests(unittest.TestCase):
    def setUp(self):
        self.cases = checker.load_cases()

    def result_model(self):
        results = {}
        for index, case, expected in self.cases:
            for populated in (False, True):
                for path in ('execute', 'literal'):
                    results[marker('parameter', index, populated, path)] = (
                        len(case['types']), copy.deepcopy(expected[int(populated)]))
                    if checker.advanced.mutates(case['sql']):
                        results[marker('parameter', index, populated, path, True)] = (4, [])
        return results

    def test_fixed_fixture_boundaries(self):
        cases = {i: c for i, c, _ in self.cases}
        self.assertEqual(cases[17]['sql'], 'SELECT $2, $1, $2;')
        self.assertEqual(checker.advanced.bind_parameters(cases[17]['sql'], cases[17]),
                         'SELECT (2::INTEGER), (1::INTEGER), (2::INTEGER);')
        self.assertIn("'?'", checker.advanced.question_parameters(cases[27]['sql']))
        self.assertEqual(checker.advanced.question_parameters("SELECT ?, '?', ?, 'it''s ?';"),
                         "SELECT $1, '?', $2, 'it''s ?';")

    def test_execute_capture_independent_of_literal_adapter(self):
        case = self.cases[1][1]
        with patch.object(checker.advanced, 'bind_parameters', side_effect=AssertionError('must not substitute')):
            capture = '\n'.join(checker.prepared_capture(case))
        self.assertIn('AS SELECT $2, $1, $2;', capture)
        self.assertIn('EXECUTE sqlean_parameters (1, 2)', capture)
        self.assertIn('RETURN QUERY EXECUTE', capture)
        self.assertIn('COPY (SELECT * FROM pg_temp.sqlean_execute_rows())', capture)
        self.assertIn('FORCE_QUOTE *', capture)
        self.assertNotIn('/dev/null', capture)

    def test_isolation_and_fail_closed_oracles(self):
        script = checker.database_script(self.cases)
        self.assertEqual(script.count('SAVEPOINT parameter_case;'), 104)  # save + rollback
        self.assertEqual(script.count('DEALLOCATE sqlean_parameters;'), 26)
        self.assertTrue(script.endswith('ROLLBACK;'))
        results = self.result_model()
        checker.verify(results, self.cases)
        for path in ('execute', 'literal'):
            bad = copy.deepcopy(results)
            bad[marker('parameter', 17, True, path)] = (3, [['1', '2', '1']])
            with self.assertRaises(AssertionError):
                checker.verify(bad, self.cases)
        bad = copy.deepcopy(results)
        for path in ('execute', 'literal'):
            bad[marker('parameter', 17, True, path)] = (3, [['9', '9', '9']])
        with self.assertRaises(AssertionError):
            checker.verify(bad, self.cases)  # equal paths are insufficient

    def test_missing_extra_state_and_arity_rejected(self):
        original = self.result_model()
        for key, value in [
            (marker('parameter', 22, True, 'execute', True), (4, [['changed']])),
            (marker('parameter', 17, True, 'execute'), (2, [['2', '1', '2']])),
            ('unexpected', (1, [])),
        ]:
            bad = copy.deepcopy(original)
            bad[key] = value
            with self.assertRaises(AssertionError):
                checker.verify(bad, self.cases)
        del original[marker('parameter', 24, False, 'execute')]
        with self.assertRaises(AssertionError):
            checker.verify(original, self.cases)

    def test_null_marker_roundtrip(self):
        index, case, expected = self.cases[-1]
        key = marker('parameter', index, False, 'execute')
        actual = parse_results(wire(expected[0], 4, key))[key]
        self.assertEqual(actual, (4, [[NULL, None, NULL, '']]))
        self.assertIn('NULL', '\n'.join(checker.prepared_capture(case)))


if __name__ == '__main__':
    unittest.main()
