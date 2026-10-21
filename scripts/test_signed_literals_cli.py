"""Fixed signed-literal oracles and fail-closed descriptor/value protocols."""
from contextlib import nullcontext, redirect_stdout
from copy import deepcopy
import io
import json
from pathlib import Path
import subprocess
import tempfile
import unittest
from unittest.mock import patch

import check_signed_literals_cli as checker


def transcript(expected):
    lines = []
    for result in expected:
        lines += ['signed-descriptor:' + result['key'], *result['descriptors'],
                  'signed-execution:' + result['key'], checker.canonical_json(result['execution'])]
    return '\n'.join(lines) + '\n'


class SignedLiteralsCliTests(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        cls.rows = checker.load_cases()

    def case(self, id_):
        return next(r for r in self.rows if r['id'] == id_)

    def test_preregistered_native_boundaries_and_execution_exclusions(self):
        self.assertEqual(len(self.rows), 70)
        self.assertEqual(sum(r['origin'] == 'astra2-native-boundary-matrix-62' for r in self.rows), 62)
        expected = {
            'matrix-10': ('integer', -2147483648),
            'matrix-11': ('bigint', 2147483648),
            'matrix-12': ('integer', -2147483648),
            'matrix-14': ('bigint', -2147483648),
            'matrix-37': ('bigint', -9223372036854775808),
            'matrix-38': ('numeric', 9223372036854775808),
            'matrix-39': ('bigint', -9223372036854775808),
            'matrix-41': ('numeric', -9223372036854775808),
            'matrix-54': ('bigint', 2147483648),
            'matrix-55': ('numeric', 9223372036854775808),
            'matrix-59': ('bigint[]', [2147483648]),
        }
        for id_, (typ, value) in expected.items():
            row = self.case(id_)
            col = row['output_columns'][0]
            self.assertEqual(col['postgres_type'], typ)
            self.assertEqual(row['execution']['rows'], [{col['name']: value}])
        for id_ in ['matrix-16', 'matrix-43', 'matrix-56', 'matrix-57',
                    'bigint-cast-barrier', 'bigint-scalar-barrier', 'parameter-overflow', 'text-cast-overflow']:
            row = self.case(id_)
            self.assertEqual(row['static_status'], 'valid')
            self.assertEqual(row['execution'], {
                'classification': 'excluded-runtime-overflow', 'sqlstate': '22003', 'rows': None})
        self.assertEqual(self.case('text-conversion-excluded')['execution']['sqlstate'], '22P02')
        self.assertTrue(self.case('matrix-56')['output_columns'][0]['nullable'])
        self.assertEqual(self.case('matrix-61')['execution']['rows'], [{'?column?': 2147483648}, {'?column?': 1}])

    def test_fixed_registry_digest_rejects_missing_extra_changed_or_reordered_evidence(self):
        for mutation in ['missing', 'duplicate', 'reorder', 'sql', 'source_kind', 'origin',
                         'parameter_types', 'parameter_values', 'output_columns', 'static_status', 'execution', 'extra']:
            rows = deepcopy(self.rows)
            if mutation == 'missing':
                rows.pop()
            elif mutation == 'duplicate':
                rows[1] = deepcopy(rows[0])
            elif mutation == 'reorder':
                rows.reverse()
            else:
                rows[0][mutation] = 'wrong'
            with tempfile.TemporaryDirectory() as directory:
                fixture = Path(directory) / 'cases.json'
                fixture.write_text(json.dumps(rows))
                with self.subTest(mutation=mutation), patch.object(checker, 'FIXTURE', fixture), self.assertRaises(AssertionError):
                    checker.load_cases()
        with tempfile.TemporaryDirectory() as directory:
            fixture = Path(directory) / 'cases.json'
            fixture.write_text(checker.canonical_json(self.rows))
            with patch.object(checker, 'FIXTURE', fixture):
                self.assertEqual(checker.load_cases(), self.rows)

    def good_report(self, row):
        return {'status': 'valid', 'assurance': 'declarative', 'profile': checker.PROFILES['contract'],
                'evidence': 'declarative-derivation', 'typePrecision': 'exact', 'catalogUnchanged': True,
                'outputColumns': [{k: c[k] for k in ('name', 'type', 'nullable')} for c in row['output_columns']],
                'outputCollations': [None]}

    def test_static_report_rejects_wrong_native_type_metadata_and_duplicate_json_keys(self):
        row = self.case('matrix-54')
        good = self.good_report(row)
        for mutation in [None, 'exit', 'status', 'assurance', 'profile', 'evidence', 'typePrecision',
                         'catalogUnchanged', 'outputCollations', 'name', 'type', 'nullable', 'diagnostic', 'sql', 'extra_column']:
            report, exit_code = deepcopy(good), 0
            if mutation == 'exit':
                exit_code = 3
            elif mutation in ['name', 'type', 'nullable']:
                report['outputColumns'][0][mutation] = 0 if mutation == 'nullable' else 'int32'
            elif mutation == 'extra_column':
                report['outputColumns'].append(deepcopy(report['outputColumns'][0]))
            elif mutation:
                report[mutation] = 'wrong'
            result = subprocess.CompletedProcess([], exit_code, json.dumps(report), '')
            with self.subTest(mutation=mutation):
                if mutation is None:
                    checker.validate_static(result, row)
                else:
                    with self.assertRaises(AssertionError):
                        checker.validate_static(result, row)
        duplicate = json.dumps(good)[:-1] + ',"status":"valid"}'
        with self.assertRaises(AssertionError):
            checker.validate_static(subprocess.CompletedProcess([], 0, duplicate, ''), row)

    def test_static_invocation_keeps_declared_parameter_type_and_original_sql(self):
        row = self.case('text-conversion-excluded')
        result = subprocess.CompletedProcess([], 0, json.dumps(self.good_report(row)), '')
        with patch.object(checker.subprocess, 'run', return_value=result) as run:
            checker.static_check(row)
        self.assertEqual(run.call_args.args[0], [str(checker.EXE), '--assurance', 'contract', '--param-types', 'text'])
        self.assertEqual(run.call_args.kwargs['input'], row['sql'])

    def test_native_script_describes_actual_prepared_outputs_and_preserves_bindings(self):
        rendered = [row['sql'] + ' /* rendered */' for row in self.rows]
        script, expected = checker.native_script(self.rows, rendered)
        self.assertEqual(len(expected), 140)
        self.assertEqual(script.count('\n\\gdesc\n'), 140)
        self.assertEqual(script.count('PREPARE signed_parameters'), 140)
        self.assertEqual(script.count('DEALLOCATE signed_parameters;'), 140)
        self.assertEqual(script.count('/* rendered */'), 70)
        self.assertNotIn('RETURNS TABLE', script)
        self.assertNotIn('EXECUTE signed_parameters;\n\\gdesc', script)
        self.assertIn('FOR item IN EXECUTE command LOOP', script)
        self.assertIn("EXECUTE signed_parameters('not-an-integer')\n\\gdesc", script)
        self.assertIn('PREPARE signed_parameters(text) AS SELECT -CAST($1 AS INTEGER);', script)
        self.assertIn('PREPARE signed_parameters(int) AS SELECT $1 + -(-9223372036854775808) AS v;', script)
        self.assertIn("SET LOCAL statement_timeout='5s';", script)
        self.assertTrue(script.startswith('BEGIN;') and script.endswith('ROLLBACK;'))
        for invalid in [rendered[:-1], rendered + ['SELECT 1'], [''] + rendered[1:]]:
            with self.assertRaises(AssertionError):
                checker.native_script(self.rows, invalid)
        unauthored = deepcopy(self.rows)
        unauthored[0]['source_kind'] = 'external'
        with self.assertRaises(AssertionError):
            checker.native_script(unauthored, rendered)

    def test_native_protocol_rejects_missing_extra_reordered_or_corrupted_observations(self):
        _, expected = checker.native_script(self.rows, [row['sql'] for row in self.rows])
        good = transcript(expected)
        checker.validate_native(good, expected)
        bad = [transcript(expected[:-1]), good + 'unexpected\n', transcript(expected[::-1]),
               good.replace('signed-descriptor:matrix-00:source', 'signed-descriptor:matrix-00:postgres', 1),
               good.replace('?column?|bigint', '?column?|integer', 1),
               good.replace('?column?|integer', 'wrong|integer', 1),
               good.replace('?column?|integer\n', '?column?|integer\nextra|integer\n', 1),
               good.replace('"sqlstate":"00000"', '"sqlstate":"22003"', 1),
               good.replace('"rows":[{"?column?":2147483647}]', '"rows":[]', 1),
               good.replace('2147483647}', '"2147483647"}', 1),
               good.replace('2147483647}', '2147483647.0}', 1),
               good.replace('"rows":null', '"rows":[]', 1),
               good.replace('"sqlstate":"00000"', '"sqlstate":"00000","sqlstate":"00000"', 1),
               good.replace('"sqlstate":"00000"', '"sqlstate":"00000","extra":true', 1)]
        for output in bad:
            with self.subTest(output=output[:100]), self.assertRaises((AssertionError, ValueError)):
                checker.validate_native(output, expected)

    def test_result_bags_preserve_duplicates_without_assuming_order(self):
        row = self.case('matrix-61')
        _, expected = checker.native_script([row], [row['sql']])
        reversed_rows = deepcopy(expected)
        for result in reversed_rows:
            result['execution']['rows'].reverse()
        checker.validate_native(transcript(reversed_rows), expected)
        duplicate = deepcopy(expected)
        duplicate[0]['execution']['rows'].append(duplicate[0]['execution']['rows'][0])
        with self.assertRaises(AssertionError):
            checker.validate_native(transcript(duplicate), expected)

    def exercise_main(self, *, source_only=False, failure=None):
        canonical = [r['sql'] if source_only else r['sql'] + ' /* rendered */' for r in self.rows]
        _, expected = checker.native_script(self.rows, canonical)
        native = transcript(expected[:-1] if failure == 'native' else expected)
        output = io.StringIO()
        argv = ['signed', '--local-bin', '/pg16'] + (['--source-only'] if source_only else [])
        with patch('sys.argv', argv), redirect_stdout(output), \
                patch.object(checker, 'static_check', side_effect=AssertionError('static') if failure == 'static' else None) as static, \
                patch.object(checker, 'replay', side_effect=AssertionError('renderer') if failure == 'renderer'
                             else lambda mode, sql, **kwargs: {'sql': sql + ' /* rendered */'}) as replay, \
                patch.object(checker, 'connection', return_value=nullcontext(['psql'])) as connection, \
                patch.object(checker, 'run', side_effect=[subprocess.CompletedProcess([], 0,
                             '17.0\n' if failure == 'version' else '16.15\n', ''),
                             subprocess.CompletedProcess([], 0, native, '')]) as run:
            try:
                checker.main()
            except AssertionError:
                if failure in ['static', 'renderer']:
                    connection.assert_not_called()
                raise
        return output.getvalue(), static, replay, run

    def test_main_source_only_never_claims_or_invokes_cli_evidence(self):
        output, static, replay, run = self.exercise_main(source_only=True)
        static.assert_not_called()
        replay.assert_not_called()
        self.assertIn('native-only preflight (source duplicated; no CLI claim)', output)
        self.assertEqual(run.call_args_list[1].kwargs['timeout'], 120)

    def test_main_checks_both_static_forms_and_all_renderer_certificates_before_native(self):
        output, static, replay, _ = self.exercise_main()
        self.assertEqual(len(static.call_args_list), 140)
        self.assertEqual([call.args[:2] for call in replay.call_args_list],
                         [(mode, r['sql']) for r in self.rows for mode in ('identity', 'postgres')])
        self.assertEqual(static.call_args_list[1].args, (self.rows[0], self.rows[0]['sql'] + ' /* rendered */'))
        self.assertIn('9 excluded evaluation failures per form remain statically valid', output)

    def test_main_fails_on_certificate_native_or_version_mismatch(self):
        for failure in ['static', 'renderer', 'native', 'version']:
            with self.subTest(failure=failure), self.assertRaises(AssertionError):
                self.exercise_main(failure=failure)


if __name__ == '__main__':
    unittest.main()
