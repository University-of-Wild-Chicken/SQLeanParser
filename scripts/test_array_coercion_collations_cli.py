"""Frozen array-collation witnesses and fail-closed native evidence protocol."""
from collections import Counter
from contextlib import nullcontext, redirect_stdout
from copy import deepcopy
import io
import json
from pathlib import Path
import subprocess
import tempfile
import unittest
from unittest.mock import patch

import check_array_coercion_collations_cli as checker


def transcript(expected):
    return '\n'.join(line for item in expected for line in (
        'array-descriptor:' + item['key'], item['descriptor'],
        'array-metadata:' + item['key'], checker.canonical_json(item['metadata']))) + '\n'


def static_report(row):
    return {'status': 'valid', 'assurance': 'declarative', 'profile': checker.PROFILES['contract'],
            'evidence': 'declarative-derivation', 'catalogUnchanged': True, 'typePrecision': 'exact',
            'outputColumns': [{k: col[k] for k in ('name', 'type', 'nullable')}
                              for col in row['output_columns']],
            'outputCollations': [col['collation'] for col in row['output_columns']]}


class ArrayCoercionCollationsCliTests(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        cls.rows = checker.load_cases()

    def case(self, id_):
        return next(row for row in self.rows if row['id'] == id_)

    def test_frozen_native_controls_distinguish_array_scalar_and_raw_constructor_coercion(self):
        wanted = {
            'minimal-scalar-array-cast': ('name[]', True, 'C'),
            'minimal-coalesce-array-cast': ('name[]', False, 'C'),
            'raw-unknown-array-target': ('name[]', False, 'C'),
            'raw-typed-text-name': ('name[]', False, 'default'),
            'scalar-text-to-name-unchanged': ('name', True, 'default'),
            'minimal-conflicting-array-cast': ('name[]', True, None),
            'array-cat': ('name[]', False, None),
            'array-cat-reverse': ('text[]', False, 'POSIX'),
            'common-coalesce': ('name[]', False, None),
            'union-all-common': ('name[]', False, None),
            'null-array-POSIX': ('name[]', True, None),
        }
        for id_, expected in wanted.items():
            col = self.case(id_)['output_columns'][0]
            self.assertEqual(tuple(col[k] for k in ('type', 'nullable', 'collation')), expected)
        self.assertEqual(len(self.rows), 181)
        self.assertEqual(sum(len(row['inputs']) for row in self.rows), 192)
        self.assertEqual(Counter(row['category'] for row in self.rows)['cast-matrix'], 144)

    def test_same_oid_and_explicit_strength_controls_are_registered(self):
        for id_ in ['cast-name-name-POSIX-implicit', 'cast-varchar(3)-varchar(4)-POSIX-implicit',
                    'cast-char(3)-char(4)-POSIX-implicit', 'same-oid-varchar(3)-varchar',
                    'same-oid-varchar-varchar(4)', 'cast-text-name-POSIX-explicit',
                    'cast-text-name-POSIX-coalesce-explicit', 'cast-name-text-POSIX-implicit']:
            self.assertEqual(self.case(id_)['output_columns'][0]['collation'], 'POSIX')
        for id_ in ['cast-text-name-POSIX-implicit', 'cast-char(3)-name-POSIX-implicit',
                    'cast-varchar(3)-name-POSIX-implicit']:
            self.assertIsNone(self.case(id_)['output_columns'][0]['collation'])

    def test_registry_rejects_missing_added_reordered_or_modified_witness(self):
        for mutation in ['missing', 'extra', 'reordered', 'sql', 'source_kind', 'origin', 'category',
                         'inputs', 'output_columns', 'static_status']:
            rows = deepcopy(self.rows)
            if mutation == 'missing':
                rows.pop()
            elif mutation == 'extra':
                rows.append(deepcopy(rows[0]))
            elif mutation == 'reordered':
                rows.reverse()
            else:
                rows[0][mutation] = 'changed'
            with self.subTest(mutation=mutation), tempfile.TemporaryDirectory() as directory:
                path = Path(directory) / 'cases.json'
                path.write_text(json.dumps(rows))
                with patch.object(checker, 'FIXTURE', path), self.assertRaises(AssertionError):
                    checker.load_cases()

    def test_registry_rejects_duplicate_json_keys(self):
        text = checker.FIXTURE.read_text().replace('"source_kind": "synthetic"',
                '"source_kind": "synthetic", "source_kind": "synthetic"', 1)
        with tempfile.TemporaryDirectory() as directory:
            path = Path(directory) / 'cases.json'
            path.write_text(text)
            with patch.object(checker, 'FIXTURE', path), self.assertRaises(AssertionError):
                checker.load_cases()

    def test_static_report_requires_exact_metadata_and_independent_evidence(self):
        row = self.case('minimal-conflicting-array-cast')
        for mutation in [None, 'status', 'assurance', 'profile', 'evidence', 'catalogUnchanged',
                         'typePrecision', 'type', 'nullable', 'nullable-integer', 'missing-collation',
                         'wrong-collation', 'extra-collation', 'missing-column', 'diagnostic', 'sql', 'exit']:
            report = static_report(row)
            if mutation in ('type', 'nullable', 'nullable-integer'):
                report['outputColumns'][0]['nullable' if mutation.startswith('nullable') else 'type'] = (
                    1 if mutation == 'nullable-integer' else False if mutation == 'nullable' else 'text[]')
            elif mutation == 'missing-collation':
                report.pop('outputCollations')
            elif mutation == 'wrong-collation':
                report['outputCollations'] = ['POSIX']
            elif mutation == 'extra-collation':
                report['outputCollations'].append(None)
            elif mutation == 'missing-column':
                report['outputColumns'] = []
            elif mutation not in (None, 'exit'):
                report[mutation] = 'weaker'
            result = subprocess.CompletedProcess([], 1 if mutation == 'exit' else 0, json.dumps(report), '')
            with self.subTest(mutation=mutation):
                if mutation is None:
                    checker.validate_static(result, row)
                else:
                    with self.assertRaises(AssertionError):
                        checker.validate_static(result, row)

    def test_native_registers_all_inputs_and_both_output_forms(self):
        source_script, source = checker.native_script(self.rows)
        script, expected = checker.native_script(self.rows, [row['sql'] for row in self.rows])
        self.assertEqual(len(source), 373)
        self.assertEqual(len(expected), 554)
        self.assertEqual(script.count('\\gdesc'), 554)
        self.assertEqual(script.count('pg_collation_for(q.v)'), 554)
        self.assertEqual(source_script.count('\\gdesc'), 373)
        self.assertEqual(sum(item['key'].endswith(':source') for item in expected), 181)
        self.assertEqual(sum(item['key'].endswith(':postgres') for item in expected), 181)
        self.assertEqual(sum(':input-' in item['key'] for item in expected), 192)
        self.assertTrue(script.endswith('ROLLBACK;'))
        checker.validate_native(transcript(expected), expected)
        checker.validate_native(transcript(source), source)

    def test_metadata_observer_does_not_coerce_output_or_skip_indeterminate_identity(self):
        row = self.case('minimal-conflicting-array-cast')
        sql = checker.metadata_query(row['sql'])
        self.assertIn('pg_typeof(q.v)::TEXT', sql)
        self.assertIn('pg_typeof(q.v)::OID::BIGINT', sql)
        self.assertIn('pg_collation_for(q.v)', sql)
        self.assertIn('FROM (' + row['sql'] + ') q LIMIT 1;', sql)
        self.assertNotIn('CAST(q.v', sql)
        self.assertNotIn('RETURNS TABLE', sql)
        self.assertNotIn('NULL::TEXT', sql)
        _, expected = checker.native_script([row])
        self.assertIsNone(expected[-1]['metadata']['collation'])

    def test_native_script_rejects_omitted_canonical_or_non_authored_input(self):
        rows = deepcopy(self.rows[:2])
        for canonical in [[], [rows[0]['sql']], [rows[0]['sql'], ''], [rows[0]['sql'], None]]:
            with self.subTest(canonical=canonical), self.assertRaises(AssertionError):
                checker.native_script(rows, canonical)
        rows[0]['source_kind'] = 'downloaded'
        with self.assertRaises(AssertionError):
            checker.native_script(rows)
        with self.assertRaises(AssertionError):
            checker.native_script([self.rows[0], self.rows[0]])
        with self.assertRaises(AssertionError):
            checker.native_script([])

    def test_native_protocol_rejects_missing_extra_duplicate_reordered_and_garbage_records(self):
        _, expected = checker.native_script(self.rows[:2], [row['sql'] for row in self.rows[:2]])
        valid = transcript(expected).splitlines()
        variants = [[], valid[:-1], valid[1:], valid + ['unexpected'], valid[:4] + valid,
                    valid[4:8] + valid[:4] + valid[8:], [''] + valid, valid + [''],
                    valid[:3] + ['not-json'] + valid[4:]]
        for index, lines in enumerate(variants):
            with self.subTest(index=index), self.assertRaises((AssertionError, json.JSONDecodeError)):
                checker.validate_native('\n'.join(lines) + '\n', expected)
        with self.assertRaises(AssertionError):
            checker.validate_native('', [])
        with self.assertRaises(AssertionError):
            checker.validate_native(transcript(expected), expected + [expected[0]])

    def test_native_protocol_rejects_wrong_descriptor_modifier_and_identity(self):
        row = self.case('cast-text-varchar(4)-C-implicit')
        _, expected = checker.native_script([row])
        lines = transcript(expected).splitlines()
        for mutation in ['descriptor-name', 'descriptor-type', 'descriptor-typmod', 'marker',
                         'native-type', 'oid', 'string-oid', 'collation', 'missing-collation',
                         'extra-key', 'duplicate-key']:
            changed = list(lines)
            if mutation.startswith('descriptor'):
                changed[5] = {'descriptor-name': 'wrong|character varying(4)[]',
                              'descriptor-type': 'v|name[]',
                              'descriptor-typmod': 'v|character varying[]'}[mutation]
            elif mutation == 'marker':
                changed[6] = 'array-metadata:unregistered'
            elif mutation == 'duplicate-key':
                changed[7] = changed[7].replace('"collation":', '"collation":null,"collation":', 1)
            else:
                data = json.loads(changed[7])
                if mutation == 'missing-collation':
                    data.pop('collation')
                else:
                    key, value = {'native-type': ('type', 'name[]'), 'oid': ('oid', 1003),
                                  'string-oid': ('oid', '1015'), 'collation': ('collation', '"POSIX"'),
                                  'extra-key': ('unregistered', None)}[mutation]
                    data[key] = value
                changed[7] = json.dumps(data)
            with self.subTest(mutation=mutation), self.assertRaises(AssertionError):
                checker.validate_native('\n'.join(changed) + '\n', expected)

    def test_json_null_collation_is_required_not_missing_or_string_null(self):
        _, expected = checker.native_script([self.case('minimal-conflicting-array-cast')])
        lines = transcript(expected).splitlines()
        for replacement in ['null', '"POSIX"', 'unknown', False, 0]:
            data = dict(expected[-1]['metadata'], collation=replacement)
            altered = lines[:-1] + [json.dumps(data)]
            with self.subTest(replacement=replacement), self.assertRaises(AssertionError):
                checker.validate_native('\n'.join(altered) + '\n', expected)

    def test_static_check_and_renderer_use_explicit_executable(self):
        row = self.rows[0]
        result = subprocess.CompletedProcess([], 0, json.dumps(static_report(row)), '')
        with patch.object(checker, 'EXE', Path('/tmp/frozen-sqlean')), patch.object(
                checker.subprocess, 'run', return_value=result) as invoke:
            checker.static_check(row)
            self.assertEqual(invoke.call_args.args[0][0], '/tmp/frozen-sqlean')
            self.assertEqual(invoke.call_args.kwargs['input'], row['sql'])
            with patch.object(checker, 'validate_report', return_value={}) as validate:
                checker.render('postgres', row['sql'])
                self.assertEqual(invoke.call_args.args[0], ['/tmp/frozen-sqlean', '--render-assurance', 'postgres'])
                validate.assert_called_once_with(result, 'postgres', row['sql'])

    def run_main(self, source_only):
        rows = self.rows[:2]
        _, expected = checker.native_script(rows, None if source_only else [row['sql'] for row in rows])
        args = ['check_array_coercion_collations_cli.py', '--local-bin', '/tmp/pg', '--exe', '/tmp/sqlean']
        if source_only:
            args.append('--source-only')
        results = [subprocess.CompletedProcess([], 0, '16.15\n', ''),
                   subprocess.CompletedProcess([], 0, transcript(expected), '')]
        with patch('sys.argv', args), patch.object(checker, 'EXE', checker.EXE), patch.object(
                checker, 'load_cases', return_value=rows), patch.object(
                checker, 'connection', return_value=nullcontext(['psql'])), patch.object(
                checker, 'run', side_effect=results) as native, patch.object(
                checker, 'static_check') as static, patch.object(
                checker, 'replay', side_effect=lambda mode, sql, **kwargs: {'sql': sql}) as render:
            output = io.StringIO()
            with redirect_stdout(output):
                checker.main()
            self.assertEqual(native.call_count, 2)
            self.assertEqual(static.call_count, 0 if source_only else 4)
            self.assertEqual(render.call_count, 0 if source_only else 4)
            script = native.call_args.kwargs['input']
            self.assertEqual(script.count('\\gdesc'), len(expected))
            self.assertEqual(':postgres' in script, not source_only)
            self.assertIn('source-only native preflight; no CLI claim' if source_only else 'source/canonical certificates',
                          output.getvalue())

    def test_source_only_never_invokes_cli_or_claims_canonical_evidence(self):
        self.run_main(True)

    def test_main_checks_both_certificates_and_all_native_observations(self):
        self.run_main(False)


if __name__ == '__main__':
    unittest.main()
