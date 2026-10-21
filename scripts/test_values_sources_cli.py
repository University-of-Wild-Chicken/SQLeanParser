"""Fail-closed protocol tests for inert whole-source VALUES certificates."""
from contextlib import redirect_stdout
from copy import deepcopy
import io
import json
from pathlib import Path
import tempfile
from types import SimpleNamespace
import unittest
from unittest.mock import patch

import check_values_sources_cli as check


def result(report, code=0, stderr=''):
    return SimpleNamespace(stdout=json.dumps(report), returncode=code, stderr=stderr)


def static_report(row):
    return {'status': 'valid', 'assurance': 'declarative',
            'profile': check.EXPECTED_CONTRACT_PROFILE, 'evidence': 'declarative-derivation',
            'catalogUnchanged': True, 'typePrecision': 'exact',
            'outputColumns': [{k: c[k] for k in ('name', 'type', 'nullable')} for c in row['output_columns']],
            'outputCollations': [c['collation'] for c in row['output_columns']]}


def render_report(mode, sql):
    return {'status': 'rendered', 'assurance': 'checked-roundtrip',
            'profile': check.renderer.PROFILES[mode], 'mode': mode, 'evidence': 'checked-instance',
            'rendererVersion': '0.2', 'semanticPreservation': False,
            'scope': 'SELECT AST serialization; independent target semantics not established',
            'assumptions': check.renderer.ASSUMPTIONS[mode],
            'trustedFoundations': sorted(check.renderer.FOUNDATIONS),
            'sql': sql.strip().removesuffix(';') + ';', 'parameterMap': [],
            'theorems': sorted(check.renderer.THEOREMS)}


class ValuesSourceProtocolTests(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        cls.pairs = check.load_sources()
        cls.rows = [{**s, 'output_columns': e['output_columns']} for s, e in cls.pairs]
        cls.lookup = {r['sql'].strip().removesuffix(';'): r for r in cls.rows}
        cls.observations = []
        for source, entry in cls.pairs:
            for phase in check.PHASES:
                sql = source['sql'] if phase == 'source-static' else source['sql'].strip().removesuffix(';') + ';'
                cls.observations.append({'id': source['id'], 'phase': phase, 'sql': sql,
                                         'source_sha256': source['sql_sha256'],
                                         'column_count': len(entry['output_columns']) if phase.endswith('-static') else 0})

    def fake_run(self, args, **kwargs):
        self.assertEqual(args[0], str(check.EXE))
        self.assertEqual(set(kwargs), {'input', 'cwd', 'text', 'capture_output', 'check', 'timeout'})
        self.assertIs(kwargs['check'], False)
        self.assertIs(kwargs['text'], True)
        self.assertIs(kwargs['capture_output'], True)
        self.assertEqual(kwargs['cwd'], check.ROOT)
        self.assertEqual(kwargs['timeout'], 30)
        sql = kwargs['input']
        row = self.lookup[sql.strip().removesuffix(';')]
        if args[1:] == ['--assurance', 'contract']:
            return result(static_report(row))
        self.assertIn(args[1:], [['--render-assurance', 'identity'], ['--render-assurance', 'postgres']])
        return result(render_report(args[-1], sql))

    def test_input_guard_preserves_frozen_50_and_65_with_empty_catalog(self):
        self.assertEqual(len(self.pairs), 50)
        self.assertEqual(sum(len(e['output_columns']) for _, e in self.pairs), 65)
        self.assertTrue(all(e['catalogFile'] is None for _, e in self.pairs))
        self.assertEqual(check.SOURCE_REGISTRY_SHA256, check.corpus.SOURCE_REGISTRY_SHA256)
        self.assertEqual(check.SOURCE_MANIFEST_SHA256, check.corpus.MANIFEST_SHA256)

    def test_fixture_corruptions_fail_before_any_cli_call(self):
        manifest = check.strict_json((check.FIXTURES / 'concrete_sources.json').read_text())
        registry = check.strict_json((check.FIXTURES / 'source_contracts.json').read_text())
        concrete = [s for s, _ in self.pairs]
        mutations = [
            ('concrete.jsonl', lambda x: x.pop()),
            ('concrete.jsonl', lambda x: x.append(deepcopy(x[0]))),
            ('concrete.jsonl', lambda x: x.reverse()),
            ('concrete.jsonl', lambda x: x[0].update(id=x[1]['id'])),
            ('concrete.jsonl', lambda x: x[0].update(sql='VALUES (999);')),
            ('concrete.jsonl', lambda x: x[0].update(source_sql_executed=0)),
            ('concrete.jsonl', lambda x: x[0].update(source_url='https://invented.invalid/')),
            ('concrete.jsonl', lambda x: x[0].update(parameter_types='int')),
            ('source_contracts.json', lambda x: x.pop()),
            ('source_contracts.json', lambda x: x[0].update(catalogFile='invented.json')),
            ('source_contracts.json', lambda x: x[0]['output_columns'][0].update(nullable=0)),
            ('source_contracts.json', lambda x: x[0]['output_columns'][0].update(type='text')),
            ('concrete_sources.json', lambda x: x['sources']['postgres'].update(commit='0' * 40)),
        ]
        with tempfile.TemporaryDirectory() as temp:
            directory = Path(temp)
            for name, mutate in mutations:
                values = {'concrete_sources.json': deepcopy(manifest), 'source_contracts.json': deepcopy(registry),
                          'concrete.jsonl': deepcopy(concrete)}
                mutate(values[name])
                for file, value in values.items():
                    text = ''.join(json.dumps(r) + '\n' for r in value) if file.endswith('.jsonl') else json.dumps(value)
                    (directory / file).write_text(text)
                with self.subTest(file=name), patch.object(check, 'FIXTURES', directory), \
                     patch.object(check, 'invoke', side_effect=AssertionError('CLI forbidden')), self.assertRaises((AssertionError, ValueError)):
                    check.load_sources()

    def test_missing_source_or_license_bytes_fail_reproduction(self):
        with patch.object(check.corpus, 'checked_file', side_effect=ValueError('source hash mismatch')):
            with self.assertRaisesRegex(ValueError, 'hash mismatch'):
                check.load_sources()

    def test_json_rejects_duplicate_keys_nonfinite_and_multiple_documents(self):
        for text in ['{"nullable":true,"nullable":false}', '{"x":{"a":1,"a":2}}',
                     '{"x":NaN}', '{"x":Infinity}', '{"x":-Infinity}', '{}\n{}', '']:
            with self.assertRaises((AssertionError, ValueError)):
                check.strict_json(text)
        with tempfile.TemporaryDirectory() as temp:
            directory = Path(temp)
            for file in ['concrete_sources.json', 'source_contracts.json', 'concrete.jsonl']:
                (directory / file).write_bytes((check.FIXTURES / file).read_bytes())
            p = directory / 'source_contracts.json'
            p.write_text(p.read_text().replace('"catalogFile": null', '"catalogFile": null, "catalogFile": null', 1))
            with patch.object(check, 'FIXTURES', directory), self.assertRaisesRegex(AssertionError, 'duplicate JSON'):
                check.load_sources()

    def test_static_exact_metadata_profile_boolean_and_status_guards(self):
        row = next(r for r in self.rows if len(r['output_columns']) == 3)
        check.validate_static(static_report(row), row)
        mutations = [lambda r: r.update(status='unsupported'), lambda r: r.update(status='invalid'),
                     lambda r: r.update(status='inconclusive'), lambda r: r.update(assurance='executable'),
                     lambda r: r.update(profile='sqlean-basic-select-v0.35'),
                     lambda r: r.update(evidence='checker-acceptance'), lambda r: r.update(typePrecision='family'),
                     lambda r: r.update(catalogUnchanged=1), lambda r: r.pop('outputCollations'),
                     lambda r: r.update(outputColumns=[]), lambda r: r['outputColumns'].reverse(),
                     lambda r: r['outputColumns'][0].update(name='wrong'),
                     lambda r: r['outputColumns'][0].update(type='bigint'),
                     lambda r: r['outputColumns'][0].update(nullable=0),
                     lambda r: r['outputColumns'][0].update(nullable=1),
                     lambda r: r['outputColumns'][0].update(extra=True),
                     lambda r: r['outputCollations'].reverse(),
                     lambda r: r['outputCollations'].__setitem__(0, False),
                     lambda r: r.update(diagnostic={'code': 'ignored'}), lambda r: r.update(sql='VALUES (1);')]
        for mutate in mutations:
            value = deepcopy(static_report(row)); mutate(value)
            with self.subTest(value=value), self.assertRaises((AssertionError, TypeError, KeyError)):
                check.validate_static(value, row)
        numeric = next(r for r in self.rows if r['output_columns'][0]['type'] == 'numeric(38,24)')
        value = static_report(numeric); value['outputColumns'][0]['type'] = 'numeric'
        with self.assertRaises(AssertionError):
            check.validate_static(value, numeric)

    def test_shared_validity_always_uses_empty_catalog_and_strict_transport(self):
        row = self.rows[0]
        previous = check.assurance.invoke
        with patch.dict(check.assurance.PROFILES, {'contract': check.EXPECTED_CONTRACT_PROFILE}), \
             patch.object(check.subprocess, 'run', side_effect=self.fake_run) as process, \
             patch.object(check.shared, 'validity', wraps=check.shared.validity) as valid:
            check.validity(row, row['sql'])
        self.assertIs(check.assurance.invoke, previous)
        self.assertIs(valid.call_args.kwargs['catalog'], False)
        self.assertEqual(process.call_args.args[0], [str(check.EXE), '--assurance', 'contract'])
        self.assertEqual(process.call_args.kwargs['input'], row['sql'])
        bad = result(static_report(row)); bad.stdout = bad.stdout.replace('"status": "valid"', '"status": "invalid", "status": "valid"')
        with patch.object(check.subprocess, 'run', return_value=bad), self.assertRaisesRegex(AssertionError, 'duplicate JSON'):
            check.validity(row, row['sql'])
        self.assertIs(check.assurance.invoke, previous)
        with check.shared_static_transport():
            for args in [['--assurance', 'contract', '--schema', 'x', row['sql']],
                         ['--assurance', 'contract', '--param-types', 'int', row['sql']]]:
                with self.assertRaises(AssertionError):
                    check.assurance.invoke(args)

    def test_process_guard_rejects_status_exit_noise_and_native_commands(self):
        row = self.rows[0]
        for code in [False, 1, 3, 4]:
            with patch.object(check.subprocess, 'run', return_value=result(static_report(row), code=code)), self.assertRaises(AssertionError):
                check.invoke(['--assurance', 'contract'], row['sql'])
        for output in ['[]', '{}\n{}', 'noise\n{}', '{"x":NaN}']:
            response = SimpleNamespace(stdout=output, stderr='', returncode=0)
            with patch.object(check.subprocess, 'run', return_value=response), self.assertRaises((AssertionError, ValueError)):
                check.invoke(['--assurance', 'contract'], row['sql'])
        with patch.object(check.subprocess, 'run', return_value=result(static_report(row), stderr='warning')), self.assertRaises(AssertionError):
            check.invoke(['--assurance', 'contract'], row['sql'])
        for args in [['psql'], ['--dsn', 'anything'], ['--assurance', 'syntax'], ['--schema', 'invented']]:
            with patch.object(check.subprocess, 'run', side_effect=AssertionError('must not run')), self.assertRaisesRegex(AssertionError, 'only inert'):
                check.invoke(args, row['sql'])

    def test_renderer_rejects_wrong_profiles_evidence_bindings_and_canonical_omission(self):
        sql = self.rows[0]['sql']
        value = render_report('postgres', sql)
        with patch.object(check.subprocess, 'run', return_value=result(value)):
            check.render('postgres', sql)
        mutations = [lambda r: r.update(profile='wrong'), lambda r: r.update(mode='identity'),
                     lambda r: r.update(status='unsupported'), lambda r: r.update(semanticPreservation=0),
                     lambda r: r.update(sql=None), lambda r: r.update(sql=''), lambda r: r.pop('sql'),
                     lambda r: r.update(sql='VALUES ($1);'),
                     lambda r: r.update(parameterMap=[{'source': {'style': 'numbered', 'index': 1}, 'target': 1}]),
                     lambda r: r['theorems'].append(r['theorems'][0]), lambda r: r['theorems'].pop(),
                     lambda r: r['trustedFoundations'].append('unchecked oracle'),
                     lambda r: r.update(diagnostic={'code': 'ignored'}),
                     lambda r: r['assumptions'].reverse()]
        for mutate in mutations:
            value = deepcopy(render_report('postgres', sql)); mutate(value)
            with patch.object(check.subprocess, 'run', return_value=result(value)), self.assertRaises((AssertionError, TypeError, KeyError)):
                check.render('postgres', sql)

    def test_all_sources_and_both_canonical_modes_are_checked_without_native_execution(self):
        with patch.dict(check.assurance.PROFILES, {'contract': check.EXPECTED_CONTRACT_PROFILE}), \
             patch.object(check.subprocess, 'run', side_effect=self.fake_run) as process, \
             patch.object(check.shared, 'postgres_script', side_effect=AssertionError('native SQL forbidden')), \
             patch.object(check.shared, 'connection', side_effect=AssertionError('native connection forbidden')), \
             patch.object(check.shared.sqlite3, 'connect', side_effect=AssertionError('SQLite forbidden')), \
             patch.object(check.shared, 'validity', wraps=check.shared.validity) as valid:
            summary = check.source_checks()
        self.assertEqual(summary, check.validate_observations(self.pairs, self.observations))
        self.assertEqual(process.call_count, 350)
        self.assertEqual(valid.call_count, 150)
        self.assertTrue(all(c.kwargs['catalog'] is False for c in valid.call_args_list))
        self.assertEqual(sum(c.args[0][1:] == ['--assurance', 'contract'] for c in process.call_args_list), 150)
        self.assertEqual(summary['static_column_positions'], 195)
        self.assertEqual(summary['internal_values_bodies_checked'], 0)
        self.assertIs(summary['source_sql_executed'], False)

    def test_missing_extra_reordered_and_empty_canonical_observations_fail(self):
        mutations = [lambda x: x.pop(), lambda x: x.append(deepcopy(x[0])),
                     lambda x: x.reverse(), lambda x: x[0].update(id=x[7]['id']),
                     lambda x: x[1].update(phase='postgres-render'),
                     lambda x: x[1].update(sql=''), lambda x: x[1].update(sql=None),
                     lambda x: x[2].update(sql='VALUES (999);'),
                     lambda x: x[3].update(sql='VALUES (998);'),
                     lambda x: x[3].update(column_count=True),
                     lambda x: x[3].update(source_sha256='0' * 64)]
        for mutate in mutations:
            values = deepcopy(self.observations); mutate(values)
            with self.assertRaises((AssertionError, TypeError)):
                check.validate_observations(self.pairs, values)

    def test_canonical_replay_drift_fails_the_actual_pipeline(self):
        calls = 0
        def invoke(args, **kwargs):
            nonlocal calls
            calls += 1
            response = self.fake_run(args, **kwargs)
            if calls == 3:
                data = json.loads(response.stdout); data['sql'] = 'VALUES (999);'
                response.stdout = json.dumps(data)
            return response
        with patch.dict(check.assurance.PROFILES, {'contract': check.EXPECTED_CONTRACT_PROFILE}), \
             patch.object(check.subprocess, 'run', side_effect=invoke), self.assertRaisesRegex(AssertionError, 'replay changed'):
            check.source_checks()
        self.assertEqual(calls, 3)

    def test_stale_profile_cannot_downgrade_the_preregistered_gate(self):
        with patch.dict(check.assurance.PROFILES, {'contract': 'sqlean-basic-select-v0.35'}), \
             patch.object(check.subprocess, 'run', side_effect=AssertionError('CLI should not run')), \
             self.assertRaisesRegex(AssertionError, 'no oracle downgrade'):
            check.source_checks()

    def test_inputs_only_main_never_invokes_a_process_or_claims_certificates(self):
        with patch('sys.argv', ['check_values_sources_cli', '--inputs-only', '--exe', '/unused']), \
             patch.object(check.subprocess, 'run', side_effect=AssertionError('no process allowed')), \
             patch.object(check, 'source_checks', side_effect=AssertionError('no certificate claim')), \
             patch.object(check, 'EXE', check.EXE), redirect_stdout(io.StringIO()) as output:
            check.main()
        self.assertIn('50 immutable whole VALUES sources / 65', output.getvalue())
        self.assertIn('no CLI or native claim', output.getvalue())


if __name__ == '__main__':
    unittest.main()
