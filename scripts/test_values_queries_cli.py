#!/usr/bin/env python3
"""Protocol and independent semantic anchors for the finite VALUES harness."""
from contextlib import contextmanager, redirect_stdout
from copy import deepcopy
import io
import json
from pathlib import Path
import tempfile
from types import SimpleNamespace
import unittest
from unittest.mock import patch

import check_values_queries_cli as check


def transcript(expected):
    lines = []
    for item in expected:
        if item['kind'] == 'stages':
            lines += ['values-stages:' + item['key'], json.dumps(item['stages'])]
        else:
            lines += ['values-descriptor:' + item['key'], *item['descriptors'],
                      'values-rows:' + item['key'], json.dumps(item['rows']),
                      'values-metadata:' + item['key'], json.dumps(item['metadata'])]
    return '\n'.join(lines) + '\n'


def report(row):
    status = row.get('status', 'valid')
    result = {'status': status, 'assurance': 'declarative',
              'profile': check.PROFILES['contract'],
              'evidence': 'declarative-derivation' if status == 'valid' else 'none'}
    if status == 'valid':
        result.update(catalogUnchanged=True, typePrecision='exact',
                      outputColumns=[{k: c[k] for k in ('name', 'type', 'nullable')}
                                     for c in row['output_columns']],
                      outputCollations=[c['collation'] for c in row['output_columns']])
    else:
        result['diagnostic'] = {'code': row['diagnostic']}
    return result


class ValuesProtocolTests(unittest.TestCase):
    def setUp(self):
        self.rows = check.load_cases()
        self.boundaries = check.load_boundaries()
        self.by_shape = {r['shape']: r for r in self.rows}
        _, self.expected = check.native_script(self.rows, boundaries=self.boundaries)

    def rejects(self, stdout, expected=None):
        with self.assertRaises((AssertionError, ValueError, KeyError, TypeError)):
            check.validate_native(stdout, self.expected if expected is None else expected)

    def test_frozen_population_and_independent_common_type_anchors(self):
        self.assertEqual(len(self.rows), 50)
        anchors = {
            'simultaneous-null-null-int': ([[None], [None], [1]], 'int32', True),
            'simultaneous-unknown-conversion': ([[None], [2], [3]], 'int32', True),
            'all-null': ([[None], [None]], 'text', True),
            'array-null-elements': ([[[1, None]], [[2, 3]]], 'integer[]', False),
            'parameter-typmod-erasure': ([['ab'], ['xy']], 'varchar', False),
        }
        for shape, (rows, type_, nullable) in anchors.items():
            row = self.by_shape[shape]
            self.assertEqual(row['expected_rows'], rows)
            self.assertEqual(row['output_columns'][0]['type'], type_)
            self.assertIs(row['output_columns'][0]['nullable'], nullable)

    def test_names_modifiers_and_per_column_nullability(self):
        row = self.by_shape['derived-prefix-alias']
        self.assertEqual([c['name'] for c in row['output_columns']], ['n', 'column2'])
        self.assertEqual([c['nullable'] for c in self.by_shape['nullable-per-column']['output_columns']], [True, True])
        for base, agree, disagree in [('varchar', 'varchar(3)', 'varchar'),
                                      ('numeric', 'numeric(5,2)', 'numeric'),
                                      ('char', 'char(3)', 'bpchar')]:
            self.assertEqual(self.by_shape[base + '-modifier-agreement']['output_columns'][0]['type'], agree)
            self.assertEqual(self.by_shape[base + '-modifier-disagreement']['output_columns'][0]['type'], disagree)

    def test_parameter_occurrences_preserve_lexical_order_and_reuse(self):
        row = self.by_shape['anonymous-row-order']
        self.assertEqual(check.question_parameters(row['sql']), 'VALUES ($1,$2),($3,$4);')
        self.assertEqual(row['expected_rows'], [[1, 2], [3, 4]])
        row = self.by_shape['numbered-repeated-reordered']
        self.assertEqual(row['parameter_values'], [2, 7])
        self.assertEqual(row['expected_rows'], [[7, 2], [2, 7]])

    def test_complete_transcripts_and_exact_counts(self):
        check.validate_native(transcript(self.expected), self.expected)
        query = [e for e in self.expected if e['kind'] == 'query']
        self.assertEqual(len(query), 50)
        self.assertEqual(sum(len(e['descriptors']) for e in query), 58)
        self.assertEqual(len(self.expected) - len(query), 13)
        canonical = [r['sql'] for r in self.rows]
        boundary = [None if r['diagnostic'] == 'input.parse' else r['sql'] for r in self.boundaries]
        _, expected = check.native_script(self.rows, canonical, self.boundaries, boundary)
        self.assertEqual(len(expected), 124)  # 100 observations, 13 source + 11 canonical stages
        check.validate_native(transcript(expected), expected)

    def test_missing_extra_and_reordered_observations_fail(self):
        lines = transcript(self.expected).splitlines()
        self.rejects('\n'.join(lines[:-1]))
        self.rejects('\n'.join(lines + ['unexpected']))
        self.rejects('\n'.join(lines[1:]))
        mutated = deepcopy(self.expected)
        mutated[0], mutated[1] = mutated[1], mutated[0]
        self.rejects(transcript(mutated))
        self.rejects(transcript(self.expected), [])

    def test_descriptor_count_name_and_modifier_fail_closed(self):
        for replacement in [[], ['column1|bigint'], ['wrong|integer'],
                            ['column1|integer', 'column2|integer']]:
            mutated = deepcopy(self.expected)
            mutated[0]['descriptors'] = replacement
            self.rejects(transcript(mutated))
        mutated = deepcopy(self.expected)
        item = next(e for e in mutated if 'varchar-modifier-agreement' in e['key'])
        item['descriptors'] = ['column1|character varying']
        self.rejects(transcript(mutated))

    def test_rows_distinguish_boolean_integer_and_multiplicity(self):
        mutated = deepcopy(self.expected)
        mutated[0]['rows']['rows'][0]['column1'] = True
        self.rejects(transcript(mutated))
        mutated = deepcopy(self.expected)
        mutated[1]['rows']['rows'].pop(0)
        self.rejects(transcript(mutated))
        mutated = deepcopy(self.expected)
        mutated[1]['rows']['rows'].reverse()
        check.validate_native(transcript(mutated), self.expected)

    def test_ordered_result_must_keep_order(self):
        mutated = deepcopy(self.expected)
        item = next(e for e in mutated if 'ordered-limit' in e['key'])
        item['rows']['rows'].reverse()
        self.rejects(transcript(mutated))

    def test_empty_query_still_requires_native_metadata(self):
        item = next(e for e in self.expected if 'empty-derived' in e['key'])
        self.assertEqual(item['rows']['rows'], [])
        self.assertEqual(item['metadata']['rows'][0]['observed'][0]['oid'], 23)
        sql = check.metadata_sql(self.by_shape['empty-derived'], 'SELECT 1 WHERE FALSE')
        self.assertIn('LEFT JOIN (SELECT 1 WHERE FALSE)', sql)
        self.assertIn('pg_typeof(q.c0)', sql)
        self.assertNotIn('RETURNS TABLE', sql)
        self.assertNotIn('::integer', sql)

    def test_indeterminate_collation_is_required_real_null(self):
        for shape in ('implicit-collation-conflict', 'array-coercion-collation'):
            item = next(e for e in self.expected if shape in e['key'])
            self.assertIsNone(item['metadata']['rows'][0]['observed'][0]['collation'])
            for bad in ('"default"', '"C"', 'unknown'):
                mutated = deepcopy(self.expected)
                target = next(e for e in mutated if shape in e['key'])
                target['metadata']['rows'][0]['observed'][0]['collation'] = bad
                self.rejects(transcript(mutated))

    def test_native_metadata_requires_type_oid_and_column_count(self):
        for mutate in [lambda c: c.update(oid=20), lambda c: c.update(type='bigint'),
                       lambda c: c.pop('collation')]:
            mutated = deepcopy(self.expected)
            mutate(mutated[0]['metadata']['rows'][0]['observed'][0])
            self.rejects(transcript(mutated))
        mutated = deepcopy(self.expected)
        mutated[0]['metadata']['rows'][0]['observed'] = []
        self.rejects(transcript(mutated))

    def test_duplicate_json_fields_and_bad_row_protocol_rejected(self):
        valid = transcript(self.expected)
        self.rejects(valid.replace('"sqlstate": "00000"', '"sqlstate": "22012", "sqlstate": "00000"', 1))
        for bad in [{'sqlstate': '22012', 'rows': None}, {'sqlstate': '00000', 'rows': [], 'extra': True}]:
            mutated = deepcopy(self.expected)
            mutated[0]['rows'] = bad
            self.rejects(transcript(mutated))

    def test_distinct_analysis_plan_and_execution_boundaries(self):
        rows = {r['id']: r for r in self.boundaries}
        self.assertEqual([rows['division-runtime'][k] for k in ('prepare', 'plan', 'execute')], ['00000', '22012', '22012'])
        self.assertEqual([rows['literal-conversion'][k] for k in ('prepare', 'plan', 'execute')], ['22P02', None, None])
        self.assertEqual([rows['scalar-cardinality'][k] for k in ('prepare', 'plan', 'execute')], ['00000', '00000', '21000'])
        self.assertEqual(rows['values-boundary-finalizes-unknown']['status'], 'invalid')
        for id_ in ('division-runtime', 'literal-conversion', 'scalar-cardinality'):
            self.assertEqual(rows[id_]['status'], 'valid')
        mutated = deepcopy(self.expected)
        next(e for e in mutated if e['key'] == 'division-runtime:source')['stages']['prepare'] = '22012'
        self.rejects(transcript(mutated))

    def test_native_script_rejects_external_source_and_missing_canonical(self):
        row = deepcopy(self.rows[0])
        row['source_kind'] = 'postgresql-regression'
        for operation in [lambda: check.native_script([row]),
                          lambda: check.metadata_sql(row, row['sql']),
                          lambda: check.native_script(self.rows, []),
                          lambda: check.native_script(self.rows, [''] * 50),
                          lambda: check.native_script(self.rows, boundaries=self.boundaries, boundary_canonical=[]),
                          lambda: check.native_script(self.rows, boundaries=self.boundaries, boundary_canonical=[None] * 13),
                          lambda: check.native_script([self.rows[0], self.rows[0]])]:
            with self.assertRaises(AssertionError):
                operation()

    def test_fixture_mutations_cannot_redefine_registered_oracle(self):
        with tempfile.TemporaryDirectory() as directory:
            fixtures = Path(directory)
            (fixtures / 'schema.json').write_text(json.dumps(check.schema()))
            for mutate in [lambda r: r[0]['expected_rows'][0].__setitem__(0, True),
                           lambda r: r.pop(),
                           lambda r: r[0]['output_columns'][0].update(nullable=0),
                           lambda r: r[0].update(source_kind='downloaded')]:
                rows = deepcopy(self.rows); mutate(rows)
                (fixtures / 'synthetic.json').write_text(json.dumps(rows))
                with patch.object(check, 'FIXTURES', fixtures), self.assertRaises(AssertionError):
                    check.load_cases()

    def test_static_metadata_profile_precision_and_diagnostics_fail_closed(self):
        row = self.rows[0]
        def validate(value, row=row, code=0):
            return check.validate_static(SimpleNamespace(stdout=json.dumps(value), returncode=code), row)
        validate(report(row))
        for mutate in [lambda r: r.update(profile='stale'), lambda r: r.update(typePrecision='coarse'),
                       lambda r: r.update(outputCollations=[]), lambda r: r.update(outputColumns=[]),
                       lambda r: r['outputColumns'][0].update(nullable=0),
                       lambda r: r.update(diagnostic={'code': 'unexpected'})]:
            value = report(row); mutate(value)
            with self.assertRaises(AssertionError):
                validate(value)
        row = self.boundaries[2]
        value = report(row)
        check.validate_static(SimpleNamespace(stdout=json.dumps(value), returncode=check.EXIT_CODES['invalid']), row)
        value['diagnostic']['code'] = 'input.parse'
        with self.assertRaises(AssertionError):
            check.validate_static(SimpleNamespace(stdout=json.dumps(value), returncode=check.EXIT_CODES['invalid']), row)

    def test_source_only_main_never_calls_checker_or_renderer(self):
        @contextmanager
        def connection(args):
            yield ['psql-test']
        def run(args, **kwargs):
            if args[-1] == 'SHOW server_version':
                return SimpleNamespace(stdout='16.15\n')
            return SimpleNamespace(stdout=transcript(self.expected))
        with patch('sys.argv', ['check', '--source-only', '--local-bin', '/unused']), \
             patch.object(check, 'connection', connection), patch.object(check, 'run', run), \
             patch.object(check, 'validity', side_effect=AssertionError('checker called')), \
             patch.object(check, 'render', side_effect=AssertionError('renderer called')), \
             redirect_stdout(io.StringIO()) as output:
            check.main()
        self.assertIn('no typed/canonical claim', output.getvalue())

    def test_syntax_boundaries_use_structured_renderer_parse_diagnostics(self):
        row=next(r for r in self.boundaries if r['diagnostic']=='input.parse')
        value={'status':'invalid','assurance':'checked-roundtrip','profile':check.RENDER_PROFILES['identity'],
               'mode':'identity','evidence':'none','rendererVersion':'0.2','semanticPreservation':False,
               'diagnostic':{'code':'input.parse','message':'expected expression'}}
        result=SimpleNamespace(returncode=1,stdout=json.dumps(value))
        with patch.object(check.subprocess,'run',return_value=result) as invoke:
            self.assertEqual(check.validity(row),value)
        self.assertEqual(invoke.call_args.args[0],[str(check.EXE),'--render-assurance','identity'])
        self.assertEqual(invoke.call_args.kwargs['input'],row['sql'])
        for mutate in [lambda v:v.update(assurance='declarative'),lambda v:v.update(profile='stale'),
                       lambda v:v.update(evidence='checked-instance'),lambda v:v.update(semanticPreservation=0),
                       lambda v:v.update(sql='VALUES (1);'),lambda v:v.update(theorems=[]),
                       lambda v:v['diagnostic'].update(code='resource.depth')]:
            bad=deepcopy(value);mutate(bad)
            with self.subTest(report=bad),self.assertRaises(AssertionError):
                check.validate_static(SimpleNamespace(returncode=1,stdout=json.dumps(bad)),row)

    def test_empty_or_non_json_parse_stdout_cannot_pass(self):
        row=next(r for r in self.boundaries if r['diagnostic']=='input.parse')
        for stdout in ('','parse error: expected expression'):
            with self.subTest(stdout=stdout),self.assertRaises(json.JSONDecodeError):
                check.validate_static(SimpleNamespace(returncode=1,stdout=stdout),row)


if __name__ == '__main__':
    unittest.main()
