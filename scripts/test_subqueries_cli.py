"""Fixed subquery models and missing/wrong native evidence must fail closed."""
from collections import Counter
from contextlib import nullcontext, redirect_stdout
from copy import deepcopy
import io
import json
from pathlib import Path
import shutil
import subprocess
import tempfile
import unittest
from unittest.mock import patch

import check_assurance_cli
import check_subqueries_cli as checker
from generate_subquery_examples import FACTORS, STATES, all_cases, schema, sql_in, sql_not
from test_set_operations_cli import native_transcript


class SubqueryCliTests(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        cls.rows = all_cases()

    def case(self, factor, shape):
        return next(row for row in self.rows if row['factor'] == factor + '_subquery' and row['shape'] == shape)

    def fixture_copy(self, rows=None, catalog=None):
        temporary = tempfile.TemporaryDirectory()
        self.addCleanup(temporary.cleanup)
        path = Path(temporary.name)
        (path / 'synthetic.json').write_text(json.dumps(self.rows if rows is None else rows))
        (path / 'schema.json').write_text(json.dumps(schema() if catalog is None else catalog))
        return path

    def test_fixed_150_cases_and_four_states(self):
        self.assertEqual(checker.load_cases(), self.rows)
        self.assertEqual(Counter(r['factor'] for r in self.rows), {f: 50 for f in FACTORS})
        self.assertEqual(len({r['sql'] for r in self.rows}), 150)
        self.assertEqual(sum(len(r['output_columns']) for r in self.rows), 159)
        self.assertTrue(all(set(r['expected_rows_by_state']) == set(STATES) for r in self.rows))

    def test_fixed_source_registry_has_78_certificates_and_72_render_only(self):
        sources = checker.load_sources()
        registered = [(source, entry) for source, entry in sources if entry]
        self.assertEqual(len(sources), 150)
        self.assertEqual(len(registered), 78)
        self.assertEqual(sum(len(entry['output_columns']) for _, entry in registered), 84)
        self.assertEqual(sum(entry['catalogFile'] is None for _, entry in registered), 37)
        self.assertEqual(Counter(source['factor'] for source, _ in registered), {'scalar': 32, 'exists': 22, 'in': 24})

    def test_source_registry_and_catalog_mutations_fail_closed(self):
        for change in ('missing', 'nullable', 'catalog_path', 'manifest', 'sql', 'source_free', 'executed', 'catalog'):
            with self.subTest(change=change), tempfile.TemporaryDirectory() as directory:
                root = Path(directory)
                target = root / 'fixtures/subqueries'
                shutil.copytree(checker.FIXTURES, target)
                registry = json.loads((target / 'source_contracts.json').read_text())
                if change in {'missing', 'nullable', 'catalog_path'}:
                    if change == 'missing': registry['scalar'].pop()
                    elif change == 'nullable': registry['scalar'][0]['output_columns'][0]['nullable'] = 1
                    else: registry['scalar'][0]['catalogFile'] = 'fixtures/subqueries/schema.json'
                    (target / 'source_contracts.json').write_text(json.dumps(registry))
                elif change == 'manifest':
                    manifest = json.loads((target / 'concrete_sources.json').read_text())
                    manifest['selections'][0]['sql_sha256'] = '0' * 64
                    (target / 'concrete_sources.json').write_text(json.dumps(manifest))
                elif change == 'catalog':
                    path = target / 'catalogs/source-01.json'
                    path.write_text(path.read_text() + ' ')
                else:
                    path = target / 'scalar_concrete.jsonl'
                    rows = [json.loads(line) for line in path.read_text().splitlines()]
                    if change == 'sql': rows[0]['sql'] += ' '
                    elif change == 'source_free': rows[0]['observed_syntax']['source_free'] = 1
                    else: rows[0]['source_sql_executed'] = True
                    path.write_text('\n'.join(map(json.dumps, rows)) + '\n')
                with patch.object(checker, 'ROOT', root), patch.object(checker, 'FIXTURES', target), self.assertRaises(AssertionError):
                    checker.load_sources()

    def test_source_stage_never_executes_and_only_certifies_fixed_registry(self):
        with patch.object(checker, 'run', side_effect=AssertionError('source SQL must never execute')), \
             patch.object(checker, 'validity') as valid, \
             patch.object(checker, 'replay', side_effect=lambda _, sql: {'sql': sql}) as render:
            self.assertEqual(checker.source_checks(), (78, 150))
        self.assertEqual(valid.call_count, 78 * 3)
        self.assertEqual(render.call_count, 150 * 2)
        self.assertEqual(sum(call.kwargs['catalog'] is False for call in valid.call_args_list), 37 * 3)
        allowed = {source['id'] for source, entry in checker.load_sources() if entry}
        self.assertEqual({call.args[0]['id'] for call in valid.call_args_list}, allowed)

    def test_loader_rejects_missing_mutated_and_bool_as_integer_metadata(self):
        for change in ('missing', 'duplicate', 'sql', 'nullable', 'collation', 'binding', 'state', 'value', 'catalog'):
            rows, catalog = deepcopy(self.rows), schema()
            if change == 'missing': rows.pop()
            elif change == 'duplicate': rows[-1] = deepcopy(rows[0])
            elif change == 'sql': rows[0]['sql'] += ' '
            elif change == 'nullable': rows[0]['output_columns'][0]['nullable'] = 1
            elif change == 'collation': rows[1]['output_columns'][0]['collation'] = 'C'
            elif change == 'binding': rows[33]['parameter_values'].reverse()
            elif change == 'state': rows[0]['expected_rows_by_state'].pop('empty')
            elif change == 'value': rows[0]['expected_rows_by_state']['empty'] = [[999]]
            else: catalog['tables'][0]['exposeUnqualified'] = 1
            with self.subTest(change=change), patch.object(checker, 'FIXTURES', self.fixture_copy(rows, catalog)):
                with self.assertRaises(AssertionError): checker.load_cases()

    def test_membership_model_distinguishes_empty_null_and_duplicate_rows(self):
        for left, values, expected in [(None, [], False), (None, [1], None), (2, [1, None], None),
                                       (1, [None, 1, 1], True), (2, [1, 1], False), (1, [], False)]:
            self.assertIs(sql_in(left, values), expected)
        self.assertIs(sql_not(None), None)
        self.assertIs(sql_not(False), True)
        row = self.case('in', 'outer-labels')
        self.assertEqual(row['expected_rows_by_state']['labels_only'], [[1, False], [1, False], [3, False], [5, False]])
        self.assertEqual(row['expected_rows_by_state']['both'], [[1, None], [1, None], [3, None], [5, None]])
        self.assertEqual(self.case('scalar', 'outer-rows')['expected_rows_by_state']['items_only'],
                         [[1, None], [2, None], [3, None], [4, None]])

    def test_scalar_metadata_is_exact_and_conservatively_nullable(self):
        for shape, type_, coll in [('unknown-null', 'text', 'default'), ('numeric-modifier', 'numeric(8,3)', None),
                                   ('name-collation', 'name', 'C'), ('stored-collation', 'text', 'C'),
                                   ('array-modifier', 'numeric(8,3)[]', None)]:
            c = self.case('scalar', shape)['output_columns'][0]
            self.assertEqual((c['type'], c['collation'], c['nullable']), (type_, coll, True))
        self.assertEqual(self.case('scalar', 'inherited-label')['output_columns'][0]['name'], 'inner_value')
        self.assertFalse(self.case('scalar', 'zero-row-coalesce')['output_columns'][0]['nullable'])
        self.assertFalse(self.case('exists', 'discarded-cardinality')['output_columns'][0]['nullable'])
        self.assertTrue(self.case('in', 'null-empty')['output_columns'][0]['nullable'])

    def test_lexical_parameter_order_binding_and_unused_children(self):
        row = self.case('scalar', 'numbered-reordered')
        self.assertEqual(checker.parameters(row['sql'], 'postgres'), [('numbered', 2), ('numbered', 1)])
        script = checker.capture(row, row['sql'])
        self.assertIn('EXECUTE subquery_parameters(2,7)', script[1])
        self.assertIn('SELECT $2-$1', script[0])
        row = self.case('in', 'unused-cte-parameters')
        self.assertEqual(checker.parameters(row['sql'], 'postgres'), [('anonymous', 1), ('anonymous', 2), ('anonymous', 3)])
        self.assertIn('SELECT $2 IN(SELECT $3)', checker.capture(row, row['sql'])[0])
        self.assertIn('EXECUTE subquery_parameters(100,7,7)', checker.capture(row, row['sql'])[1])

    def test_native_capture_counts_types_and_collations_are_separate(self):
        sql, expected = checker.postgres_script(self.rows, [r['sql'] for r in self.rows])
        self.assertEqual(len(expected), 2400)
        self.assertEqual(sum('_rows_' in key for key in expected), 1200)
        self.assertEqual(sum('_collations_' in key for key in expected), 1200)
        self.assertEqual(sql.count('PREPARE subquery_parameters'), 2400)
        self.assertIn('pg_typeof(q.c0)', sql)
        self.assertIn('t.typcollation<>0', sql)
        self.assertIn('pg_collation_for(q.c0)', sql)
        descriptions, wanted = checker.describe_script(self.rows, [r['sql'] for r in self.rows])
        self.assertEqual(len(wanted), 318)
        self.assertEqual(descriptions.count('\\gdesc'), 300)
        self.assertIn('v|numeric(8,3)', wanted)
        self.assertIn('inner_value|integer', wanted)
        self.assertIn('v|time(2) without time zone', wanted)

    def test_native_row_checker_rejects_missing_duplicate_wrong_value_and_null(self):
        rows = [self.case('scalar', 'unknown-null'), self.case('in', 'outer-labels')]
        _, expected = checker.postgres_script(rows, [r['sql'] for r in rows])
        transcript = native_transcript(expected)
        checker.validate_native(checker.parse_results(transcript), expected)
        for change in ('missing', 'extra', 'wrong', 'null', 'duplicate_row'):
            mutated = deepcopy(expected)
            key = next(iter(mutated))
            if change == 'missing': mutated.pop(key)
            elif change == 'extra': mutated[key + '_extra'] = mutated[key]
            elif change == 'wrong': mutated[key] = (1, [['wrong']])
            elif change == 'null': mutated[key] = (1, [['NULL']])
            else:
                key = next(k for k,v in mutated.items() if v[1])
                mutated[key][1].append(deepcopy(mutated[key][1][0]))
            with self.subTest(change=change), self.assertRaises(AssertionError):
                checker.validate_native(checker.parse_results(native_transcript(mutated)), expected)

    def test_boundary_stages_preserve_analysis_planning_and_execution_distinctions(self):
        rows = {r['id']: r for r in checker.boundary_cases()}
        self.assertEqual(len(rows), 38)
        self.assertEqual([rows['scalar-many'][s] for s in ('prepare', 'plan', 'execute')], ['00000', '00000', '21000'])
        self.assertEqual([rows['exists-offset-division'][s] for s in ('prepare', 'plan', 'execute')], ['00000', '22012', '22012'])
        self.assertEqual(rows['exists-discarded-division']['execute'], '00000')
        self.assertEqual(rows['exists-discarded-cardinality']['execute'], '00000')
        self.assertEqual(rows['in-unknown-null-child']['prepare'], '42883')
        self.assertEqual(rows['in-json-array-runtime']['execute'], '42883')
        _, expected = checker.analysis_script()
        checker.validate_stages('\n'.join(map(json.dumps, expected)), expected)
        for mutated in (expected[:-1], expected + [expected[0]], list(reversed(expected)),
                        [{**expected[0], 'prepare': '00000'}, *expected[1:]]):
            with self.assertRaises(AssertionError): checker.validate_stages('\n'.join(map(json.dumps, mutated)), expected)

    def test_static_boundaries_are_preregistered_and_wrong_codes_fail(self):
        cases = checker.boundary_cases()
        self.assertEqual(Counter(checker.boundary_classification(r)['status'] for r in cases),
                         {'valid': 13, 'invalid': 14, 'unsupported': 7, 'parse-excluded': 4})
        rows = {r['id']: checker.boundary_classification(r) for r in cases}
        self.assertEqual(rows['scalar-indeterminate-collation']['diagnostic'], 'scalar_subquery_collation')
        self.assertEqual(rows['in-row']['output_columns'],
                         [{'name': '?column?', 'type': 'bool', 'nullable': True, 'collation': None}])
        self.assertEqual(rows['exists-nullable-lock']['diagnostic'], 'subquery_planning_lock')
        self.assertEqual(rows['scalar-unknown-arithmetic']['diagnostic'], 'operator_signature')
        self.assertEqual(rows['exists-bad-operator']['diagnostic'], 'operator_signature')
        self.assertEqual(rows['exists-bad-literal']['status'], 'valid')
        self.assertEqual(rows['in-bad-left-literal']['status'], 'valid')
        parse = subprocess.CompletedProcess([],1,json.dumps({'status':'invalid','diagnostic':{'code':'input.parse'}}),'')
        with patch.object(checker, 'invoke', return_value=parse), \
             patch.object(checker, 'replay', side_effect=lambda _,sql: {'sql':sql}), \
             patch.object(checker, 'assert_report', return_value={'diagnostic':{'code':'wrong'}}):
            with self.assertRaises(AssertionError): checker.boundaries()

    def test_in_operator_input_collation_is_independently_observed(self):
        sql, expected = checker.operator_collation_script()
        self.assertEqual(len(expected), 8)
        self.assertEqual([r['input_collation'] for r in expected], ['default', 'default', 'C', 'POSIX', 'C', 'POSIX', None, 'POSIX'])
        self.assertIn('pg_rewrite', sql)
        self.assertIn(':inputcollid', sql)
        wrong = deepcopy(expected)
        wrong[0]['input_collation'] = None
        with self.assertRaises(AssertionError): checker.validate_stages('\n'.join(map(json.dumps, wrong)), expected)

    def test_recursive_sublink_registry_and_precise_static_boundaries(self):
        rows = checker.recursion_boundary_cases()
        self.assertEqual(Counter(r['prepare'] for r in rows), {'42P19': 9, '00000': 3, '0A000': 1})
        self.assertEqual(Counter(checker.recursion_boundary_classification(r)['status'] for r in rows),
                         {'invalid': 9, 'valid': 2, 'unsupported': 2})
        by_id = {r['id']: checker.recursion_boundary_classification(r) for r in rows}
        self.assertEqual(by_id['forward-via-exists']['diagnostic'], 'recursive_dependency')
        self.assertEqual(by_id['anchor-reference']['diagnostic'], 'recursive_reference')
        self.assertEqual(by_id['inner-shadow-allowed']['output_columns'],
                         [{'name': 'n', 'type': 'int32', 'nullable': True, 'collation': None}])
        with tempfile.TemporaryDirectory() as directory:
            path = Path(directory) / 'recursion_boundaries.json'
            path.write_text(json.dumps(rows[:-1]))
            with patch.object(checker, 'FIXTURES', Path(directory)), self.assertRaises(AssertionError):
                checker.recursion_boundary_cases()

    def test_recursive_sublinks_are_analyzed_without_planning_or_execution(self):
        rows = checker.recursion_boundary_cases()
        sql, expected = checker.recursion_script([r['sql'] for r in rows])
        self.assertEqual(len(expected), 26)
        self.assertEqual(expected[0], {'id': 'exists-step', 'form': 'source', 'prepare': '42P19'})
        self.assertEqual(expected[1], {'id': 'exists-step', 'form': 'postgres', 'prepare': '42P19'})
        self.assertIn("EXECUTE 'PREPARE subquery_guard AS '", sql)
        self.assertNotIn('EXPLAIN', sql)
        self.assertNotIn('EXECUTE subquery_guard;', sql)
        checker.validate_stages('\n'.join(map(json.dumps, expected)), expected)
        wrong = deepcopy(expected)
        wrong[0]['prepare'] = '00000'
        for changed in (expected[:-1], [*expected, expected[0]], list(reversed(expected)), wrong):
            with self.assertRaises(AssertionError): checker.validate_stages('\n'.join(map(json.dumps, changed)), expected)
        with self.assertRaises(AssertionError): checker.recursion_script([])

    def test_in_normalization_distinguishes_parent_vars_and_uncorrelated_sublinks(self):
        rows = checker.in_normalization_cases()
        self.assertEqual(Counter(r['prepare'] for r in rows), {'42P21': 4, '00000': 5})
        expected = {r['id']: checker.in_normalization_classification(r) for r in rows}
        for id_ in ('scalar-explicit-conflict', 'scalar-column-child-conflict', 'exists-wrapped-conflict', 'inquery-wrapped-conflict'):
            self.assertEqual(expected[id_], {'status': 'invalid', 'diagnostic': 'collation_conflict'})
        self.assertEqual(expected['scalar-variable-pairwise']['status'], 'valid')
        self.assertTrue(expected['scalar-implicit-conflict']['output_columns'][0]['nullable'])
        self.assertFalse(expected['inquery-variable-pairwise']['output_columns'][0]['nullable'])
        sql, prepared = checker.prepare_only_script(rows, [r['sql'] for r in rows])
        self.assertEqual(len(prepared), 18)
        self.assertNotIn('EXPLAIN', sql)
        self.assertNotIn('EXECUTE subquery_guard;', sql)
        changed = deepcopy(prepared)
        changed[0]['prepare'] = '00000'
        for transcript in (prepared[:-1], changed):
            with self.assertRaises(AssertionError): checker.validate_stages('\n'.join(map(json.dumps, transcript)), prepared)
        with self.assertRaises(AssertionError): checker.prepare_only_script([{**rows[0], 'source_kind': 'concrete'}])
        with tempfile.TemporaryDirectory() as directory:
            (Path(directory) / 'in_normalization_boundaries.json').write_text(json.dumps(rows[:-1]))
            with patch.object(checker, 'FIXTURES', Path(directory)), self.assertRaises(AssertionError):
                checker.in_normalization_cases()

    def test_sqlite_portable_subset_and_registered_cardinality_difference(self):
        rows = checker.sqlite_cases(self.rows)
        self.assertEqual(len(rows), 22)
        self.assertEqual(checker.sqlite_observations(rows, [r['sqlite_sql'] for r in rows]), 176)
        self.assertEqual([r['postgres_execute'] for r in rows if 'postgres_execute' in r], ['21000', '21000'])
        self.assertEqual([r['sqlite_expected_rows_by_state']['empty'] for r in rows[-2:]], [[[1]], [[2]]])

    def test_sqlite_binding_order_corruption_fails(self):
        row = deepcopy(next(r for r in checker.sqlite_cases(self.rows) if r.get('shape') == 'numbered-reordered'))
        row['parameter_values'].reverse()
        with self.assertRaises(AssertionError): checker.sqlite_observations([row], [row['sqlite_sql']])

    def test_native_execution_helpers_reject_downloaded_source_rows(self):
        row = {**self.rows[0], 'source_kind': 'concrete'}
        for operation in [lambda: checker.capture(row, row['sql']), lambda: checker.collation_query(row, row['sql']),
                          lambda: checker.postgres_script([row], [row['sql']]),
                          lambda: checker.describe_script([row], [row['sql']])]:
            with self.assertRaises(AssertionError): operation()
        with self.assertRaises(AssertionError): checker.postgres_script(self.rows, [])
        with self.assertRaises(AssertionError): checker.describe_script(self.rows, [])

    def test_static_report_requires_exact_metadata_and_collation(self):
        row = self.case('scalar', 'stored-collation')
        good = {'status': 'valid', 'assurance': 'declarative', 'profile': check_assurance_cli.PROFILES['contract'],
                'evidence': 'declarative-derivation', 'catalogUnchanged': True, 'typePrecision': 'exact',
                'outputColumns': [{k: c[k] for k in ('name','type','nullable')} for c in row['output_columns']],
                'outputCollations': ['C']}
        for field in (None, 'evidence', 'profile', 'typePrecision', 'outputCollations', 'nullable'):
            report = deepcopy(good)
            if field == 'outputCollations': report[field] = ['default']
            elif field == 'nullable': report['outputColumns'][0]['nullable'] = False
            elif field is not None: report[field] = 'wrong'
            with self.subTest(field=field), patch.object(check_assurance_cli, 'invoke', return_value=subprocess.CompletedProcess([],0,json.dumps(report),'')):
                if field is None: checker.validity(row)
                else:
                    with self.assertRaises(AssertionError): checker.validity(row)

    def main_with_corruption(self, corruption=None):
        rows = self.rows
        canonical = [r['sql'] for r in rows]
        value_sql, values = checker.postgres_script(rows, canonical)
        desc_sql, desc = checker.describe_script(rows, canonical)
        stage_sql, stages = checker.analysis_script()
        op_sql, ops = checker.operator_collation_script()
        recursion_sql, recursion = checker.recursion_script()
        normalization_sql, normalization = checker.prepare_only_script(checker.in_normalization_cases())
        outputs = {value_sql: native_transcript(values), desc_sql: '\n'.join(desc)+'\n',
                   stage_sql: '\n'.join(map(json.dumps, stages))+'\n', op_sql: '\n'.join(map(json.dumps, ops))+'\n',
                   recursion_sql: '\n'.join(map(json.dumps, recursion))+'\n',
                   normalization_sql: '\n'.join(map(json.dumps, normalization))+'\n'}
        if corruption == 'row':
            changed = deepcopy(values)
            key = next(iter(changed)); changed[key] = (1, [['wrong']])
            outputs[value_sql] = native_transcript(changed)
        elif corruption == 'descriptor': outputs[desc_sql] = '\n'.join(desc[:-1])+'\n'
        elif corruption == 'stage': outputs[stage_sql] = '\n'.join(map(json.dumps, stages[:-1]))+'\n'
        elif corruption == 'operator': outputs[op_sql] = '\n'.join(map(json.dumps, ops[:-1]))+'\n'
        elif corruption == 'recursion': outputs[recursion_sql] = '\n'.join(map(json.dumps, recursion[:-1]))+'\n'
        elif corruption == 'normalization': outputs[normalization_sql] = '\n'.join(map(json.dumps, normalization[:-1]))+'\n'
        def run(command, **kwargs):
            text = outputs[kwargs['input']] if 'input' in kwargs else '16.15\n'
            return subprocess.CompletedProcess(command, 0, text, '')
        with patch('sys.argv', ['check_subqueries_cli.py','--local-bin','/unused','--source-only']), \
             patch.object(checker, 'connection', return_value=nullcontext(['psql'])), \
             patch.object(checker, 'run', side_effect=run), patch.object(checker, 'replay', side_effect=AssertionError('unexpected CLI')), \
             patch.object(checker, 'validity', side_effect=AssertionError('unexpected CLI')), redirect_stdout(io.StringIO()):
            checker.main()

    def test_main_accepts_complete_protocol_and_fails_missing_wrong_evidence(self):
        self.main_with_corruption()
        for corruption in ('row', 'descriptor', 'stage', 'operator', 'recursion', 'normalization'):
            with self.subTest(corruption=corruption), self.assertRaises(AssertionError): self.main_with_corruption(corruption)


if __name__ == '__main__':
    unittest.main()
