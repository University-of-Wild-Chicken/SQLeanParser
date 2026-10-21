"""Row-IN semantic anchors and fail-closed CLI/native evidence protocols."""
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

import check_row_in_subqueries_cli as checker
from generate_row_in_subquery_examples import STATES, all_cases, cases, row_equal, row_in, schema
from test_set_operations_cli import native_transcript


class RowInSubqueriesCliTests(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        cls.rows = all_cases()
        cls.registry = json.loads((checker.FIXTURES / 'source_contracts.json').read_text())

    def case(self, shape):
        return next(row for row in self.rows if row['shape'] == shape)

    def fixture_copy(self, rows=None, catalog=None, sources=False):
        temporary = tempfile.TemporaryDirectory()
        self.addCleanup(temporary.cleanup)
        path = Path(temporary.name)
        (path / 'synthetic.json').write_text(json.dumps(self.rows if rows is None else rows))
        (path / 'schema.json').write_text(json.dumps(schema() if catalog is None else catalog))
        if sources:
            for name in ('concrete.jsonl', 'concrete_sources.json', 'source_contracts.json'):
                (path / name).write_bytes((checker.FIXTURES / name).read_bytes())
        return path

    def test_closed_fifty_queries_and_four_population_oracles(self):
        rows = checker.load_cases()
        self.assertEqual(rows, self.rows)
        self.assertEqual(len({r['shape'] for r in rows}), 50)
        self.assertEqual(len({r['sql'] for r in rows}), 50)
        self.assertTrue(all(set(r['expected_rows_by_state']) == set(STATES) for r in rows))
        self.assertEqual(sum(r['sqlite_supported'] for r in rows), 25)
        self.assertEqual(sum(len(r['output_columns']) for r in rows), 50)

    def test_row_equality_null_does_not_hide_a_definite_field_mismatch(self):
        for left, right, wanted in (
            ([1, None], [2, None], False),
            ([None, 1], [None, 2], False),
            ([1, None], [1, 2], None),
            ([None, None], [None, None], None),
            ([1, 2, 3], [1, 2, 3], True),
        ):
            with self.subTest(left=left, right=right):
                self.assertIs(row_equal(left, right), wanted)
        for left, right in (([], []), ([1, 2], [1])):
            with self.assertRaises(AssertionError):
                row_equal(left, right)

    def test_membership_true_unknown_false_priority_and_empty_null_rows(self):
        for left, right, wanted in (
            ([None, None], [], False),
            ([1, 2], [[1, None], [1, 2], [1, 2]], True),
            ([1, 2], [[1, None], [3, 4]], None),
            ([1, None], [[2, None], [3, None]], False),
            ([1, 2], [[3, 2], [1, 4]], False),
        ):
            self.assertIs(row_in(left, right), wanted)
        anchors = {
            'false-dominates-null': False, 'left-null': None, 'right-null': None,
            'both-null': None, 'empty': False, 'null-empty': False,
            'duplicate': True, 'match-beats-unknown': True,
            'unknown-beats-false': None, 'not-match': False,
            'not-unknown': None, 'not-empty': True,
        }
        for shape, wanted in anchors.items():
            for state in STATES:
                self.assertEqual(self.case(shape)['expected_rows_by_state'][state], [[wanted]])

    def test_independent_population_preserves_outer_and_join_multiplicity(self):
        data = {'items': [[8, None, 'N'], [8, None, 'N'], [9, 8, 'A']],
                'labels': [[8, 'A'], [8, 'B'], [9, 'C']]}
        rows = {r['shape']: r for r in cases(data)}
        self.assertEqual(rows['outer-items']['expected_rows'], [[None], [None], [True]])
        self.assertEqual(rows['outer-labels']['expected_rows'], [[True], [True], [True]])
        self.assertEqual(rows['join-duplicate-membership']['expected_rows'], [[True]] * 5)
        self.assertEqual(rows['item-score-membership']['expected_rows'], [[False]])

    def test_frozen_fixture_and_schema_reject_omissions_mutations_and_bool_integer_aliases(self):
        for change in ('missing', 'duplicate', 'sql', 'nullable_integer', 'row_boolean_integer',
                       'collation', 'binding', 'state', 'value', 'schema', 'schema_boolean_integer'):
            rows, catalog = deepcopy(self.rows), schema()
            if change == 'missing': rows.pop()
            elif change == 'duplicate': rows[-1] = deepcopy(rows[0])
            elif change == 'sql': rows[0]['sql'] += ' '
            elif change == 'nullable_integer': rows[0]['output_columns'][0]['nullable'] = 1
            elif change == 'row_boolean_integer': rows[0]['expected_rows_by_state']['empty'] = [[1]]
            elif change == 'collation': rows[0]['output_columns'][0]['collation'] = 'C'
            elif change == 'binding': next(r for r in rows if r['shape'] == 'numbered-reordered')['parameter_values'].reverse()
            elif change == 'state': rows[0]['expected_rows_by_state'].pop('empty')
            elif change == 'value': rows[0]['expected_rows_by_state']['empty'] = [[False]]
            elif change == 'schema': catalog['tables'][0]['columns'][0]['type'] = 'text'
            else: catalog['tables'][0]['exposeUnqualified'] = 1
            with self.subTest(change=change), patch.object(checker, 'FIXTURES', self.fixture_copy(rows, catalog)):
                with self.assertRaises(AssertionError):
                    checker.load_cases()

    def test_bound_parameters_cross_row_and_child_without_literal_substitution(self):
        row = self.case('numbered-reordered')
        capture = checker.shared.capture(row, row['sql'])
        self.assertIn('($4,$1)', capture[0])
        self.assertIn('SELECT $3,$2', capture[0])
        self.assertIn('EXECUTE subquery_parameters(2,2,1,1)', capture[1])
        row = self.case('cte-anonymous-global-order')
        self.assertEqual(checker.parameters(row['sql'], 'postgres'), [('anonymous', n) for n in range(1, 6)])
        capture = checker.shared.capture(row, row['sql'])
        self.assertIn('SELECT $1,$2', capture[0])
        self.assertIn('($3,$4) IN(SELECT a,b FROM c WHERE $5>0)', capture[0])
        self.assertIn('EXECUTE subquery_parameters(1,2,1,2,1)', capture[1])

    def test_native_capture_requires_both_forms_and_distinct_row_collation_evidence(self):
        canonical = [r['sql'] for r in self.rows]
        script, wanted = checker.shared.postgres_script(self.rows, canonical)
        self.assertEqual(len(wanted), 800)
        self.assertEqual(sum('_rows_' in k for k in wanted), 400)
        self.assertEqual(sum('_collations_' in k for k in wanted), 400)
        self.assertEqual(script.count('PREPARE subquery_parameters'), 800)
        self.assertIn('pg_typeof(q.c0)', script)
        self.assertIn('pg_collation_for(q.c0)', script)
        self.assertIn('LEFT JOIN', script)
        descriptors, expected = checker.shared.describe_script(self.rows, canonical)
        self.assertEqual(len(expected), 100)
        self.assertEqual(descriptors.count('\\gdesc'), 100)
        for operation in (checker.shared.postgres_script, checker.shared.describe_script):
            with self.assertRaisesRegex(AssertionError, 'missing canonical'):
                operation(self.rows, canonical[:-1])
        with self.assertRaisesRegex(AssertionError, 'missing canonical'):
            checker.shared.prepare_only_script(checker.boundary_cases(), [])

    def test_native_transcript_rejects_omissions_wrong_nulls_and_changed_multiplicity(self):
        rows = [self.case('left-null'), self.case('join-duplicate-membership')]
        _, expected = checker.shared.postgres_script(rows, [r['sql'] for r in rows])
        checker.validate_native(checker.parse_results(native_transcript(expected)), expected)
        for change in ('missing', 'extra', 'canonical_wrong', 'null_as_text', 'duplicate_row', 'wrong_width'):
            actual = deepcopy(expected)
            nonempty = next(k for k, (_, values) in actual.items() if values and '_rows_' in k)
            canonical = next(k for k, (_, values) in actual.items() if values and '_rows_' in k and 'postgres' in k)
            if change == 'missing': actual.pop(canonical)
            elif change == 'extra': actual[nonempty + '_extra'] = actual[nonempty]
            elif change == 'canonical_wrong': actual[canonical] = (1, [['wrong']])
            elif change == 'null_as_text': actual[nonempty] = (1, [['NULL']])
            elif change == 'wrong_width': actual[nonempty] = (2, [[None, None]])
            else: actual[nonempty][1].append(deepcopy(actual[nonempty][1][0]))
            with self.subTest(change=change), self.assertRaises(AssertionError):
                checker.validate_native(checker.parse_results(native_transcript(actual)), expected)

    def test_authored_sqlite_checks_execute_null_and_duplicate_anchors(self):
        rows = [{**r, 'sqlite_sql': r['sql'], 'sqlite_expected_rows_by_state': r['expected_rows_by_state']}
                for r in self.rows if r['sqlite_supported']]
        self.assertEqual(checker.shared.sqlite_observations(rows, [r['sql'] for r in rows]), 200)
        row = next(r for r in rows if r['shape'] == 'join-duplicate-membership')
        bad = deepcopy(row)
        bad['sqlite_expected_rows_by_state']['both'] = bad['sqlite_expected_rows_by_state']['both'][:1]
        with self.assertRaises(AssertionError):
            checker.shared.sqlite_observations([bad], [bad['sql']])
        null = next(r for r in rows if r['shape'] == 'left-null')
        canonical = 'SELECT FALSE AS v;'
        with self.assertRaises(AssertionError):
            checker.shared.sqlite_observations([null], [canonical])

    def test_prepare_controls_distinguish_arity_signature_collation_and_scope(self):
        controls = checker.boundary_cases()
        self.assertEqual(Counter(r['status'] for r in controls), {'invalid': 9, 'unsupported': 2})
        by_id = {r['id']: r for r in controls}
        for id_ in ('zero-fields', 'too-few-columns', 'too-many-columns'):
            self.assertEqual((by_id[id_]['diagnostic'], by_id[id_]['prepare']), ('in_row_subquery_arity', '42601'))
        self.assertEqual(by_id['finalized-null']['prepare'], '42883')
        self.assertEqual(by_id['left-explicit-conflict']['prepare'], '42P21')
        self.assertEqual(by_id['correlated-child']['diagnostic'], 'subquery_correlation')
        self.assertEqual(by_id['correlated-child']['prepare'], '00000')
        script, expected = checker.shared.prepare_only_script(controls, [r['sql'] for r in controls])
        self.assertEqual(len(expected), 22)
        self.assertNotIn('EXPLAIN ', script)
        self.assertNotIn('EXECUTE subquery_guard(', script)
        checker.shared.validate_stages('\n'.join(map(json.dumps, expected)), expected)
        wrong = [{**expected[0], 'prepare': '00000'}, *expected[1:]]
        for actual in (expected[:-1], expected + [expected[0]], list(reversed(expected)), wrong):
            with self.assertRaises(AssertionError):
                checker.shared.validate_stages('\n'.join(map(json.dumps, actual)), expected)
        with patch.object(checker, 'assert_report', return_value={'diagnostic': {'code': 'wrong'}}), \
             patch.object(checker, 'replay', side_effect=lambda _, sql: {'sql': sql}):
            with self.assertRaises(AssertionError):
                checker.boundaries()

    def test_sources_only_render_all_inputs_and_certify_the_fixed_twelve(self):
        with patch('subprocess.run', side_effect=AssertionError('source execution forbidden')), \
             patch.object(checker.shared, 'validity') as valid, \
             patch.object(checker, 'replay', side_effect=lambda _, sql: {'sql': sql}) as render:
            self.assertEqual(checker.source_checks(), (12, 50))
        self.assertEqual(render.call_count, 112)
        self.assertEqual(Counter(c.args[0] for c in render.call_args_list), {'identity': 50, 'postgres': 62})
        self.assertEqual(valid.call_count, 24)
        self.assertEqual({c.args[0]['id'] for c in valid.call_args_list}, {r['id'] for r in self.registry})
        for call in valid.call_args_list:
            record = next(r for r in self.registry if r['id'] == call.args[0]['id'])
            catalog = call.kwargs.get('catalog', call.args[2] if len(call.args) > 2 else None)
            self.assertEqual(catalog, checker.ROOT / record['catalogFile'] if record['catalogFile'] else False)
            self.assertEqual(call.args[0]['output_columns'], record['output_columns'])

    def test_source_registry_manifest_and_saved_copy_guards_run_before_rendering(self):
        for change in ('registry_missing', 'registry_nullable', 'registry_catalog', 'manifest',
                       'source_missing', 'source_sql', 'source_executed', 'source_false_as_integer'):
            path = self.fixture_copy(sources=True)
            if change.startswith('registry'):
                value = json.loads((path / 'source_contracts.json').read_text())
                if change == 'registry_missing': value.pop()
                elif change == 'registry_nullable': value[0]['output_columns'][0]['nullable'] = not value[0]['output_columns'][0]['nullable']
                else: value[0]['catalogFile'] = None
                (path / 'source_contracts.json').write_text(json.dumps(value))
            elif change == 'manifest':
                value = json.loads((path / 'concrete_sources.json').read_text())
                value['selections'][0]['sql_sha256'] = '0' * 64
                (path / 'concrete_sources.json').write_text(json.dumps(value))
            else:
                value = [json.loads(line) for line in (path / 'concrete.jsonl').read_text().splitlines()]
                if change == 'source_missing': value.pop()
                elif change == 'source_sql': value[0]['sql'] += ' '
                elif change == 'source_executed': value[0]['source_sql_executed'] = True
                else: value[0]['source_sql_executed'] = 0
                (path / 'concrete.jsonl').write_text(''.join(json.dumps(row) + '\n' for row in value))
            with self.subTest(change=change), patch.object(checker, 'FIXTURES', path), \
                 patch.object(checker, 'replay') as render, patch.object(checker.shared, 'validity') as valid:
                with self.assertRaises((AssertionError, ValueError)):
                    checker.source_checks()
                render.assert_not_called()
                valid.assert_not_called()

    def main_protocol(self, fault=None):
        canonical = [r['sql'].rstrip(';') + ' /* postgres canonical */;' for r in self.rows]
        _, values = checker.shared.postgres_script(self.rows, canonical)
        _, descriptors = checker.shared.describe_script(self.rows, canonical)
        _, guards = checker.shared.prepare_only_script(checker.boundary_cases(), [r['sql'] for r in checker.boundary_cases()])
        if fault == 'canonical-row':
            key = next(k for k in values if '_rows_' in k and 'postgres' in k)
            values[key] = (1, [['wrong']])
        elif fault == 'descriptor-omission': descriptors.pop()
        elif fault == 'prepare-omission': guards.pop()
        elif fault == 'prepare-wrong-code': guards[0]['prepare'] = '00000'
        outputs = [native_transcript(values), '\n'.join(descriptors) + '\n', '\n'.join(map(json.dumps, guards)) + '\n',
                   '15.9\n' if fault == 'version' else '16.15\n']
        run_results = [subprocess.CompletedProcess([], 0, output, '') for output in outputs]
        diagnostics = {r['sql']: r['diagnostic'] for r in checker.boundary_cases()}
        with patch('sys.argv', ['check_row_in_subqueries_cli.py', '--dsn', 'mock']), \
             patch.object(checker, 'connection', return_value=nullcontext(['mock-psql'])), \
             patch.object(checker, 'run', side_effect=run_results) as native, \
             patch.object(checker.shared, 'validity') as valid, \
             patch.object(checker.shared, 'sqlite_observations', return_value=200), \
             patch.object(checker, 'replay', side_effect=lambda mode, sql: {'sql': sql.rstrip(';') + ' /* ' + mode + ' canonical */;'}) as render, \
             patch.object(checker, 'assert_report', side_effect=lambda args, *_: {'diagnostic': {'code': diagnostics[args[-1]]}}), \
             redirect_stdout(io.StringIO()) as output:
            checker.main()
        return native, valid, render, output.getvalue()

    def test_main_checks_complete_source_and_canonical_protocol(self):
        native, valid, render, output = self.main_protocol()
        self.assertEqual(native.call_count, 4)
        self.assertEqual(valid.call_count, 100)
        canonical_calls = [c for c in valid.call_args_list if len(c.args) > 1]
        self.assertEqual(len(canonical_calls), 50)
        self.assertTrue(all('/* postgres canonical */' in c.args[1] for c in canonical_calls))
        self.assertIn('400 typed rows + 400 collation captures', output)
        self.assertIn('100 descriptor positions, 22 PREPARE controls', output)
        self.assertIn('200 authored SQLite', output)
        self.assertEqual(Counter(c.args[0] for c in render.call_args_list), {'identity': 50, 'postgres': 61, 'sqlite': 25})

    def test_main_rejects_changed_canonical_results_and_missing_descriptor_or_prepare_evidence(self):
        for fault in ('canonical-row', 'descriptor-omission', 'prepare-omission', 'prepare-wrong-code', 'version'):
            with self.subTest(fault=fault), self.assertRaises(AssertionError):
                self.main_protocol(fault)


if __name__ == '__main__':
    unittest.main()
