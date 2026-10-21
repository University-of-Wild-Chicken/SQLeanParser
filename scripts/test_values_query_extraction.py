"""Whole immutable VALUES inputs and independent metadata, never execution."""
from collections import Counter
from copy import deepcopy
import json
import unittest
from unittest.mock import patch

import extract_values_query_corpus as corpus


class ValuesQueryExtractionTests(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        cls.manifest = json.loads((corpus.DIRECTORY / 'concrete_sources.json').read_text())
        cls.registry = json.loads((corpus.DIRECTORY / 'source_contracts.json').read_text())
        cls.rows = corpus.reproduce(cls.manifest)
        cls.by_id = {r['id']: r for r in cls.registry}

    def test_fixed_population_is_whole_query_input_not_insert_values(self):
        with patch('subprocess.run', side_effect=AssertionError('SQL/source execution forbidden')):
            actual = corpus.reproduce(self.manifest)
        saved = [json.loads(s) for s in (corpus.DIRECTORY / 'concrete.jsonl').read_text().splitlines()]
        self.assertEqual(actual, saved)
        self.assertEqual(len(actual), 50)
        self.assertEqual(Counter(r['source'] for r in actual), {'postgres': 9, 'duckdb': 41})
        self.assertEqual(Counter(r['query_class'] for r in actual),
                         {'standalone-values': 7, 'select-containing-values': 43})
        for r in actual:
            self.assertEqual(r['sql'], r['raw_sql'])
            self.assertEqual(r['transformations'], [])
            self.assertFalse(r['source_sql_executed'])
            self.assertIsNone(r['parameter_types'])
            self.assertEqual(r['observed_parameter_slots'], [])
            self.assertIn(r['commit'], r['source_url'])
            self.assertIn('VALUES', r['sql'].upper())
            self.assertFalse(r['sql'].upper().lstrip().startswith('INSERT'))

    def test_manifest_rejects_changes_to_input_provenance_or_body_oracles(self):
        changes = [lambda m: m['selections'].pop(), lambda m: m['selections'].reverse(),
                   lambda m: m['selections'][0].update(id='replacement'),
                   lambda m: m['selections'][0].update(sql_sha256='0' * 64),
                   lambda m: m['selections'][0].update(normalized_tokens_sha256='0' * 64),
                   lambda m: m['sources']['duckdb'].update(commit='0' * 40),
                   lambda m: m['selections'][0]['values_body_columns'][0][0].update(type='text'),
                   lambda m: m['primary_sources'][0].update(sha256='0' * 64)]
        for change in changes:
            value = deepcopy(self.manifest)
            change(value)
            with self.assertRaisesRegex(ValueError, 'manifest changed'):
                corpus.reproduce(value)
        with patch.object(corpus, 'checked_file', side_effect=ValueError('file hash mismatch')):
            with self.assertRaisesRegex(ValueError, 'hash mismatch'):
                corpus.reproduce(self.manifest)

    def test_registry_is_closed_and_independent_of_checker(self):
        self.assertIs(corpus.validate_registry(self.manifest, self.registry), self.registry)
        self.assertEqual(len(self.registry), 50)
        self.assertEqual(sum(len(r['output_columns']) for r in self.registry), 65)
        self.assertTrue(all(r['catalogFile'] is None for r in self.registry))
        for row in self.rows:
            obs = row['observed_syntax']
            self.assertEqual(obs['external_relation_candidates'], [])
            self.assertEqual(obs['parameters'], [])
            self.assertEqual(obs['functions'], [])
            self.assertFalse(obs['lateral'])
        self.assertEqual(sum(bool(r['observed_syntax']['cte_names']) for r in self.rows), 2)

    def test_anonymous_derived_scope_is_an_explicit_additional_requirement(self):
        affected = [r for r in self.rows if r['observed_syntax']['anonymous_derived_relations']]
        self.assertEqual(len(affected), 12)
        self.assertEqual(sum(r['observed_syntax']['anonymous_derived_relations'] for r in affected), 12)
        self.assertEqual(self.manifest['required_grammar_features'],
                         {'values_query_body': 50, 'anonymous_derived_relation': 12})
        self.assertTrue(any(r['sql'].strip() == 'SELECT * FROM (VALUES (42, 43))' for r in affected))

    def test_registry_rejects_guessed_labels_types_nullability_and_catalogs(self):
        changes = [lambda r: r.pop(), lambda r: r[0].update(catalogFile='invented.json'),
                   lambda r: r[0]['output_columns'][0].update(name='invented'),
                   lambda r: r[0]['output_columns'][0].update(type='text'),
                   lambda r: r[0]['output_columns'][0].update(nullable=True),
                   lambda r: r[0]['output_columns'][0].update(collation='C')]
        for change in changes:
            value = deepcopy(self.registry)
            change(value)
            with self.assertRaisesRegex(ValueError, 'preregistered'):
                corpus.validate_registry(self.manifest, value)

    def test_all_unknown_and_nullability_use_postgresql_metadata(self):
        nulls = next(r for r in self.rows if r['sql'].strip() == 'SELECT * FROM (VALUES (NULL, NULL)) v1;')
        self.assertEqual(self.by_id[nulls['id']]['output_columns'], [
            {'name': 'column1', 'type': 'text', 'nullable': True, 'collation': 'default'},
            {'name': 'column2', 'type': 'text', 'nullable': True, 'collation': 'default'}])
        mixed = next(r for r in self.rows if r['sql'].strip() == 'VALUES (1,2), (3,4+4), (7,77.7);')
        self.assertEqual(self.by_id[mixed['id']]['output_columns'], [
            {'name': 'column1', 'type': 'int32', 'nullable': False, 'collation': None},
            {'name': 'column2', 'type': 'numeric', 'nullable': False, 'collation': None}])

    def test_post_coercion_modifier_expectations_are_fixed_before_checker(self):
        rows = [r for r in self.rows if r['source_file'].endswith('decimal_values_warning.test')]
        self.assertEqual(len(rows), 4)
        self.assertEqual([self.by_id[r['id']]['output_columns'][0]['type'] for r in rows],
                         ['numeric', 'numeric(38,24)', 'numeric', 'numeric'])
        self.assertTrue(all(self.by_id[r['id']]['output_columns'][0]['nullable'] for r in rows))
        self.assertTrue(all(r['extraction']['input_header'] == 'statement ok' for r in rows))
        self.assertIn('(NULL);', rows[0]['sql'])
        self.assertIn('(NULL::DECIMAL(38,24));', rows[1]['sql'])
        self.assertIn('(NULL::DECIMAL(10,2));', rows[2]['sql'])
        self.assertIn('(NULL::NUMERIC);', rows[3]['sql'])

    def test_selectors_reject_expression_fragments_and_header_changes(self):
        for kind in ['sql_slice', 'values_sqllogic_input']:
            s = next(s for s in self.manifest['selections'] if s['selector']['kind'] == kind)
            f = next(f for f in self.manifest['sources'][s['source']]['files'] if f['path'] == s['source_file'])
            text = (corpus.ROOT / f['local_path']).read_text()
            for key in set(s['selector']) - {'kind'}:
                selector = deepcopy(s['selector'])
                selector[key] += 1
                with self.assertRaises(ValueError):
                    corpus.selection(text, selector)

    def test_sql_logic_results_and_error_inputs_remain_opaque(self):
        source = ('statement error\nVALUES (broken);\n----\nquery I\nVALUES (999);\n\n'
                  'query I\nVALUES (12);\n----\nstatement ok\nVALUES (888);\n\n'
                  'statement ok\nVALUES (13);\n\n')
        inputs = list(corpus.sqllogic_inputs(source))
        self.assertEqual([sql.strip() for sql, *_ in inputs], ['VALUES (12);', 'VALUES (13);'])
        for sql, _, selector, _ in inputs:
            self.assertEqual(corpus.selection(source, selector)[0], sql)
        with self.assertRaisesRegex(ValueError, 'unsupported'):
            list(corpus.sqllogic_inputs('loop i 1 5\nquery I\nVALUES (1);\n----\n1\n\n'))
        with self.assertRaisesRegex(ValueError, 'delimiter'):
            list(corpus.sqllogic_inputs('query I\nVALUES (1);\n\n'))
        with self.assertRaisesRegex(ValueError, 'statement-ok'):
            list(corpus.sqllogic_inputs('statement ok\nVALUES (1);\n----\n1\n\n'))

    def test_complete_query_does_not_admit_dml_or_multiple_inputs(self):
        for sql in ['INSERT INTO t VALUES (1);', 'VALUES (1); SELECT 2;', '42', 'SELECT ${x}', 'VALUES (1)\x00']:
            with self.assertRaises(ValueError):
                corpus.complete_query(sql)
        for sql in ['VALUES (1);', '(VALUES (1), (2));', 'SELECT * FROM (VALUES (1)) t;']:
            corpus.complete_query(sql)

    def test_optional_oracle_mismatch_fails_closed(self):
        with patch.object(corpus, 'syntax_observation', return_value=({}, 'wrong')):
            with self.assertRaisesRegex(ValueError, 'observation changed'):
                corpus.reproduce(self.manifest, oracle=True)


if __name__ == '__main__':
    unittest.main()
