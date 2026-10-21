"""Immutable whole-query inputs, retained declarations and honest static scope."""
from collections import Counter
from copy import deepcopy
import json
import unittest
from unittest.mock import patch

import extract_quantified_subquery_corpus as corpus


class QuantifiedSubqueryExtractionTests(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        cls.manifest = json.loads((corpus.DIRECTORY / 'concrete_sources.json').read_text())
        cls.registry = json.loads((corpus.DIRECTORY / 'source_contracts.json').read_text())
        cls.rows = corpus.reproduce(cls.manifest)

    def test_offline_exact_inputs_never_execute_sql_or_source_controls(self):
        with patch('subprocess.run', side_effect=AssertionError('execution forbidden')):
            rows = corpus.reproduce(self.manifest)
        saved = [json.loads(s) for s in (corpus.DIRECTORY / 'concrete.jsonl').read_text().splitlines()]
        self.assertEqual(rows, saved)
        self.assertEqual(len(rows), 84)
        self.assertEqual(Counter(r['query_class'] for r in rows), {'scalar': 50, 'row': 34})
        self.assertEqual(self.manifest['coverage_shortfall'], {'scalar': 0, 'row': 16})
        self.assertEqual(Counter(r['source'] for r in rows), {'duckdb': 75, 'materialize': 4, 'postgres': 3, 'calcite': 2})
        self.assertEqual(Counter(q for r in rows for q in r['quantifiers']), {'ANY': 46, 'SOME': 13, 'ALL': 25})
        self.assertEqual({q['operator'] for r in rows for q in r['quantified_queries']}, {'=', '<>', '<', '<=', '>', '>='})
        for row in rows:
            self.assertEqual(row['sql'], row['raw_sql'])
            self.assertEqual(row['transformations'], [])
            self.assertIs(row['source_sql_executed'], False)
            self.assertIsNone(row['parameter_types'])
            self.assertIn(row['commit'], row['source_url'])

    def test_manifest_rejects_reselection_or_changed_provenance(self):
        changes = [lambda m: m['selections'].pop(), lambda m: m['selections'].reverse(),
                   lambda m: m['selections'][0].update(id='replacement'),
                   lambda m: m['selections'][0].update(sql_sha256='0' * 64),
                   lambda m: m['selections'][0].update(normalized_tokens_sha256='0' * 64),
                   lambda m: m['selections'][0].update(quantifiers=['ALL']),
                   lambda m: m['sources']['duckdb'].update(commit='0' * 40),
                   lambda m: m['contexts'][0]['table']['columns'][0].update(nullable=False)]
        for change in changes:
            value = deepcopy(self.manifest)
            change(value)
            with self.assertRaisesRegex(ValueError, 'manifest changed'):
                corpus.reproduce(value)
        with patch.object(corpus, 'checked_file', side_effect=ValueError('file hash mismatch')):
            with self.assertRaisesRegex(ValueError, 'hash mismatch'):
                corpus.reproduce(self.manifest)

    def test_fixed_static_registry_and_rendering_only_exclusions(self):
        self.assertIs(corpus.validate_registry(self.manifest, self.registry), self.registry)
        self.assertEqual(len(self.registry), 80)
        self.assertEqual(sum(len(r['output_columns']) for r in self.registry), 93)
        self.assertEqual(sum(r['catalogFile'] is None for r in self.registry), 46)
        ids = {r['id'] for r in self.registry}
        excluded = [r for r in self.rows if r['id'] not in ids]
        self.assertEqual(Counter(r['source'] for r in excluded), {'postgres': 2, 'calcite': 2})
        for row in self.rows:
            if row['id'] in ids:
                for key in ['correlated', 'uncertain_scope', 'unresolved_scope', 'parameters']:
                    self.assertEqual(row['observed_syntax'][key], [])
            else:
                self.assertEqual(row['validity_scope'], 'rendering-only')
                self.assertIn('no static scope', row['scope_claim'])
        scalar = next(r for r in self.rows if r['sql'].strip() == 'SELECT 5 = SOME(SELECT 5)')
        null = next(r for r in self.rows if r['sql'].strip() == 'SELECT 5 = SOME(SELECT NULL::INTEGER)')
        by_id = {r['id']: r for r in self.registry}
        self.assertIs(by_id[scalar['id']]['output_columns'][0]['nullable'], False)
        self.assertIs(by_id[null['id']]['output_columns'][0]['nullable'], True)

    def test_original_population_and_expected_metadata_are_preserved(self):
        self.assertEqual(corpus.sha256(corpus.canonical(self.manifest['selections'][:50]).encode()),
                         corpus.ORIGINAL_SELECTIONS_SHA256)
        self.assertEqual(corpus.sha256(corpus.canonical(self.registry[:47]).encode()),
                         corpus.ORIGINAL_REGISTRY_SHA256)
        self.assertEqual(sum(len(r['output_columns']) for r in self.registry[:47]), 49)

    def test_deferred_values_never_pad_the_active_population(self):
        deferred = corpus.reproduce(self.manifest, deferred=True)
        saved = [json.loads(s) for s in (corpus.DIRECTORY / 'deferred_values.jsonl').read_text().splitlines()]
        self.assertEqual(deferred, saved)
        self.assertEqual(len(deferred), 17)
        active_ids = {r['id'] for r in self.rows}
        registry_ids = {r['id'] for r in self.registry}
        for row in deferred:
            self.assertEqual(row['query_class'], 'row')
            self.assertIn('VALUES', row['sql'].upper())
            self.assertTrue(row['coverage_gaps'])
            self.assertEqual(row['validity_scope'], 'rendering-only')
            self.assertNotIn(row['id'], active_ids | registry_ids)
        mixed = {'quantified_queries': [{'row_left': True}, {'row_left': False}]}
        with self.assertRaisesRegex(ValueError, 'mixed'):
            corpus.query_class(mixed)

    def test_registry_rejects_invented_types_labels_nullability_or_catalogs(self):
        changes = [lambda r: r.pop(), lambda r: r[0].update(catalogFile='invented.json'),
                   lambda r: r[0]['output_columns'][0].update(name='invented'),
                   lambda r: r[0]['output_columns'][0].update(type='text'),
                   lambda r: r[0]['output_columns'][0].update(nullable=False),
                   lambda r: r[0]['output_columns'][0].update(collation='C')]
        for change in changes:
            value = deepcopy(self.registry)
            change(value)
            with self.assertRaisesRegex(ValueError, 'preregistered'):
                corpus.validate_registry(self.manifest, value)

    def test_declarations_are_complete_preceding_inputs_not_inferred_from_queries(self):
        data = {(name, f['path']): (corpus.ROOT / f['local_path']).read_text()
                for name, src in self.manifest['sources'].items() for f in src['files']}
        corpus.validate_contexts(self.manifest, data)
        context = self.manifest['contexts'][0]
        source = data[context['source'], context['source_file']]
        sql, table = corpus.written_declaration(source, context['selector'])
        self.assertEqual(sql, context['sql'])
        self.assertEqual(table, context['table'])
        for key in ['header_start', 'start', 'end']:
            sel = deepcopy(context['selector'])
            sel[key] += 1
            with self.assertRaises(ValueError):
                corpus.written_declaration(source, sel)
        changed = deepcopy(self.manifest)
        changed['selections'][0]['scope_catalog_columns'] = {'integers': ['invented']}
        with self.assertRaisesRegex(ValueError, 'scope inventory'):
            corpus.validate_contexts(changed, data)

    def test_query_selectors_cannot_take_expression_fragments_or_expected_results(self):
        selection = next(s for s in self.manifest['selections'] if s['selector']['kind'] == 'setop_sqllogic_query')
        file = next(f for f in self.manifest['sources'][selection['source']]['files'] if f['path'] == selection['source_file'])
        text = (corpus.ROOT / file['local_path']).read_text()
        for key in ['header_line', 'start', 'end']:
            sel = deepcopy(selection['selector'])
            sel[key] += 1
            with self.assertRaises(ValueError):
                corpus.selection(text, sel)

    def test_optional_oracle_mismatch_is_not_silently_ignored(self):
        with patch.object(corpus, 'syntax_observation', return_value=({}, [], [], 'wrong')):
            with self.assertRaisesRegex(ValueError, 'observation changed'):
                corpus.reproduce(self.manifest, oracle=True)


if __name__ == '__main__':
    unittest.main()
