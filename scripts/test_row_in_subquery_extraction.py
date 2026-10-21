"""Whole-input boundaries, immutable source populations and preregistered rows."""
from collections import Counter
from copy import deepcopy
import json
import unittest
from unittest.mock import patch

import extract_row_in_subquery_corpus as corpus


class PopulationTests(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        cls.manifest = json.loads((corpus.DIRECTORY / 'concrete_sources.json').read_text())
        cls.registry = json.loads((corpus.DIRECTORY / 'source_contracts.json').read_text())
        cls.rows = corpus.reproduce(cls.manifest)

    def test_fifty_unchanged_inputs_reproduce_offline_without_process_execution(self):
        with patch('subprocess.run', side_effect=AssertionError('source execution forbidden')):
            rows = corpus.reproduce(self.manifest)
        saved = [json.loads(line) for line in (corpus.DIRECTORY / 'concrete.jsonl').read_text().splitlines()]
        self.assertEqual(rows, saved)
        self.assertEqual(len(rows), 50)
        self.assertEqual(len({r['id'] for r in rows}), 50)
        self.assertEqual(Counter(r['source'] for r in rows),
                         {'hatchet': 10, 'postgres': 7, 'duckdb': 1, 'materialize': 5, 'sqlite': 25, 'calcite': 2})
        for row in rows:
            self.assertEqual(row['sql'], row['raw_sql'])
            self.assertEqual(row['transformations'], [])
            self.assertIs(row['source_sql_executed'], False)
            self.assertIsNone(row['parameter_types'])
            self.assertTrue(all(n >= 2 for n in row['row_in_arities']))

    def test_closed_manifest_does_not_silently_reselect(self):
        for mutate in (
            lambda m: m['selections'].pop(),
            lambda m: m['selections'][0].update(id='replacement'),
            lambda m: m['selections'][0].update(sql_sha256='0' * 64),
            lambda m: m['selections'][0].update(normalized_tokens_sha256='0' * 64),
            lambda m: m['selections'][0].update(row_in_arities=[1]),
            lambda m: m['expected_sources'].update(sqlite=24),
        ):
            changed = deepcopy(self.manifest)
            mutate(changed)
            with self.assertRaisesRegex(ValueError, 'manifest changed'):
                corpus.reproduce(changed)

    def test_fixed_certificate_population_and_rendering_only_scope(self):
        self.assertIs(corpus.validate_registry(self.manifest, self.registry), self.registry)
        self.assertEqual(len(self.registry), 12)
        self.assertEqual(sum(len(e['output_columns']) for e in self.registry), 20)
        self.assertEqual(sum(e['catalogFile'] is None for e in self.registry), 2)
        ids = {e['id'] for e in self.registry}
        for row in self.rows:
            if row['id'] in ids:
                self.assertEqual(row['scope_claim'], 'uncorrelated under fixed declarations')
                for k in ('correlated', 'uncertain_scope', 'unresolved_scope'):
                    self.assertEqual(row['observed_syntax'][k], [])
            else:
                self.assertEqual(row['validity_scope'], 'rendering-only')
                self.assertIn('no static scope', row['scope_claim'])
        # The source's descriptive alias is retained, but does not establish correlation.
        aliased = next(e for e in self.registry if e['output_columns'][0]['name'] == 'Correlated Field')
        self.assertIn(aliased['id'], ids)

    def test_registry_mutations_cannot_invent_output_metadata_or_eligibility(self):
        for mutate in (
            lambda r: r.pop(),
            lambda r: r[0]['output_columns'][0].update(name='invented'),
            lambda r: r[0]['output_columns'][0].update(type='text'),
            lambda r: r[0]['output_columns'][0].update(nullable=not r[0]['output_columns'][0]['nullable']),
            lambda r: r[0]['output_columns'][0].update(collation='C'),
            lambda r: r[0].update(catalogFile='invented.json'),
            lambda r: r[0].update(id=r[1]['id']),
        ):
            changed = deepcopy(self.registry)
            mutate(changed)
            with self.assertRaisesRegex(ValueError, 'preregistered'):
                corpus.validate_registry(self.manifest, changed)

    def test_written_declaration_catalogs_are_checked_without_result_inference(self):
        data = {(n, f['path']): (corpus.ROOT / f['local_path']).read_text()
                for n, source in self.manifest['sources'].items() for f in source['files']}
        corpus.validate_contexts(self.manifest, data)
        for mutate in (
            lambda m: m['contexts'][0]['table']['columns'][0].update(nullable=False),
            lambda m: m['contexts'][0].update(start=m['contexts'][0]['start'] + 1),
            lambda m: m['contexts'][0].update(sql='CREATE TABLE invented(x INT)'),
            lambda m: m['contexts'].pop(),
            lambda m: next(s for s in m['selections'] if s.get('context_ids'))['scope_catalog_columns'].update(invented=['x']),
        ):
            changed = deepcopy(self.manifest)
            mutate(changed)
            with self.assertRaises((ValueError, KeyError)):
                corpus.validate_contexts(changed, data)

    def test_boolean_row_in_outputs_remain_conservatively_nullable(self):
        for entry in self.registry:
            for field in entry['output_columns']:
                if field['type'] == 'bool':
                    self.assertIs(field['nullable'], True)
        literal = next(e for e in self.registry if e['id'].startswith('row-in:duckdb:'))
        self.assertEqual(literal['output_columns'], [{'name': '?column?', 'type': 'int32', 'nullable': False, 'collation': None}])


class InputBoundaryTests(unittest.TestCase):
    def tcl(self, text):
        command = corpus.COMMAND.search(text)
        start = command.end()
        return {'kind': 'whole_tcl_sql_argument', 'command_start': command.start(),
                'block_start': start, 'block_end': corpus.block_end(text, start - 1)}

    def test_whole_tcl_argument_preserves_missing_semicolon_and_whitespace(self):
        for sql in ('\n SELECT (1,2) IN (SELECT a,b FROM t)\n', 'SELECT (1,2) IN (SELECT 1,2);'):
            text = 'do_execsql_test 1.1 {' + sql + '} {1}\n'
            extracted, _, evidence = corpus.selection(text, self.tcl(text))
            self.assertEqual(extracted, sql)
            self.assertIs(evidence['controls_executed'], False)

    def test_whole_tcl_argument_rejects_fragments_assembly_and_substitution(self):
        cases = [
            'do_catchsql_test 1.1 {SELECT (1,2) IN (SELECT 1,2)} {1 error}\n',
            'execsql db {SELECT (1,2) IN (SELECT 1,2)}\n',
            'do_execsql_test 1.1 {SELECT 1; SELECT (1,2) IN (SELECT 1,2)} {1}\n',
            'do_execsql_test 1.1 {SELECT \\\n (1,2) IN (SELECT 1,2)} {1}\n',
            'do_execsql_test 1.1 {SELECT (1,2) IN (SELECT 1,2)}suffix\n',
        ]
        for text in cases:
            with self.subTest(text=text), self.assertRaises(ValueError):
                corpus.selection(text, self.tcl(text))
        text = 'do_execsql_test 1.1 {SELECT (1,2) IN (SELECT 1,2)} {1}\n'
        for key in ('command_start', 'block_start', 'block_end'):
            selected = self.tcl(text)
            selected[key] += 1
            with self.assertRaises(ValueError):
                corpus.selection(text, selected)

    def test_quidem_complete_query_does_not_require_a_saved_result_table(self):
        sql = 'SELECT (1,2) IN (SELECT a,b FROM t);'
        text = '# complete literal input\n' + sql + '\n\n# next test\nSELECT 1;\n'
        start = text.index(sql)
        selected = {'kind': 'quidem_complete_query_input', 'start': start, 'end': start + len(sql)}
        self.assertEqual(corpus.selection(text, selected)[0], sql)
        for key in ('start', 'end'):
            changed = dict(selected)
            changed[key] += 1
            with self.assertRaises(ValueError):
                corpus.selection(text, changed)

    def test_finite_declaration_grammar_requires_actual_supported_fields(self):
        self.assertEqual(corpus.declaration_table('CREATE TABLE t(a INT PRIMARY KEY, b TEXT COLLATE "C");'),
                         {'name': 't', 'columns': [{'name': 'a', 'type': 'int', 'nullable': False},
                                                  {'name': 'b', 'type': 'text', 'nullable': True}],
                          'columnCollations': [{'column': 'b', 'collation': 'C'}]})
        for sql in ('CREATE TABLE t(a)', 'CREATE TABLE t(a INT DEFAULT 1)',
                    'CREATE TABLE t(a INT, a TEXT)', 'CREATE TABLE t(a INT); DROP TABLE t;'):
            with self.assertRaises(ValueError):
                corpus.declaration_table(sql)


if __name__ == '__main__':
    unittest.main()
