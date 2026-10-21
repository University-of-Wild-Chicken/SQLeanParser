"""Whole-input provenance, conservative lexical scope and fixed source schemas."""
from collections import Counter
from copy import deepcopy
import hashlib
import json
from pathlib import Path
import unittest
from unittest.mock import patch

import extract_subquery_corpus as corpus
from extract_application_corpus import go_tokens
from extract_subquery_inputs import go_query, view_body, yaml_query, quidem_query
from extract_subquery_sqllogic import selected_subquery_sqllogic
from extract_statement_corpus import statement_spans
from observe_subquery_source import observe_tree


def column(*parts):
    return {'ColumnRef': {'fields': [{'String': {'sval': x}} for x in parts]}}


def query(value, sources=(), **extra):
    return {'SelectStmt': {'targetList': [{'ResTarget': {'val': value}}],
                           'fromClause': list(sources), 'op': 'SETOP_NONE', **extra}}


def table(name, alias=None):
    value = {'relname': name}
    if alias:
        value['alias'] = {'aliasname': alias}
    return {'RangeVar': value}


def link(value, kind='EXISTS_SUBLINK', **extra):
    return {'SubLink': {'subLinkType': kind, 'subselect': value, **extra}}


def literal(n=1):
    return {'A_Const': {'ival': {'ival': n}}}


def go_selector(source, needle):
    tokens = go_tokens(source)
    i = next(i for i, token in enumerate(tokens) if token.text == needle)
    return {'kind': 'go_query_token', 'start': tokens[i].start,
            'end': tokens[i].end, 'token_index': i}


def slt_selector(source, sql):
    start = source.index(sql)
    return {'kind': 'setop_sqllogic_query', 'start': start, 'end': start + len(sql),
            'header_line': source.count('\n', 0, start)}


class SourcePopulationTests(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        cls.manifest = json.loads((corpus.DIRECTORY / 'concrete_sources.json').read_text())
        cls.rows = corpus.reproduce(cls.manifest)

    def test_all_150_originals_reproduce_without_oracle_or_execution(self):
        self.assertEqual(len(self.rows), 150)
        self.assertEqual(Counter(r['factor'] for r in self.rows), {'exists': 50, 'scalar': 50, 'in': 50})
        self.assertEqual(len({r['id'] for r in self.rows}), 150)
        for factor in corpus.FACTORS:
            saved = [json.loads(line) for line in (corpus.DIRECTORY / f'{factor}_concrete.jsonl').read_text().splitlines()]
            self.assertEqual(saved, [r for r in self.rows if r['factor'] == factor])
        for row in self.rows:
            self.assertEqual(row['sql'], row['raw_sql'])
            self.assertEqual(row['transformations'], [])
            self.assertIs(row['source_sql_executed'], False)
            self.assertIsNone(row['parameter_types'])
            self.assertFalse(row['observed_syntax']['correlated'])

    def test_changed_source_inventory_or_observation_is_not_silently_reselected(self):
        for mutate in (
            lambda m: m['selections'].pop(),
            lambda m: m['selections'][0].update(id='replaced'),
            lambda m: m['selections'][0].update(sql_sha256='0' * 64),
            lambda m: m['selections'][0]['observation'].update(source_free=True),
            lambda m: m['expected_factors']['exists'].update(duckdb=17),
        ):
            changed = deepcopy(self.manifest)
            mutate(changed)
            with self.assertRaisesRegex(ValueError, 'manifest changed'):
                corpus.reproduce(changed)

    def test_declared_catalogs_retain_real_inputs_and_no_execution_claim(self):
        self.assertEqual(len(self.manifest['contexts']), 26)
        self.assertEqual(len(self.manifest['catalogs']), 18)
        for context in self.manifest['contexts']:
            self.assertEqual(corpus.declaration_table(context['sql']), context['table'])
            self.assertIn('not executed', context['claim'])
        for entry in self.manifest['catalogs']:
            catalog = json.loads((corpus.ROOT / entry['local_path']).read_text())
            self.assertIs(catalog['sourceProvenance']['source_sql_executed'], False)
            self.assertEqual(set(entry['context_ids']), set(catalog['sourceProvenance']['context_ids']))

    def test_declaration_metadata_mutations_fail_even_with_new_manifest_digest(self):
        data = {}
        for name, info in self.manifest['sources'].items():
            for file in info['files']:
                data[name, file['path']] = (corpus.ROOT / file['local_path']).read_text()
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

    def test_type_and_nullability_are_not_inferred_from_result_values(self):
        self.assertEqual(corpus.declaration_table('CREATE TABLE t(x INT, y BOOLEAN NOT NULL);'),
                         {'name': 't', 'columns': [{'name': 'x', 'type': 'int', 'nullable': True},
                                                   {'name': 'y', 'type': 'bool', 'nullable': False}]})
        for sql in ('CREATE TABLE t(x DECIMAL)', 'CREATE TABLE t(x INT DEFAULT 1)',
                    'CREATE TABLE t(x INT, x INT)', 'CREATE TABLE t(x INT PRIMARY KEY)',
                    'CREATE TABLE t(x INT); DROP TABLE t;'):
            with self.subTest(sql=sql), self.assertRaises(ValueError):
                corpus.declaration_table(sql)

    def test_closed_registry_is_preregistered_not_all_source_free_queries(self):
        registry = json.loads((corpus.DIRECTORY / 'source_contracts.json').read_text())
        self.assertEqual({f: len(v) for f, v in registry.items()}, {'scalar': 32, 'exists': 22, 'in': 24})
        self.assertEqual({f: sum(len(e['output_columns']) for e in v) for f, v in registry.items()},
                         {'scalar': 37, 'exists': 23, 'in': 24})
        entries = {e['id']: e for rows in registry.values() for e in rows}
        self.assertEqual(len(entries), 78)
        self.assertEqual(sum(e['catalogFile'] is not None for e in entries.values()), 41)
        closed = [r for r in self.rows if r['observed_syntax']['source_free']]
        self.assertEqual(len(closed), 40)
        exclusions = [r['sql'] for r in closed if r['id'] not in entries]
        self.assertEqual(len(exclusions), 3)
        self.assertTrue(all('SELECT NULL' in sql for sql in exclusions))
        for e in entries.values():
            for c in e['output_columns']:
                self.assertIs(type(c['nullable']), bool)
                self.assertIn(c['collation'], (None, 'default'))

    def test_registry_mutants_cannot_change_eligibility_or_output_evidence(self):
        registry = json.loads((corpus.DIRECTORY / 'source_contracts.json').read_text())
        self.assertIs(corpus.validate_registry(self.manifest, registry), registry)
        for mutate in (
            lambda r: r['exists'].pop(),
            lambda r: r['scalar'][0]['output_columns'][0].update(name='renamed'),
            lambda r: r['scalar'][0]['output_columns'][0].update(type='text'),
            lambda r: r['scalar'][0]['output_columns'][0].update(nullable=1),
            lambda r: r['scalar'][0]['output_columns'][0].update(collation='C'),
            lambda r: r['exists'][0].update(id=r['exists'][1]['id']),
            lambda r: r['exists'][1].update(catalogFile=None),
        ):
            changed = deepcopy(registry)
            mutate(changed)
            with self.assertRaisesRegex(ValueError, 'preregistered'):
                corpus.validate_registry(self.manifest, changed)

    def test_observation_rejects_correlated_uncertain_and_false_boolean_metadata(self):
        example = deepcopy(self.rows[0]['observed_syntax'])
        for key, value in [('correlated', [['outer', 'x']]), ('uncertain_scope', [['x']]),
                           ('unresolved_scope', [['missing']]), ('source_free', 0), ('parameters', [True])]:
            changed = deepcopy(example)
            changed[key] = value
            with self.subTest(key=key), self.assertRaises(ValueError):
                corpus.validate_observation(changed, 'exists')


class LiteralReaderTests(unittest.TestCase):
    def test_go_raw_and_plain_query_arguments_preserve_all_sql_bytes(self):
        for needle in ('`\n SELECT EXISTS(SELECT 1)\n`', '"SELECT EXISTS(SELECT 1)"'):
            source = 'package main\nfunc f() { db.QueryRow(' + needle + ', arg).Scan(&ok) }'
            sql, _, evidence = go_query(source, go_selector(source, needle))
            self.assertEqual(sql, needle[1:-1])
            self.assertEqual(evidence['source_expression'], needle)
        needle = '`SELECT EXISTS(SELECT 1)`'
        source = 'db.QueryRowContext(ctx, ' + needle + ', id)'
        self.assertEqual(go_query(source, go_selector(source, needle))[0], needle[1:-1])

    def test_go_rejects_concatenation_other_apis_comments_and_partial_tokens(self):
        needle = '`SELECT EXISTS(SELECT 1)`'
        for source in ('db.QueryRow(' + needle + '+suffix)', 'fmt.Print(' + needle + ')',
                       'x := ' + needle, 'db.QueryRowContext(other, ' + needle + ')'):
            with self.subTest(source=source), self.assertRaises(ValueError):
                go_query(source, go_selector(source, needle))
        source = 'db.QueryRow(' + needle + ')'
        selected = go_selector(source, needle)
        selected['start'] += 1
        with self.assertRaises(ValueError):
            go_query(source, selected)
        with self.assertRaises(StopIteration):
            go_selector('// db.QueryRow(' + needle + ')\n', needle)

    def test_go_escaped_and_malformed_strings_fail(self):
        needle = '"SELECT EXISTS(SELECT 1)\\n"'
        source = 'db.QueryRow(' + needle + ')'
        with self.assertRaises(ValueError):
            go_query(source, go_selector(source, needle))
        needle = '`SELECT EXISTS(SELECT 1)`'
        source = 'db.QueryRow(' + needle + ')\n"unterminated'
        with self.assertRaises(ValueError):
            go_query(source, go_selector(source, needle))
        source = '/* unterminated db.QueryRow(' + needle + ')'
        with self.assertRaises(ValueError):
            go_query(source, go_selector(source, needle))

    def test_view_body_retains_security_wrapper_and_rejects_partial_body(self):
        source = 'CREATE VIEW v WITH (security_barrier = true) AS\n SELECT EXISTS(SELECT 1);'
        start = source.index('SELECT')
        selector = {'kind': 'sql_query_body', 'start': 0, 'end': len(source),
                    'statement_index': 0, 'body_start': start, 'container_kind': 'ViewStmt'}
        sql, _, detail = view_body(source, selector)
        self.assertEqual(sql, 'SELECT EXISTS(SELECT 1);')
        self.assertEqual(detail['container_sql'], source)
        with self.assertRaises(ValueError):
            view_body(source, {**selector, 'body_start': source.index('SELECT 1')})
        with self.assertRaises(ValueError):
            view_body(source.replace('CREATE VIEW', 'ALTER  VIEW'), selector)

    def test_yaml_select_is_exact_whole_statement_and_setup_stays_inert(self):
        source = '- sql: |\n    create table t(x int);\n    select exists(select * from t);\n  expected_outputs:\n  - logical_plan\n'
        block_start = source.index('    create')
        block_end = source.index('  expected')
        a, b = statement_spans(source[block_start:block_end])[1]
        selected = {'kind': 'yaml_sql_statement', 'header_line': 1,
                    'block_start': block_start, 'block_end': block_end,
                    'start': block_start + a, 'end': block_start + b, 'statement_index': 1}
        sql, _, detail = yaml_query(source, selected)
        self.assertEqual(sql, 'select exists(select * from t);')
        self.assertEqual(detail['preceding_inputs'], ['create table t(x int);'])
        self.assertIs(detail['controls_executed'], False)
        for changed in ({**selected, 'start': selected['start'] + 7},
                        {**selected, 'block_end': len(source)}, {**selected, 'statement_index': 0}):
            with self.assertRaises(ValueError):
                yaml_query(source, changed)
        with self.assertRaises(ValueError):
            yaml_query(source.replace('- sql: |', '- sql: >'), selected)

    def test_quidem_whole_input_and_not_with_tail_or_generated_result(self):
        sql = 'select x in (select y from t) from u;'
        source = '# actual input\n' + sql + '\n+----+\n| r |\n+----+\n!ok\n'
        selector = {'kind': 'whole_query_input', 'start': source.index(sql), 'end': source.index(sql) + len(sql)}
        self.assertEqual(quidem_query(source, selector)[0], sql)
        bad = 'with u as (select 1 x)\n' + sql + '\n+----+\n'
        with self.assertRaises(ValueError):
            quidem_query(bad, {'kind': 'whole_query_input', 'start': bad.index(sql), 'end': bad.index(sql) + len(sql)})
        with self.assertRaises(ValueError):
            quidem_query(source, {**selector, 'end': selector['end'] - 1})

    def test_slt_empty_prefix_records_subtests_and_results_stay_separate(self):
        sql = 'SELECT EXISTS(SELECT 1)\n'
        source = 'mode cockroach\n\nquery\nSELECT * FROM zero\n----\n\nsubtest named_case\n\nquery T\n' + sql + '----\nnot a native oracle\n'
        actual, _, metadata = selected_subquery_sqllogic(source, slt_selector(source, sql))
        self.assertEqual(actual, sql)
        self.assertIs(metadata['controls_executed'], False)
        opaque = 'query T\nSELECT 0\n----\nquery T\n' + sql + '----\n1\n'
        with self.assertRaises(ValueError):
            selected_subquery_sqllogic(opaque, slt_selector(opaque, sql))

    def test_slt_unknown_controls_substitutions_and_multiple_queries_fail(self):
        sql = 'SELECT EXISTS(SELECT 1)\n'
        for prefix in ('include file\n', 'loop x 1 9\n', 'mode arbitrary\n'):
            source = prefix + '\nquery T\n' + sql + '----\n1\n'
            with self.assertRaises(ValueError):
                selected_subquery_sqllogic(source, slt_selector(source, sql))
        for sql in ('SELECT EXISTS(SELECT 1); SELECT 2\n', "SELECT '${x}', EXISTS(SELECT 1)\n"):
            source = 'query T\n' + sql + '----\n1\n'
            with self.assertRaises(ValueError):
                selected_subquery_sqllogic(source, slt_selector(source, sql))


class ScopeObservationTests(unittest.TestCase):
    def test_three_sublink_kinds_are_distinguished_from_quantified_comparisons(self):
        for kind, factor in [('EXISTS_SUBLINK', 'exists'), ('EXPR_SUBLINK', 'scalar'), ('ANY_SUBLINK', 'in')]:
            result = observe_tree(query(link(query(literal()), kind)))
            self.assertEqual(result['factors'], {factor: 1})
            self.assertTrue(result['source_free'])
        value = link(query(literal()), 'ANY_SUBLINK', operName=[{'String': {'sval': '='}}])
        result = observe_tree(query(value))
        self.assertEqual(result['factors'], {'other': 1})
        self.assertEqual(result['dependencies'], {'other_sublinks': 1})

    def test_qualified_local_name_shadow_is_not_correlation(self):
        tree = query(link(query(column('a', 'x'), [table('inner', 'a')])), [table('outer', 'a')])
        result = observe_tree(tree)
        self.assertEqual(result['correlated'], [])
        self.assertEqual(result['uncertain_scope'], [])
        self.assertEqual(result['external_relations'], ['inner', 'outer'])

    def test_actual_outer_reference_and_unknown_field_fallback_are_not_accepted(self):
        tree = query(link(query(column('o', 'x'), [table('inner', 'i')])), [table('outer', 'o')])
        self.assertEqual(observe_tree(tree)['correlated'], [['o', 'x']])
        tree = query(link(query(column('x'), [table('inner')])), [table('outer')])
        self.assertEqual(observe_tree(tree)['uncertain_scope'], [['x']])
        fixed = observe_tree(tree, {'inner': ['x'], 'outer': ['x']})
        self.assertFalse(fixed['uncertain_scope'])
        self.assertFalse(fixed['correlated'])

    def test_outer_reference_hidden_in_nonlateral_derived_query_is_retained(self):
        source = {'RangeSubselect': {'subquery': query(column('o', 'x')), 'alias': {'aliasname': 'd'}}}
        tree = query(link(query(column('x'), [source])), [table('outer', 'o')])
        self.assertIn(['o', 'x'], observe_tree(tree)['correlated'])

    def test_unbound_references_and_parameters_do_not_become_closed_cases(self):
        result = observe_tree(query(link(query(column('missing')))))
        self.assertEqual(result['unresolved_scope'], [['missing']])
        value = {'A_Expr': {'lexpr': {'ParamRef': {'number': 2}}, 'rexpr': {'ParamRef': {'number': 2}}}}
        result = observe_tree(query(link(query(value))))
        self.assertFalse(result['source_free'])
        self.assertEqual(result['parameters'], [2])

    def test_sequential_cte_names_are_lexical_and_dependencies_are_explicit(self):
        cte = {'CommonTableExpr': {'ctename': 'c', 'aliascolnames': [{'String': {'sval': 'x'}}],
                                  'ctequery': query(literal())}}
        tree = query(link(query(column('x'), [table('c')])), withClause={'ctes': [cte]})
        result = observe_tree(tree)
        self.assertTrue(result['source_free'])
        self.assertFalse(result['unresolved_scope'])
        tree['SelectStmt']['withClause']['recursive'] = True
        self.assertEqual(observe_tree(tree)['dependencies']['recursive'], 1)
        with self.assertRaises(ValueError):
            observe_tree({'InsertStmt': {}})
        with self.assertRaises(ValueError):
            observe_tree(query(literal()))


if __name__ == '__main__':
    unittest.main()
