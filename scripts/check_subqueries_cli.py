#!/usr/bin/env python3
"""Finite PostgreSQL observations for authored scalar/EXISTS/IN subqueries.

Only the authored synthetic registry executes, in a private cluster or one
rolled-back transaction. Downloaded source statements are inert static/render
inputs. PREPARE, planning and execution boundaries are reported separately;
static typing never claims scalar cardinality or execution success.
"""
import argparse
from collections import Counter
import hashlib
import json
import sqlite3

from check_advanced_cli import literal, question_parameters
from check_assurance_cli import assert_report, invoke
from check_join_contract_cli import bag, sqlite_bindings, validate_native
from check_locking_cli import copy_cell
from check_pagination_cli import ROOT, replay
from check_postgresql_cli import connection, copy_result, marker, parse_results, run, sql_identifier, sql_literal
from check_renderer_corpus import parameters
from generate_subquery_examples import STATES, FACTORS, TABLES, all_cases, population, schema

FIXTURES = ROOT / 'fixtures/subqueries'
NATIVE_COLLATIONS = {None: None, 'default': '"default"', 'C': '"C"', 'POSIX': '"POSIX"'}
RECURSION_BOUNDARIES_SHA256 = '13875ffaff90a25d59f6675a0be74e867d51b7a99e47ead61788037f4379bdc0'
IN_NORMALIZATION_BOUNDARIES_SHA256 = 'f8ac57e859b5c4e9dceb991be39281f589781270df509c10481ef411b812de55'
SOURCE_REGISTRY_SHA256 = '6f7849b733d871fdc74123f2d32a193571b6849a794f9fda7eec5defce51f792'
SOURCE_MANIFEST_SHA256 = '291ffef3a9326a42ce5b75858bd152ec596f797205c9bcc5f90b3e274230702c'
SOURCE_COUNTS = {'scalar': (32, 37, 24), 'exists': (22, 23, 1), 'in': (24, 24, 12)}


def canonical_json(value):
    return json.dumps(value, sort_keys=True, separators=(',', ':'))


def load_cases():
    rows = json.loads((FIXTURES / 'synthetic.json').read_text())
    assert canonical_json(rows) == canonical_json(all_cases()), 'authored fixture/model mismatch'
    assert canonical_json(json.loads((FIXTURES / 'schema.json').read_text())) == canonical_json(schema())
    assert len(rows) == len({r['id'] for r in rows}) == len({r['sql'] for r in rows}) == 150
    assert Counter(r['factor'] for r in rows) == {f: 50 for f in FACTORS}
    for row in rows:
        assert row['source_kind'] == 'synthetic'
        assert row['catalogFile'] == 'fixtures/subqueries/schema.json'
        assert set(row['expected_rows_by_state']) == set(STATES)
        slots = {index for _, index in parameters(row['sql'], 'postgres')}
        assert slots == set(range(1, len(row['parameter_values']) + 1))
        assert len(row['parameter_types'].split(',')) == len(slots) if slots else not row['parameter_types']
        assert row['output_columns']
        assert all(type(c['nullable']) is bool and c['collation'] in NATIVE_COLLATIONS for c in row['output_columns'])
        assert all(len(values) == len(row['output_columns']) for result in row['expected_rows_by_state'].values() for values in result)
    return rows


def validity(row, sql=None, catalog=None):
    args = ['--assurance', 'contract']
    if catalog is not False:
        args += ['--schema', str(catalog or FIXTURES / 'schema.json')]
    if row.get('parameter_types'):
        args += ['--param-types', row['parameter_types']]
    output = tuple((c['name'], c['type'], c['nullable']) for c in row['output_columns'])
    report = assert_report([*args, row['sql'] if sql is None else sql], 'valid', 'contract', output)
    assert report.get('outputCollations') == [c['collation'] for c in row['output_columns']], (row['id'], report)
    return report


def load_sources():
    """Fixed certificate eligibility is independent of the syntax-only flags."""
    registry = json.loads((FIXTURES / 'source_contracts.json').read_text())
    manifest = json.loads((FIXTURES / 'concrete_sources.json').read_text())
    assert hashlib.sha256(canonical_json(registry).encode()).hexdigest() == SOURCE_REGISTRY_SHA256, 'fixed source contracts changed'
    assert hashlib.sha256(canonical_json(manifest).encode()).hexdigest() == SOURCE_MANIFEST_SHA256, 'fixed source provenance changed'
    assert set(registry) == {'scalar', 'exists', 'in'}
    declarations = {entry['local_path']: entry for entry in manifest['catalogs']}
    assert len(declarations) == len(manifest['catalogs']) == 18
    for path, entry in declarations.items():
        assert hashlib.sha256((ROOT / path).read_bytes()).hexdigest() == entry['sha256'], 'conditional catalog changed'
    selections = {entry['id']: entry for entry in manifest['selections']}
    assert len(selections) == len(manifest['selections']) == 150
    result = []
    for group in ('scalar', 'exists', 'in'):
        sources = [json.loads(line) for line in (FIXTURES / f'{group}_concrete.jsonl').read_text().splitlines()]
        assert len(sources) == len({s['id'] for s in sources}) == len({s['sql'] for s in sources}) == 50
        registered = {entry['id']: entry for entry in registry[group]}
        assert len(registered) == len(registry[group]) and set(registered) <= {s['id'] for s in sources}
        assert (len(registered), sum(len(e['output_columns']) for e in registered.values()),
                sum(e['catalogFile'] is None for e in registered.values())) == SOURCE_COUNTS[group]
        for source in sources:
            assert source['factor'] == group and source['source_kind'] != 'synthetic'
            assert source['sql'] == source['raw_sql'] and source['transformations'] == []
            assert hashlib.sha256(source['sql'].encode()).hexdigest() == source['sql_sha256']
            selection = selections[source['id']]
            assert selection['sql_sha256'] == source['sql_sha256'] and selection['factor'] == group
            assert source['source_sql_executed'] is False and source['parameter_types'] is None
            assert type(source['observed_syntax']['source_free']) is bool
            assert canonical_json(source['observed_syntax']) == canonical_json(selection['observation'])
            entry = registered.get(source['id'])
            if entry:
                assert set(entry) == {'id', 'catalogFile', 'output_columns'}
                assert source['observed_parameter_slots'] == []
                assert entry['catalogFile'] in declarations or entry['catalogFile'] is None
                assert source['observed_syntax']['source_free'] is (entry['catalogFile'] is None)
                for column in entry['output_columns']:
                    assert set(column) == {'name', 'type', 'nullable', 'collation'}
                    assert isinstance(column['name'], str) and isinstance(column['type'], str)
                    assert type(column['nullable']) is bool and column['collation'] in NATIVE_COLLATIONS
            result.append((source, entry))
    assert len({source['id'] for source, _ in result}) == 150
    return result


def source_checks():
    """No native SQL builder is called with any source record."""
    count = total = 0
    for source, entry in load_sources():
        catalog = ROOT / entry['catalogFile'] if entry and entry['catalogFile'] else False
        if entry:
            typed = {**source, 'parameter_types': '', 'output_columns': entry['output_columns']}
            validity(typed, catalog=catalog)
            count += 1
        for mode in ('identity', 'postgres'):
            rendered = replay(mode, source['sql'])['sql']
            if entry:
                validity(typed, sql=rendered, catalog=catalog)
        total += 1
    return count, total


def table_statements():
    types = {'int': 'INTEGER', 'text': 'TEXT'}
    return ['CREATE TABLE public.' + sql_identifier(table) + '(' + ','.join(
        sql_identifier(name) + ' ' + types[type_] + ('' if nullable else ' NOT NULL')
        for name, type_, nullable in fields) + ');' for table, fields in TABLES.items()]


def capture(row, sql, metadata=False):
    assert row['source_kind'] == 'synthetic', 'only authored SQL may execute'
    types = row['parameter_types'].replace('?', '')
    declaration = '(' + types + ')' if types else ''
    execute = 'EXECUTE subquery_parameters'
    if row['parameter_values']:
        execute += '(' + ','.join(map(literal, row['parameter_values'])) + ')'
    signature = ','.join(f'c{i} ' + ('TEXT' if metadata else c['postgres_type']) for i, c in enumerate(row['output_columns']))
    return [
        'PREPARE subquery_parameters' + declaration + ' AS ' + question_parameters(sql).strip().removesuffix(';') + ';',
        'CREATE OR REPLACE FUNCTION pg_temp.subquery_rows() RETURNS TABLE(' + signature +
        ') LANGUAGE plpgsql VOLATILE AS ' + sql_literal('BEGIN RETURN QUERY EXECUTE ' + sql_literal(execute) + '; END;') + ';',
        copy_result('SELECT * FROM pg_temp.subquery_rows()'),
    ]


def collation_query(row, sql):
    assert row['source_kind'] == 'synthetic', 'only authored SQL may execute'
    names = ','.join(f'c{i}' for i in range(len(row['output_columns'])))
    # Native pg_type decides whether each actual output type is collatable.
    # pg_collation_for rejects noncollatable types, so guard it using observed
    # catalog metadata rather than the authored expected collation.
    getters = ','.join(f'CASE WHEN EXISTS(SELECT 1 FROM pg_catalog.pg_type t WHERE t.oid=pg_typeof(q.c{i}) AND t.typcollation<>0) THEN pg_collation_for(q.c{i}) ELSE NULL::TEXT END' for i in range(len(row['output_columns'])))
    return 'SELECT ' + getters + ' FROM (VALUES(0)) seed(dummy) LEFT JOIN (' + sql.strip().removesuffix(';') + ') q(' + names + ') ON TRUE LIMIT 1'


def postgres_script(rows, canonical):
    assert len(rows) == len(canonical), 'missing canonical result input'
    assert all(row['source_kind'] == 'synthetic' for row in rows)
    commands = ['\\encoding UTF8', 'BEGIN;', "SET LOCAL statement_timeout='5s';",
                'SET LOCAL standard_conforming_strings=on;', 'SET LOCAL search_path=public,pg_catalog;', *table_statements()]
    expected = {}
    for state in STATES:
        commands.append('TRUNCATE public.items,public.labels;')
        for table, records in population(state).items():
            if records:
                commands.append('INSERT INTO public.' + sql_identifier(table) + ' VALUES ' + ','.join(
                    '(' + ','.join(map(literal, record)) + ')' for record in records) + ';')
        for index, (row, rendered) in enumerate(zip(rows, canonical), 1):
            for form, sql in [('source', row['sql']), ('postgres', rendered)]:
                for kind, query, wanted in [
                    ('rows', sql, row['expected_rows_by_state'][state]),
                    ('collations', collation_query(row, sql), [[NATIVE_COLLATIONS[c['collation']] for c in row['output_columns']]]),
                ]:
                    key = marker('subquery_' + state + '_' + kind, index, state != 'empty', form)
                    parts = capture(row, query, kind == 'collations')
                    commands += ['SAVEPOINT subquery_case;', *parts[:-1], '\\echo ' + key, parts[-1],
                                 'DEALLOCATE subquery_parameters;', 'ROLLBACK TO SAVEPOINT subquery_case;', 'RELEASE SAVEPOINT subquery_case;']
                    expected[key] = (len(row['output_columns']), [[copy_cell(v) for v in values] for values in wanted])
    commands.append('ROLLBACK;')
    return '\n'.join(commands), expected


def describe_script(rows, canonical):
    assert len(rows) == len(canonical), 'missing canonical descriptor input'
    assert all(row['source_kind'] == 'synthetic' for row in rows)
    commands = ['BEGIN;', *table_statements()]
    expected = []
    for row, rendered in zip(rows, canonical):
        types = row['parameter_types'].replace('?', '')
        declaration = '(' + types + ')' if types else ''
        values = '(' + ','.join(map(literal, row['parameter_values'])) + ')' if row['parameter_values'] else ''
        for sql in (row['sql'], rendered):
            commands += ['PREPARE subquery_description' + declaration + ' AS ' + question_parameters(sql).strip().removesuffix(';') + ';',
                         'EXECUTE subquery_description' + values, '\\gdesc', 'DEALLOCATE subquery_description;']
            expected += [c['name'] + '|' + c['postgres_display_type'] for c in row['output_columns']]
    commands.append('ROLLBACK;')
    return '\n'.join(commands), expected



SQLITE_SELECTION = {
    'scalar_subquery': ('integer', 'unknown-null', 'numbered-reordered', 'typed-null', 'zero-row-coalesce', 'table-first'),
    'exists_subquery': ('one', 'empty', 'multiple-projections', 'many-rows', 'discarded-division', 'labels', 'outer-item-rows'),
    'in_subquery': ('match', 'empty', 'null-empty', 'nullable-scores', 'outer-items', 'anonymous-order', 'numbered-reorder'),
}


def sqlite_cases(rows):
    selected = [row for row in rows if row['shape'] in SQLITE_SELECTION[row['factor']]]
    assert len(selected) == 20
    selected = [{**row, 'sqlite_sql': row['sql'].replace('$', '?'),
                 'sqlite_expected_rows_by_state': row['expected_rows_by_state']} for row in selected]
    for index, (body, value) in enumerate([
        ('SELECT 1 UNION ALL SELECT 2', 1),
        ('SELECT 1 UNION ALL SELECT 2 ORDER BY 1 DESC', 2),
    ]):
        selected.append({'id': f'sqlite-scalar-cardinality-{index}', 'source_kind': 'synthetic',
                         'sqlite_sql': f'SELECT ({body}) AS v;', 'parameter_values': [],
                         'output_columns': [{'name': 'v'}], 'postgres_execute': '21000',
                         'sqlite_expected_rows_by_state': {state: [[value]] for state in STATES}})
    return selected


def sqlite_observations(rows, canonical):
    assert len(rows) == len(canonical), 'missing SQLite canonical input'
    assert all(row['source_kind'] == 'synthetic' for row in rows)
    assert sqlite3.sqlite_version_info >= (3, 39, 0)
    count = 0
    with sqlite3.connect(':memory:') as database:
        database.set_progress_handler(lambda: 1, 1_000_000)
        for statement in table_statements():
            database.execute(statement.replace('public.', ''))
        for state in STATES:
            for table, records in population(state).items():
                database.execute('DELETE FROM ' + sql_identifier(table))
                slots = ','.join('?' for _ in TABLES[table])
                database.executemany('INSERT INTO ' + sql_identifier(table) + ' VALUES(' + slots + ')', records)
            for row, rendered in zip(rows, canonical):
                for sql in (row['sqlite_sql'], rendered):
                    cursor = database.execute(sql, sqlite_bindings(sql, row['parameter_values']))
                    assert [c[0] for c in cursor.description] == [c['name'] for c in row['output_columns']], row['id']
                    actual = cursor.fetchall()
                    expected = row['sqlite_expected_rows_by_state'][state]
                    assert bag(actual) == bag(expected), (row['id'], state, sql, actual, expected)
                    count += 1
    return count

def boundary_cases():
    # Expected PostgreSQL SQLSTATE is authored independently of our checker.
    # Static classification is separately registered below, not inferred from
    # PREPARE/planning/execution success.
    values = [
        ('scalar-zero-columns', 'SELECT (SELECT)', '42601', None, None),
        ('scalar-two-columns', 'SELECT (SELECT 1,2)', '42601', None, None),
        ('scalar-many', 'SELECT (SELECT 1 UNION ALL SELECT 2)', '00000', '00000', '21000'),
        ('scalar-many-equal', 'SELECT (SELECT 1 UNION ALL SELECT 1)', '00000', '00000', '21000'),
        ('scalar-unknown-arithmetic', 'SELECT 1+(SELECT NULL)', '42883', None, None),
        ('scalar-unknown-coalesce', 'SELECT COALESCE((SELECT NULL),1)', '42804', None, None),
        ('scalar-unknown-set', "SELECT (SELECT '1') UNION ALL SELECT 1", '42804', None, None),
        ('exists-zero-columns', 'SELECT EXISTS(SELECT)', '00000', '00000', '00000'),
        ('exists-missing-column', 'SELECT EXISTS(SELECT missing)', '42703', None, None),
        ('exists-bad-operator', 'SELECT EXISTS(SELECT TRUE+1)', '42883', None, None),
        ('exists-bad-literal', "SELECT EXISTS(SELECT CAST('bad' AS INTEGER))", '22P02', None, None),
        ('exists-discarded-division', 'SELECT EXISTS(SELECT 1/0)', '00000', '00000', '00000'),
        ('exists-offset-division', 'SELECT EXISTS(SELECT 1/0 OFFSET 0)', '00000', '22012', '22012'),
        ('exists-set-division', 'SELECT EXISTS(SELECT 1/0 UNION ALL SELECT 2)', '00000', '22012', '22012'),
        ('exists-discarded-cardinality', 'SELECT EXISTS(SELECT (SELECT 1 UNION ALL SELECT 2))', '00000', '00000', '00000'),
        ('exists-scalar-arity', 'SELECT EXISTS(SELECT (SELECT 1,2))', '42601', None, None),
        ('exists-json-distinct', "SELECT EXISTS(SELECT DISTINCT '{}'::JSON)", '42883', None, None),
        ('exists-negative-limit', 'SELECT EXISTS(SELECT 1 LIMIT -1)', '00000', '00000', '2201W'),
        ('exists-negative-offset', 'SELECT EXISTS(SELECT 1 OFFSET -1)', '00000', '00000', '2201X'),
        ('exists-nullable-lock', 'SELECT EXISTS(SELECT 1 FROM items i LEFT JOIN labels l ON TRUE FOR UPDATE OF l)', '00000', '0A000', '0A000'),
        ('in-unknown-string-child', "SELECT 1 IN(SELECT '1')", '42883', None, None),
        ('in-unknown-null-child', 'SELECT 1 IN(SELECT NULL)', '42883', None, None),
        ('in-bad-left-literal', "SELECT 'bad' IN(SELECT 1)", '22P02', None, None),
        ('in-zero-columns', 'SELECT 1 IN(SELECT)', '42601', None, None),
        ('in-two-columns', 'SELECT 1 IN(SELECT 1,2)', '42601', None, None),
        ('in-row', 'SELECT ROW(1,2) IN(SELECT 1,2)', '00000', '00000', '00000'),
        ('in-row-zero', 'SELECT ROW() IN(SELECT)', '0A000', None, None),
        ('in-json', "SELECT '{}'::JSON IN(SELECT '{}'::JSON)", '42883', None, None),
        ('in-json-array-runtime', "SELECT ARRAY['{}'::JSON] IN(SELECT ARRAY['{}'::JSON])", '00000', '00000', '42883'),
        ('in-array-mismatch', 'SELECT ARRAY[1::INTEGER] IN(SELECT ARRAY[1::BIGINT])', '42883', None, None),
        ('in-collation-runtime', "SELECT (SELECT 'x' COLLATE \"C\") IN(SELECT 'x' COLLATE \"POSIX\")", '00000', '00000', '42P22'),
        ('scalar-collation-runtime', "SELECT (SELECT 'x' COLLATE \"C\")=(SELECT 'x' COLLATE \"POSIX\")", '00000', '00000', '42P22'),
        ('scalar-indeterminate-collation', 'SELECT (SELECT c||p FROM(SELECT \'x\' COLLATE "C" AS c,\'y\' COLLATE "POSIX" AS p)d)||\'a\'', '00000', '00000', '00000'),
        ('sibling-output-hidden', 'SELECT 1 AS x,(SELECT x)', '42703', None, None),
        ('child-cte-hidden', 'SELECT (WITH c AS(SELECT 3 AS x) SELECT x FROM c),(SELECT x FROM c)', '42P01', None, None),
        ('later-cte-hidden', 'WITH a AS(SELECT (SELECT x FROM b) AS x),b AS(SELECT 3 AS x) SELECT x FROM a', '42P01', None, None),
        ('correlated-qualified', 'SELECT (SELECT i.id) FROM items i', '00000', '00000', '00000'),
        ('correlated-unqualified-fallback', 'SELECT (SELECT id FROM (SELECT 1 AS n) z) FROM items', '00000', '00000', '00000'),
    ]
    return [dict(id=id_, sql=sql, prepare=prepare, plan=plan, execute=execute) for id_, sql, prepare, plan, execute in values]



def boundary_classification(row):
    id_ = row['id']
    parse_gaps = {'scalar-zero-columns', 'exists-zero-columns', 'in-zero-columns', 'in-row-zero'}
    invalid = {
        'scalar-two-columns': 'scalar_subquery_arity',
        'scalar-unknown-arithmetic': 'operator_signature',
        'scalar-unknown-coalesce': 'conditional_signature',
        'scalar-unknown-set': 'set_common_type',
        'exists-bad-operator': 'operator_signature',
        'exists-scalar-arity': 'scalar_subquery_arity',
        'exists-json-distinct': 'distinct_type',
        'in-unknown-string-child': 'in_subquery_signature',
        'in-unknown-null-child': 'in_subquery_signature',
        'in-two-columns': 'in_subquery_arity',
        'in-json': 'in_subquery_signature',
        'in-array-mismatch': 'in_subquery_signature',
        'child-cte-hidden': 'relation_binding', 'later-cte-hidden': 'relation_binding',
    }
    unsupported = {
        'exists-missing-column': 'subquery_correlation',
        'exists-nullable-lock': 'subquery_planning_lock',
        'in-row': 'row_subquery', 'in-json-array-runtime': 'array_element_operator',
        'scalar-indeterminate-collation': 'scalar_subquery_collation',
        'sibling-output-hidden': 'subquery_correlation',
        'correlated-qualified': 'subquery_correlation',
        'correlated-unqualified-fallback': 'subquery_correlation',
    }
    if id_ in parse_gaps:
        return {'status': 'parse-excluded', 'diagnostic': 'input.parse'}
    if id_ in invalid:
        return {'status': 'invalid', 'diagnostic': invalid[id_]}
    if id_ in unsupported:
        return {'status': 'unsupported', 'diagnostic': unsupported[id_]}
    valid = {
        'scalar-many': ('?column?', 'int32', True),
        'scalar-many-equal': ('?column?', 'int32', True),
        'exists-bad-literal': ('exists', 'bool', False),
        'exists-discarded-division': ('exists', 'bool', False),
        'exists-offset-division': ('exists', 'bool', False),
        'exists-set-division': ('exists', 'bool', False),
        'exists-discarded-cardinality': ('exists', 'bool', False),
        'exists-negative-limit': ('exists', 'bool', False),
        'exists-negative-offset': ('exists', 'bool', False),
        'in-bad-left-literal': ('?column?', 'bool', False),
        'in-collation-runtime': ('?column?', 'bool', True),
        'scalar-collation-runtime': ('?column?', 'bool', True),
    }
    name, type_, nullable = valid[id_]
    return {'status': 'valid', 'output_columns': [{'name': name, 'type': type_, 'nullable': nullable, 'collation': None}]}


def boundaries():
    rendered = []
    for row in boundary_cases():
        expected = boundary_classification(row)
        if expected['status'] == 'parse-excluded':
            result = invoke(['--render-assurance', 'identity'], stdin=row['sql'])
            report = json.loads(result.stdout)
            assert (result.returncode, report['status'], report['diagnostic']['code']) == (1, 'invalid', 'input.parse'), (row['id'], report)
            rendered.append(None)
            continue
        canonical = replay('postgres', row['sql'])['sql']
        for sql in (row['sql'], canonical):
            if expected['status'] == 'valid':
                validity({**row, 'parameter_types': '', 'output_columns': expected['output_columns']}, sql=sql)
            else:
                report = assert_report(['--assurance', 'contract', '--schema', str(FIXTURES / 'schema.json'), sql], expected['status'], 'contract')
                assert report['diagnostic']['code'] == expected['diagnostic'], (row['id'], report)
        rendered.append(canonical)
    return rendered

def analysis_script(canonical=None):
    rows = boundary_cases()
    if canonical is not None:
        assert len(canonical) == len(rows), 'missing canonical boundary input'
    commands = ['BEGIN;', "SET LOCAL statement_timeout='5s';", *table_statements(),
        r'''CREATE FUNCTION pg_temp.subquery_stage(q TEXT) RETURNS JSONB LANGUAGE plpgsql AS $$
DECLARE result JSONB:='{}'; state TEXT;
BEGIN
 BEGIN EXECUTE 'PREPARE subquery_probe AS '||q;
 result:=jsonb_build_object('prepare','00000');
 EXCEPTION WHEN OTHERS THEN RETURN jsonb_build_object('prepare',SQLSTATE,'plan',NULL,'execute',NULL); END;
 BEGIN EXECUTE 'EXPLAIN '||q; result:=result||jsonb_build_object('plan','00000');
 EXCEPTION WHEN OTHERS THEN result:=result||jsonb_build_object('plan',SQLSTATE); END;
 BEGIN EXECUTE 'EXECUTE subquery_probe'; result:=result||jsonb_build_object('execute','00000');
 EXCEPTION WHEN OTHERS THEN result:=result||jsonb_build_object('execute',SQLSTATE); END;
 DEALLOCATE subquery_probe;
 RETURN result;
END $$;''']
    expected = []
    for index, row in enumerate(rows):
        for sql in ([row['sql']] if canonical is None or canonical[index] is None else [row['sql'], canonical[index]]):
            commands.append('SELECT pg_temp.subquery_stage(' + sql_literal(sql) + ');')
            expected.append({stage: row[stage] for stage in ('prepare', 'plan', 'execute')})
    commands.append('ROLLBACK;')
    return '\n'.join(commands), expected


def recursion_boundary_cases():
    path = FIXTURES / 'recursion_boundaries.json'
    assert hashlib.sha256(path.read_bytes()).hexdigest() == RECURSION_BOUNDARIES_SHA256, 'recursive SubLink registry changed'
    rows = json.loads(path.read_text())
    assert len(rows) == len({r['id'] for r in rows}) == len({r['sql'] for r in rows}) == 13
    assert all(r['source_kind'] == 'synthetic' for r in rows)
    assert Counter(r['prepare'] for r in rows) == {'42P19': 9, '00000': 3, '0A000': 1}
    return rows


def recursion_boundary_classification(row):
    if row['id'] in {'forward-via-exists', 'mutual-via-exists'}:
        return {'status': 'unsupported', 'diagnostic': 'recursive_dependency'}
    if row['id'] in {'exists-step', 'scalar-step', 'in-step', 'exists-only-reference',
                     'scalar-only-reference', 'join-on-reference', 'order-reference',
                     'anchor-reference', 'unused-cte-reference'}:
        return {'status': 'invalid', 'diagnostic': 'recursive_reference'}
    assert row['id'] in {'inner-shadow-allowed', 'independent-child-allowed'}
    return {'status': 'valid', 'output_columns': [
        {'name': 'n', 'type': 'int32', 'nullable': True, 'collation': None}]}


def recursion_boundaries():
    canonical = []
    for row in recursion_boundary_cases():
        expected = recursion_boundary_classification(row)
        rendered = replay('postgres', row['sql'])['sql']
        for sql in (row['sql'], rendered):
            if expected['status'] == 'valid':
                validity({**row, 'parameter_types': '', 'output_columns': expected['output_columns']}, sql=sql)
            else:
                report = assert_report(['--assurance', 'contract', '--schema', str(FIXTURES / 'schema.json'), sql], expected['status'], 'contract')
                assert report['diagnostic']['code'] == expected['diagnostic'], (row['id'], report)
        canonical.append(rendered)
    return canonical


def recursion_script(canonical=None):
    """Analyze the authored recursion controls; never plan or execute them."""
    return prepare_only_script(recursion_boundary_cases(), canonical)


def prepare_only_script(rows, canonical=None):
    assert all(row['source_kind'] == 'synthetic' for row in rows), 'only authored SQL may be analyzed'
    if canonical is not None:
        assert len(canonical) == len(rows), 'missing canonical SubLink guard input'
    commands = ['BEGIN;', "SET LOCAL statement_timeout='5s';", r'''CREATE FUNCTION pg_temp.subquery_guard_prepare(q TEXT) RETURNS TEXT LANGUAGE plpgsql AS $$
BEGIN
 EXECUTE 'PREPARE subquery_guard AS '||q;
 DEALLOCATE subquery_guard;
 RETURN '00000';
EXCEPTION WHEN OTHERS THEN RETURN SQLSTATE;
END $$;''']
    expected = []
    for index, row in enumerate(rows):
        forms = [('source', row['sql'])]
        if canonical is not None:
            forms.append(('postgres', canonical[index]))
        for form, sql in forms:
            commands.append('SELECT jsonb_build_object(\'id\',' + sql_literal(row['id']) +
                            ',\'form\',' + sql_literal(form) + ',\'prepare\',pg_temp.subquery_guard_prepare(' + sql_literal(sql) + '));')
            expected.append({'id': row['id'], 'form': form, 'prepare': row['prepare']})
    commands.append('ROLLBACK;')
    return '\n'.join(commands), expected


def in_normalization_cases():
    path = FIXTURES / 'in_normalization_boundaries.json'
    assert hashlib.sha256(path.read_bytes()).hexdigest() == IN_NORMALIZATION_BOUNDARIES_SHA256, 'IN SubLink normalization registry changed'
    rows = json.loads(path.read_text())
    assert len(rows) == len({r['id'] for r in rows}) == len({r['sql'] for r in rows}) == 9
    assert all(r['source_kind'] == 'synthetic' for r in rows)
    assert Counter(r['prepare'] for r in rows) == {'42P21': 4, '00000': 5}
    return rows


def in_normalization_classification(row):
    if row['id'] in {'scalar-explicit-conflict', 'scalar-column-child-conflict',
                     'exists-wrapped-conflict', 'inquery-wrapped-conflict'}:
        return {'status': 'invalid', 'diagnostic': 'collation_conflict'}
    assert row['id'] in {'scalar-implicit-conflict', 'scalar-implicit-left-explicit',
                         'scalar-same-explicit', 'scalar-variable-pairwise', 'inquery-variable-pairwise'}
    return {'status': 'valid', 'output_columns': [
        {'name': '?column?', 'type': 'bool', 'nullable': row['id'] != 'inquery-variable-pairwise', 'collation': None}]}


def in_normalization_boundaries():
    canonical = []
    for row in in_normalization_cases():
        expected = in_normalization_classification(row)
        rendered = replay('postgres', row['sql'])['sql']
        for sql in (row['sql'], rendered):
            if expected['status'] == 'valid':
                validity({**row, 'parameter_types': '', 'output_columns': expected['output_columns']}, sql=sql)
            else:
                report = assert_report(['--assurance', 'contract', '--schema', str(FIXTURES / 'schema.json'), sql], 'invalid', 'contract')
                assert report['diagnostic']['code'] == 'collation_conflict', (row['id'], report)
        canonical.append(rendered)
    return canonical



def operator_collation_cases():
    child = "SELECT c||p FROM(SELECT 'x' COLLATE \"C\" AS c,'y' COLLATE \"POSIX\" AS p)d"
    rows = []
    for name, left, identity in [
        ('unknown-default', "'xy'", 'default'),
        ('known-default', "CAST('xy' AS TEXT)", 'default'),
        ('explicit-c', "'xy' COLLATE \"C\"", 'C'),
        ('explicit-posix', "'xy' COLLATE \"POSIX\"", 'POSIX'),
        ('implicit-c', "(SELECT 'xy' COLLATE \"C\")", 'C'),
        ('implicit-posix', "(SELECT 'xy' COLLATE \"POSIX\")", 'POSIX'),
    ]:
        rows.append({'id': name, 'sql': f'SELECT {left} IN({child}) AS v', 'input_collation': identity})
    rows.append({'id': 'both-none', 'sql': f'SELECT q.v IN({child}) AS v FROM({child})q(v)', 'input_collation': None})
    rows.append({'id': 'rhs-explicit-becomes-implicit',
                 'sql': "SELECT 'xy' COLLATE \"POSIX\" IN(SELECT 'xy' COLLATE \"C\") AS v",
                 'input_collation': 'POSIX'})
    return rows


def operator_collation_script():
    commands = ['BEGIN;', "SET LOCAL statement_timeout='5s';"]
    expected = []
    for row in operator_collation_cases():
        commands.append('CREATE TEMP VIEW subquery_operator_view AS ' + row['sql'] + ';')
        commands.append(r"""SELECT jsonb_build_object('operator',o.oprname,'left',o.oprleft::regtype::text,
'right',o.oprright::regtype::text,'result',o.oprresult::regtype::text,
'input_collation',CASE WHEN m.parts[2]::oid=0 THEN NULL ELSE c.collname END)
FROM pg_rewrite r CROSS JOIN LATERAL regexp_matches(r.ev_action::text,
':opno ([0-9]+) :opfuncid [0-9]+ :opresulttype [0-9]+ :opretset [^ ]+ :opcollid [0-9]+ :inputcollid ([0-9]+)','g') m(parts)
JOIN pg_operator o ON o.oid=m.parts[1]::oid LEFT JOIN pg_collation c ON c.oid=m.parts[2]::oid
WHERE r.ev_class='pg_temp.subquery_operator_view'::regclass AND o.oprname='=';""")
        expected.append({'operator': '=', 'left': 'text', 'right': 'text', 'result': 'boolean',
                         'input_collation': row['input_collation']})
        commands.append('DROP VIEW pg_temp.subquery_operator_view;')
    commands.append('ROLLBACK;')
    return '\n'.join(commands), expected

def validate_stages(output, expected):
    observed = [json.loads(line) for line in output.splitlines()]
    assert observed == expected, (observed, expected)


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    target = parser.add_mutually_exclusive_group(required=True)
    target.add_argument('--local-bin')
    target.add_argument('--dsn')
    parser.add_argument('--psql')
    parser.add_argument('--source-only', action='store_true', help='authored native preflight only; use original SQL in both form slots')
    parser.add_argument('--source-registry', action='store_true', help='also check all150 unchanged sources and the fixed eligible registry; never execute them')
    args = parser.parse_args()
    assert not (args.source_only and args.source_registry)
    rows = load_cases()
    canonical = []
    for row in rows:
        if args.source_only:
            canonical.append(row['sql'])
        else:
            validity(row)
            replay('identity', row['sql'])
            rendered = replay('postgres', row['sql'])['sql']
            validity(row, sql=rendered)
            canonical.append(rendered)
    source_count = source_checks() if args.source_registry else None
    sqlite_rows = sqlite_cases(rows)
    sqlite_canonical = [row['sqlite_sql'] if args.source_only else replay('sqlite', row['sqlite_sql'])['sql'] for row in sqlite_rows]
    sqlite_count = sqlite_observations(sqlite_rows, sqlite_canonical)
    values_sql, values = postgres_script(rows, canonical)
    descriptions_sql, descriptions = describe_script(rows, canonical)
    boundary_canonical = None if args.source_only else boundaries()
    stages_sql, stages = analysis_script(boundary_canonical)
    operators_sql, operators = operator_collation_script()
    recursion_sql, recursion = recursion_script(None if args.source_only else recursion_boundaries())
    normalization_sql, normalization = prepare_only_script(in_normalization_cases(), None if args.source_only else in_normalization_boundaries())
    with connection(args) as psql:
        result = run([*psql, '-X', '-q', '-v', 'ON_ERROR_STOP=1'], input=values_sql, timeout=180)
        validate_native(parse_results(result.stdout), values)
        result = run([*psql, '-X', '-qAt', '-v', 'ON_ERROR_STOP=1'], input=descriptions_sql, timeout=120)
        assert result.stdout.splitlines() == descriptions, (result.stdout.splitlines(), descriptions)
        result = run([*psql, '-X', '-qAt', '-v', 'ON_ERROR_STOP=1'], input=stages_sql, timeout=120)
        validate_stages(result.stdout, stages)
        result = run([*psql, '-X', '-qAt', '-v', 'ON_ERROR_STOP=1'], input=operators_sql, timeout=120)
        validate_stages(result.stdout, operators)
        result = run([*psql, '-X', '-qAt', '-v', 'ON_ERROR_STOP=1'], input=recursion_sql, timeout=120)
        validate_stages(result.stdout, recursion)
        result = run([*psql, '-X', '-qAt', '-v', 'ON_ERROR_STOP=1'], input=normalization_sql, timeout=120)
        validate_stages(result.stdout, normalization)
        version = run([*psql, '-X', '-At', '-c', 'SHOW server_version']).stdout.strip()
        assert version.startswith('16.'), version
    print(f'PASS: 150 authored subqueries; PostgreSQL {version}: {len(values)//2} typed row captures, '
          f'{len(values)//2} collation captures, {len(descriptions)} descriptor positions, {len(stages)} three-stage boundaries, {len(operators)} operator input-collation checks, {len(recursion)} recursive SubLink and {len(normalization)} IN-normalization PREPARE checks')
    if source_count:
        print(f'PASS: {source_count[0]} fixed authentic certificates; {source_count[1]} unchanged sources rendered, none executed')
    print(f'PASS: SQLite {sqlite3.sqlite_version}: {sqlite_count} authored row/label observations; 20 portable cases plus two registered scalar-cardinality differences')
    print('Scope: finite authored observations; no general cross-dialect semantics claim. Static typing does not prove cardinality or execution success.')


if __name__ == '__main__':
    main()
