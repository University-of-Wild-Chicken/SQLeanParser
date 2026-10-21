#!/usr/bin/env python3
"""Author 50 scalar, 50 EXISTS and 50 scalar-IN subqueries with finite row models."""
import argparse
import json
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
FIXTURES = ROOT / 'fixtures/subqueries'
STATES = ('empty', 'items_only', 'labels_only', 'both')
FACTORS = ('scalar_subquery', 'exists_subquery', 'in_subquery')
TABLES = {
    'items': [('id', 'int', False), ('score', 'int', True), ('name', 'text', False)],
    'labels': [('id', 'int', False), ('category', 'text', False)],
}
DATA = {'items': [[1, 10, 'Ada'], [2, None, 'Bea'], [3, 10, 'Cy'], [4, 40, 'Di']],
        'labels': [[1, 'A'], [1, 'B'], [3, 'C'], [5, 'E']]}
NATIVE = {
    'int32': ('INTEGER', 'integer'), 'bool': ('BOOLEAN', 'boolean'), 'text': ('TEXT', 'text'),
    'name': ('NAME', 'name'), 'varchar(7)': ('VARCHAR(7)', 'character varying(7)'),
    'char(4)': ('CHAR(4)', 'character(4)'), 'numeric(8,3)': ('NUMERIC(8,3)', 'numeric(8,3)'),
    'integer[]': ('INTEGER[]', 'integer[]'), 'numeric(8,3)[]': ('NUMERIC(8,3)[]', 'numeric(8,3)[]'),
    'boolean[]': ('BOOLEAN[]', 'boolean[]'), 'interval second(3)': ('INTERVAL SECOND(3)', 'interval second(3)'),
    'date': ('DATE', 'date'), 'time(2)': ('TIME(2)', 'time(2) without time zone'),
    'timestamp(3)': ('TIMESTAMP(3)', 'timestamp(3) without time zone'),
    'jsonb': ('JSONB', 'jsonb'), 'bytea': ('BYTEA', 'bytea'),
}


def population(state):
    assert state in STATES
    return {table: rows if state in ('both', table + '_only') else [] for table, rows in DATA.items()}


def schema():
    return {'tables': [
        {'name': table, 'schema': 'public', 'exposeUnqualified': True,
         'columns': [{'name': name, 'type': type_, 'nullable': nullable} for name, type_, nullable in fields]}
        for table, fields in TABLES.items()],
        'collations': {'encoding': 'UTF8', 'entries': [
            {'id': name, 'schema': 'pg_catalog', 'name': name, 'encoding': None,
             'deterministic': True, 'exposeUnqualified': True} for name in ('default', 'C', 'POSIX')]}}


def col(type_='int32', nullable=False, name='v', collation=None):
    if collation is None and type_ in ('text', 'varchar(7)', 'char(4)'):
        collation = 'default'
    if collation is None and type_ == 'name':
        collation = 'C'
    native, display = NATIVE[type_]
    return {'name': name, 'type': type_, 'nullable': nullable, 'collation': collation,
            'postgres_type': native, 'postgres_display_type': display}


def sql_in(left, values):
    """SQL scalar equality membership for this authored int/text/bool model."""
    if not values:
        return False
    if left is None:
        return None
    if any(value is not None and value == left for value in values):
        return True
    return None if None in values else False


def sql_not(value):
    return None if value is None else not value


def cases(data=DATA):
    rows = []
    counts = {factor: 0 for factor in FACTORS}

    def add(factor, shape, sql, output, expected, *, types='', values=None):
        counts[factor] += 1
        rows.append({'id': f'{factor}-{counts[factor]:02d}-{shape}', 'factor': factor,
                     'shape': shape, 'source_kind': 'synthetic', 'sql': sql + ';',
                     'catalogFile': 'fixtures/subqueries/schema.json', 'parameter_types': types,
                     'parameter_values': [] if values is None else values,
                     'output_columns': output, 'expected_rows': expected})

    def scalar(shape, expr, value, type_='int32', *, name='v', collation=None, types='', values=None):
        add(FACTORS[0], shape, f'SELECT {expr} AS {name}', [col(type_, True, name, collation)],
            [[value]], types=types, values=values)

    scalar('integer', '(SELECT 1)', 1)
    scalar('unknown-null', '(SELECT NULL)', None, 'text')
    scalar('unknown-string', "(SELECT 'abc')", 'abc', 'text')
    scalar('typed-null', '(SELECT CAST(NULL AS INTEGER))', None)
    scalar('numeric-modifier', '(SELECT CAST(1.2345 AS NUMERIC(8,3)))', '1.235', 'numeric(8,3)')
    scalar('varchar-modifier', "(SELECT CAST('abcdefgh' AS VARCHAR(7)))", 'abcdefg', 'varchar(7)')
    scalar('char-padding', "(SELECT CAST('a' AS CHAR(4)))", 'a   ', 'char(4)')
    scalar('name-collation', "(SELECT CAST('Ada' AS NAME))", 'Ada', 'name')
    scalar('array-null-element', '(SELECT ARRAY[1,NULL])', '{1,NULL}', 'integer[]')
    scalar('array-modifier', '(SELECT ARRAY[CAST(1.2345 AS NUMERIC(8,3))])', '{1.235}', 'numeric(8,3)[]')
    scalar('interval-modifier', "(SELECT INTERVAL '2.1234' SECOND(3))", '00:00:02.123', 'interval second(3)')
    scalar('date', "(SELECT DATE '2024-01-02')", '2024-01-02', 'date')
    scalar('time-modifier', "(SELECT TIME(2) '12:34:56.1234')", '12:34:56.12', 'time(2)')
    scalar('timestamp-modifier', "(SELECT TIMESTAMP(3) '2024-01-02 12:34:56.1234')",
           '2024-01-02 12:34:56.123', 'timestamp(3)')
    scalar('jsonb', "(SELECT '{\"x\":1}'::JSONB)", '{"x": 1}', 'jsonb')
    scalar('bytea', "(SELECT '\\x4142'::BYTEA)", '\\x4142', 'bytea')
    scalar('stored-collation', "(SELECT 'x' COLLATE \"C\")", 'x', 'text', collation='C')
    add(FACTORS[0], 'inherited-label', 'SELECT (SELECT 7 AS inner_value)',
        [col(nullable=True, name='inner_value')], [[7]])
    add(FACTORS[0], 'nested-label', 'SELECT (SELECT (SELECT 8 AS deep_name))',
        [col(nullable=True, name='deep_name')], [[8]])
    add(FACTORS[0], 'cast-inherited-label', 'SELECT CAST((SELECT 7 AS inner_value) AS TEXT)',
        [col('text', True, 'inner_value')], [['7']])
    add(FACTORS[0], 'zero-row-coalesce', 'SELECT COALESCE((SELECT 7 WHERE FALSE),77) AS v', [col()], [[77]])
    add(FACTORS[0], 'zero-row-null-test', 'SELECT (SELECT 7 WHERE FALSE) IS NULL AS v', [col('bool')], [[True]])
    add(FACTORS[0], 'array-member', 'SELECT ARRAY[(SELECT 7 WHERE FALSE)] AS v', [col('integer[]')], [['{NULL}']])
    scalar('case-member', 'CASE WHEN TRUE THEN (SELECT 7) ELSE 8 END', 7)
    scalar('arithmetic-member', '(SELECT 2)+3', 5)
    scalar('boolean', '(SELECT TRUE)', True, 'bool')
    scalar('derived-child', '(SELECT x FROM (SELECT 3 AS x) d)', 3)
    add(FACTORS[0], 'outer-cte', 'WITH c AS(SELECT 3 AS x) SELECT (SELECT x FROM c) AS v', [col(nullable=True)], [[3]])
    add(FACTORS[0], 'cte-shadow', 'WITH c AS(SELECT 3 AS x) SELECT (WITH c AS(SELECT 4 AS x) SELECT x FROM c) AS v',
        [col(nullable=True)], [[4]])
    add(FACTORS[0], 'cte-own-body-outer', 'WITH c AS(SELECT 3 AS x) SELECT (WITH c AS(SELECT x+1 AS x FROM c) SELECT x FROM c) AS v',
        [col(nullable=True)], [[4]])
    scalar('set-limit', '(SELECT 1 UNION ALL SELECT 2 ORDER BY 1 LIMIT 1)', 1)
    scalar('empty-intersect', '(SELECT 1 INTERSECT SELECT 2)', None)
    scalar('anonymous', '(SELECT ?)', 7, types='int', values=[7])
    scalar('numbered-reordered', '(SELECT $2-$1)', 5, types='int,int', values=[2, 7])
    add(FACTORS[0], 'lexical-outer-child', 'SELECT ? AS marker,(SELECT ?) AS v',
        [col(name='marker'), col(nullable=True)], [[9, 7]], types='int,int', values=[9, 7])
    add(FACTORS[0], 'unused-cte-parameters', 'WITH unused AS(SELECT ? AS x) SELECT (SELECT ?) AS v',
        [col(nullable=True)], [[7]], types='int,int', values=[100, 7])
    scalar('numbered-reuse', '$1+(SELECT $1)', 14, types='int', values=[7])
    scalar('nullable-parameter', '(SELECT $1)', None, types='int?', values=[None])
    scalar('parameter-explicit-modifier', '(SELECT CAST($1 AS NUMERIC(8,3)))', '1.235', 'numeric(8,3)',
           types='numeric', values=['1.2345'])
    scalar('parameter-child-filter', '(SELECT ? WHERE ?)', None, types='int,bool', values=[7, False])
    items, labels = data['items'], data['labels']
    first = items[0] if items else [None, None, None]
    last = items[-1] if items else [None, None, None]
    scalar('table-first', '(SELECT id FROM items ORDER BY id LIMIT 1)', first[0])
    scalar('table-last', '(SELECT id FROM items ORDER BY id DESC LIMIT 1)', last[0])
    scalar('nullable-table', '(SELECT score FROM items WHERE id=2)', None)
    scalar('table-name', '(SELECT name FROM items WHERE id=1)', first[2], 'text')
    scalar('empty-table-filter', '(SELECT id FROM items WHERE id=99)', None)
    scalar('duplicate-source-limit', '(SELECT id FROM labels ORDER BY id LIMIT 1)', 1 if labels else None)
    scalar('duplicate-source-offset', '(SELECT category FROM labels ORDER BY category OFFSET 1 LIMIT 1)',
           'B' if labels else None, 'text')
    add(FACTORS[0], 'outer-rows', 'SELECT id,(SELECT id FROM labels ORDER BY id LIMIT 1) AS v FROM items',
        [col(name='id'), col(nullable=True)], [[i, 1 if labels else None] for i, _, _ in items])
    scalar('cte-table-child', '(WITH c AS(SELECT id FROM items) SELECT id FROM c ORDER BY id LIMIT 1)', first[0])
    scalar('empty-by-offset', '(SELECT id FROM items ORDER BY id OFFSET 10 LIMIT 1)', None)
    assert counts[FACTORS[0]] == 50

    def exists(shape, body, value=True, *, negated=False, types='', values=None):
        expr = ('NOT ' if negated else '') + 'EXISTS(' + body + ')'
        add(FACTORS[1], shape, 'SELECT ' + expr + ' AS v', [col('bool')], [[value]], types=types, values=values)

    exists('one', 'SELECT 1')
    exists('empty', 'SELECT 1 WHERE FALSE', False)
    exists('null-projection', 'SELECT NULL')
    exists('multiple-projections', 'SELECT 1,2')
    exists('many-rows', 'SELECT 1 UNION ALL SELECT 2')
    exists('empty-set', 'SELECT 1 INTERSECT SELECT 2', False)
    exists('limit-zero', 'SELECT 1 LIMIT 0', False)
    exists('offset-one', 'SELECT 1 OFFSET 1', False)
    exists('limit-null', 'SELECT 1 LIMIT NULL')
    exists('array-projection', 'SELECT ARRAY[1,NULL]')
    exists('numeric-projection', 'SELECT CAST(1.2345 AS NUMERIC(8,3))')
    exists('discarded-cardinality', 'SELECT (SELECT 1 UNION ALL SELECT 2)')
    exists('discarded-division', 'SELECT 1/0')
    exists('discarded-distinct-division', 'SELECT DISTINCT 1/0')
    exists('discarded-sort-division', 'SELECT 1/0 ORDER BY 1')
    add(FACTORS[1], 'outer-cte', 'WITH c AS(SELECT 3 AS x) SELECT EXISTS(SELECT x FROM c) AS v', [col('bool')], [[True]])
    add(FACTORS[1], 'inner-cte-shadow', 'WITH c AS(SELECT 3 AS x) SELECT EXISTS(WITH c AS(SELECT 4 AS x) SELECT x FROM c WHERE x=3) AS v',
        [col('bool')], [[False]])
    exists('nested-exists', 'SELECT EXISTS(SELECT 1 WHERE FALSE)')
    exists('not-empty', 'SELECT 1 WHERE FALSE', True, negated=True)
    add(FACTORS[1], 'cast', 'SELECT CAST(EXISTS(SELECT 1) AS TEXT) AS v', [col('text')], [['true']])
    add(FACTORS[1], 'array', 'SELECT ARRAY[EXISTS(SELECT 1)] AS v', [col('boolean[]')], [['{t}']])
    add(FACTORS[1], 'where', 'SELECT 1 AS v WHERE EXISTS(SELECT 1)', [col()], [[1]])
    add(FACTORS[1], 'case', 'SELECT CASE WHEN EXISTS(SELECT 1) THEN 7 ELSE 8 END AS v', [col()], [[7]])
    exists('scalar-child', 'SELECT (SELECT 7)')
    exists('distinct', 'SELECT DISTINCT 1')
    exists('intersect', 'SELECT 1 INTERSECT SELECT 1')
    exists('except', 'SELECT 1 EXCEPT SELECT 1', False)
    exists('unknown-set', 'SELECT NULL UNION ALL SELECT NULL')
    exists('empty-ordered', 'SELECT 1 WHERE FALSE ORDER BY 1', False)
    exists('subquery-limit', 'SELECT 1 LIMIT (SELECT 1)')
    exists('anonymous-target', 'SELECT ?', types='int', values=[7])
    exists('nullable-target', 'SELECT $1', types='int?', values=[None])
    exists('anonymous-condition', 'SELECT ? WHERE ?', False, types='int,bool', values=[7, False])
    exists('numbered-reordered', 'SELECT $2 WHERE $1', types='bool,int', values=[True, 7])
    add(FACTORS[1], 'lexical-outer-child', 'SELECT ? AS marker,EXISTS(SELECT ?) AS v',
        [col(name='marker'), col('bool')], [[9, True]], types='int,int', values=[9, 7])
    add(FACTORS[1], 'unused-cte-parameters', 'WITH unused AS(SELECT ? AS x) SELECT EXISTS(SELECT ?) AS v',
        [col('bool')], [[True]], types='int,int', values=[100, 7])
    exists('items', 'SELECT id FROM items', bool(items))
    exists('items-missing', 'SELECT id FROM items WHERE id=99', False)
    exists('null-score', 'SELECT id FROM items WHERE score IS NULL', bool(items))
    exists('score-ten', 'SELECT id FROM items WHERE score=10', bool(items))
    exists('labels', 'SELECT id FROM labels', bool(labels))
    exists('duplicate-labels', 'SELECT id FROM labels WHERE id=1', bool(labels))
    exists('labels-missing', 'SELECT id FROM labels WHERE id=99', False)
    exists('join', 'SELECT i.id FROM items i JOIN labels l ON i.id=l.id', bool(items and labels))
    exists('left-join', 'SELECT i.id FROM items i LEFT JOIN labels l ON FALSE', bool(items))
    exists('table-page', 'SELECT id FROM labels ORDER BY id OFFSET 3 LIMIT 1', bool(labels))
    exists('table-empty-page', 'SELECT id FROM labels ORDER BY id OFFSET 4 LIMIT 1', False)
    add(FACTORS[1], 'outer-item-rows', 'SELECT id,EXISTS(SELECT id FROM labels) AS v FROM items',
        [col(name='id'), col('bool')], [[i, bool(labels)] for i, _, _ in items])
    add(FACTORS[1], 'outer-label-rows', 'SELECT id,EXISTS(SELECT score FROM items WHERE score IS NULL) AS v FROM labels',
        [col(name='id'), col('bool')], [[i, bool(items)] for i, _ in labels])
    add(FACTORS[1], 'table-filter', 'SELECT id AS v FROM items WHERE EXISTS(SELECT id FROM labels)',
        [col()], [[i] for i, _, _ in items] if labels else [])
    assert counts[FACTORS[1]] == 50

    def member(shape, left, child, value, *, nullable=False, negated=False, types='', values=None):
        add(FACTORS[2], shape, f'SELECT {left} ' + ('NOT ' if negated else '') + f'IN({child}) AS v',
            [col('bool', nullable)], [[value]], types=types, values=values)

    member('match', '1', 'SELECT 1', True)
    member('nonmatch', '1', 'SELECT 2', False)
    member('empty', '1', 'SELECT 1 WHERE FALSE', False)
    member('null-empty', 'NULL', 'SELECT 1 WHERE FALSE', False, nullable=True)
    member('null-left', 'NULL', 'SELECT 1', None, nullable=True)
    member('null-right', '1', 'SELECT CAST(NULL AS INTEGER)', None, nullable=True)
    member('both-null', 'NULL', 'SELECT NULL', None, nullable=True)
    member('unknown-left', "'1'", 'SELECT 1', True)
    member('cross-numeric', 'CAST(1 AS SMALLINT)', 'SELECT CAST(1 AS BIGINT)', True)
    member('char-padding', "'x  '", "SELECT CAST('x' AS CHAR(4))", True)
    member('jsonb', "'{}'::JSONB", "SELECT '{}'::JSONB", True)
    member('array', 'ARRAY[1]', 'SELECT ARRAY[1]', True)
    member('array-null-element', 'ARRAY[NULL::INTEGER]', 'SELECT ARRAY[NULL::INTEGER]', True)
    member('cross-temporal', "DATE '2024-01-02'", "SELECT TIMESTAMP '2024-01-02'", True)
    member('varchar-text', "CAST('x' AS VARCHAR(7))", "SELECT 'x'", True)
    member('explicit-over-stored-collation', "'x' COLLATE \"C\"", "SELECT 'x' COLLATE \"POSIX\"", True)
    member('not-empty', '1', 'SELECT 1 WHERE FALSE', True, negated=True)
    member('not-null', '1', 'SELECT CAST(NULL AS INTEGER)', None, nullable=True, negated=True)
    member('match-before-null', '1', 'SELECT 1 UNION ALL SELECT NULL::INTEGER', True, nullable=True)
    member('nonmatch-with-null', '2', 'SELECT 1 UNION ALL SELECT NULL::INTEGER', None, nullable=True)
    member('duplicate-match', '1', 'SELECT 1 UNION ALL SELECT 1', True)
    member('scalar-left', '(SELECT 1)', 'SELECT 1', True, nullable=True)
    member('nested-in', 'TRUE', 'SELECT 1 IN(SELECT 1)', True)
    member('unknown-date', "'2024-01-02'", "SELECT DATE '2024-01-02'", True)
    member('negative', '-1', 'SELECT -1', True)
    member('numeric-modifier', 'CAST(1.234 AS NUMERIC(8,3))', 'SELECT CAST(1.234 AS NUMERIC(8,3))', True)
    add(FACTORS[2], 'cast', 'SELECT CAST(1 IN(SELECT 1) AS TEXT) AS v', [col('text')], [['true']])
    add(FACTORS[2], 'case', 'SELECT CASE WHEN 1 IN(SELECT 1) THEN 7 ELSE 8 END AS v', [col()], [[7]])
    add(FACTORS[2], 'array-member', 'SELECT ARRAY[1 IN(SELECT 1)] AS v', [col('boolean[]')], [['{t}']])
    add(FACTORS[2], 'null-test', 'SELECT (1 IN(SELECT NULL::INTEGER)) IS NULL AS v', [col('bool')], [[True]])
    member('anonymous-order', '?', 'SELECT ?', True, types='int,int', values=[7, 7])
    member('numbered-reorder', '$2', 'SELECT $1', False, types='int,int', values=[2, 7])
    member('numbered-reuse', '$1', 'SELECT $1', True, types='int', values=[7])
    member('nullable-left-parameter', '$1', 'SELECT $2', None, nullable=True, types='int?,int', values=[None, 7])
    member('nullable-right-parameter', 'CAST($1 AS INTEGER)', 'SELECT $2', None, nullable=True, types='int,int?', values=[7, None])
    member('child-where-parameter', '?', 'SELECT ? WHERE ?', False, types='int,int,bool', values=[7, 7, False])
    add(FACTORS[2], 'unused-cte-parameters', 'WITH unused AS(SELECT ? AS x) SELECT ? IN(SELECT ?) AS v',
        [col('bool')], [[True]], types='int,int,int', values=[100, 7, 7])
    add(FACTORS[2], 'lexical-outer-child', 'SELECT ? AS marker,? IN(SELECT ?) AS v',
        [col(name='marker'), col('bool')], [[9, True]], types='int,int,int', values=[9, 7, 7])
    ids = [i for i, _, _ in items]
    labelids = [i for i, _ in labels]
    scores = [score for _, score, _ in items]
    member('item-membership', '1', 'SELECT id FROM items', sql_in(1, ids))
    member('missing-item', '99', 'SELECT id FROM items', False)
    member('duplicate-membership', '1', 'SELECT id FROM labels', sql_in(1, labelids))
    member('nullable-scores', '20', 'SELECT score FROM items', sql_in(20, scores), nullable=True)
    member('score-match', '10', 'SELECT score FROM items', sql_in(10, scores), nullable=True)
    member('not-nullable-scores', '20', 'SELECT score FROM items', sql_not(sql_in(20, scores)), nullable=True, negated=True)
    member('text-membership', "'Ada'", 'SELECT name FROM items', sql_in('Ada', [name for _, _, name in items]))
    member('category-membership', "'B'", 'SELECT category FROM labels', sql_in('B', [category for _, category in labels]))
    add(FACTORS[2], 'outer-items', 'SELECT id,id IN(SELECT id FROM labels) AS v FROM items',
        [col(name='id'), col('bool')], [[i, sql_in(i, labelids)] for i, _, _ in items])
    add(FACTORS[2], 'outer-nullable', 'SELECT id,score IN(SELECT id FROM labels) AS v FROM items',
        [col(name='id'), col('bool', True)], [[i, sql_in(score, labelids)] for i, score, _ in items])
    add(FACTORS[2], 'outer-labels', 'SELECT id,id IN(SELECT score FROM items) AS v FROM labels',
        [col(name='id'), col('bool', True)], [[i, sql_in(i, scores)] for i, _ in labels])
    add(FACTORS[2], 'where-membership', 'SELECT id AS v FROM items WHERE id IN(SELECT id FROM labels)',
        [col()], [[i] for i, _, _ in items if sql_in(i, labelids) is True])
    assert counts[FACTORS[2]] == 50
    assert len(rows) == len({r['id'] for r in rows}) == len({r['sql'] for r in rows}) == 150
    return rows


def all_cases():
    result = cases()
    for row in result:
        row['expected_rows_by_state'] = {}
    for state in STATES:
        for row, modeled in zip(result, cases(population(state))):
            assert row['id'] == modeled['id'] and row['output_columns'] == modeled['output_columns']
            row['expected_rows_by_state'][state] = modeled['expected_rows']
    return result


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--check', action='store_true')
    args = parser.parse_args()
    for name, value in [('synthetic.json', all_cases()), ('schema.json', schema())]:
        text = json.dumps(value, indent=2) + '\n'
        path = FIXTURES / name
        if args.check:
            assert path.read_text() == text, f'stale {path}'
        else:
            FIXTURES.mkdir(parents=True, exist_ok=True)
            path.write_text(text)
    print('PASS: 150 authored scalar/EXISTS/scalar-IN subqueries; four independent table populations')


if __name__ == '__main__':
    main()
