#!/usr/bin/env python3
"""Fifty authored row-IN queries with independent three-valued membership models."""
import argparse
import json
from pathlib import Path

from generate_subquery_examples import STATES, DATA, population, schema, col, sql_not

ROOT = Path(__file__).resolve().parents[1]
FIXTURES = ROOT / 'fixtures/row_in_subqueries'


def row_equal(left, right):
    assert len(left) == len(right) and left
    if any(a is not None and b is not None and a != b for a, b in zip(left, right)):
        return False
    return None if any(a is None or b is None for a, b in zip(left, right)) else True


def row_in(left, rows):
    comparisons = [row_equal(left, row) for row in rows]
    return True if True in comparisons else None if None in comparisons else False


def cases(data=DATA):
    result = []

    def add(shape, sql, value, *, types='', values=None, output=None, sqlite=False):
        result.append({'id': f'row-in-{len(result)+1:02d}-{shape}',
            'factor': 'row_in_subquery', 'shape': shape, 'source_kind': 'synthetic',
            'sql': sql + ';', 'catalogFile': 'fixtures/row_in_subqueries/schema.json',
            'parameter_types': types, 'parameter_values': values or [],
            'output_columns': output or [col('bool', True)], 'expected_rows': value,
            'sqlite_supported': sqlite})

    def member(shape, left_sql, child_sql, left, right, *, negated=False, **options):
        value = row_in(left, right)
        if negated:
            value = sql_not(value)
        add(shape, f'SELECT {left_sql} {"NOT IN" if negated else "IN"} ({child_sql}) AS v',
            [[value]], **options)

    member('match', '(1,2)', 'SELECT 1,2', [1,2], [[1,2]], sqlite=True)
    member('mismatch', '(1,2)', 'SELECT 1,3', [1,2], [[1,3]], sqlite=True)
    member('false-dominates-null', '(1,NULL)', 'SELECT 2,NULL::INTEGER', [1,None], [[2,None]])
    member('left-null', '(1,NULL)', 'SELECT 1,2', [1,None], [[1,2]], sqlite=True)
    member('right-null', '(1,2)', 'SELECT 1,NULL::INTEGER', [1,2], [[1,None]])
    member('both-null', '(NULL,NULL)', 'SELECT NULL::INTEGER,NULL::INTEGER', [None,None], [[None,None]])
    member('empty', '(1,2)', 'SELECT 1,2 WHERE FALSE', [1,2], [], sqlite=True)
    member('null-empty', '(NULL,NULL)', 'SELECT 1,2 WHERE FALSE', [None,None], [], sqlite=True)
    member('duplicate', '(1,2)', 'SELECT 1,2 UNION ALL SELECT 1,2', [1,2], [[1,2],[1,2]], sqlite=True)
    member('match-beats-unknown', '(1,2)', 'SELECT 1,NULL::INTEGER UNION ALL SELECT 1,2', [1,2], [[1,None],[1,2]])
    member('unknown-beats-false', '(1,2)', 'SELECT 1,NULL::INTEGER UNION SELECT 4,5', [1,2], [[1,None],[4,5]])
    member('all-false', '(1,2)', 'SELECT 3,2 UNION ALL SELECT 1,4', [1,2], [[3,2],[1,4]], sqlite=True)
    member('not-match', '(1,2)', 'SELECT 1,2', [1,2], [[1,2]], negated=True, sqlite=True)
    member('not-unknown', '(NULL,2)', 'SELECT 1,2', [None,2], [[1,2]], negated=True, sqlite=True)
    member('not-empty', '(NULL,2)', 'SELECT 1,2 WHERE FALSE', [None,2], [], negated=True, sqlite=True)
    member('three-fields', '(1,2,3)', 'SELECT 1,2,3', [1,2,3], [[1,2,3]], sqlite=True)
    member('four-fields', '(1,2,3,4)', 'SELECT 1,2,3,5', [1,2,3,4], [[1,2,3,5]], sqlite=True)
    member('one-field', 'ROW(1)', 'SELECT 1', [1], [[1]])
    member('contextual-string', "('1','2')", 'SELECT 1,2', [1,2], [[1,2]])
    member('contextual-null', '(NULL,2)', 'SELECT 1::BIGINT,2', [None,2], [[1,2]])
    member('int64', '(1::BIGINT,2)', 'SELECT 1,2::BIGINT', [1,2], [[1,2]])
    member('numeric-modifiers', '(1.23::NUMERIC(5,2),2)', 'SELECT 1.230::NUMERIC(6,3),2', ['1.23',2], [['1.23',2]])
    member('text', "('a','b')", "SELECT 'a','b'", ['a','b'], [['a','b']], sqlite=True)
    member('bpchar-text', "('a'::CHAR(3),2)", "SELECT 'a'::TEXT,2", ['a',2], [['a',2]])
    member('booleans', '(TRUE,FALSE)', 'SELECT TRUE,FALSE', [True,False], [[True,False]], sqlite=True)
    member('dates', "(DATE '2024-01-01',2)", "SELECT DATE '2024-01-01',2", ['2024-01-01',2], [['2024-01-01',2]])
    member('times', "(TIME '12:30:00',2)", "SELECT TIME '12:30:00',2", ['12:30',2], [['12:30',2]])
    member('jsonb', "('{\"a\":1}'::JSONB,2)", "SELECT '{\"a\":1}'::JSONB,2", ['json',2], [['json',2]])
    member('bytea', "('abc'::BYTEA,2)", "SELECT 'abc'::BYTEA,2", ['abc',2], [['abc',2]])
    member('arrays', '(ARRAY[1,2],2)', 'SELECT ARRAY[1,2],2', [[1,2],2], [[[1,2],2]])
    member('independent-default-collations', "('a'::TEXT,'b'::TEXT)", "SELECT 'a'::TEXT,'b'::TEXT", ['a','b'], [['a','b']])
    member('independent-explicit-fields', "('a' COLLATE \"C\",'b' COLLATE \"POSIX\")", "SELECT 'a' COLLATE \"C\",'b' COLLATE \"POSIX\"", ['a','b'], [['a','b']])
    member('child-collations', "('a','b')", "SELECT 'a' COLLATE \"C\",'b' COLLATE \"POSIX\"", ['a','b'], [['a','b']])
    member('explicit-left-wins-implicit-child', "('a' COLLATE \"C\",'b' COLLATE \"C\")", "SELECT 'a' COLLATE \"POSIX\",'b' COLLATE \"POSIX\"", ['a','b'], [['a','b']])
    member('anonymous-order', '(?,?)', 'SELECT ?,?', [1,2], [[1,2]], types='int,int,int,int', values=[1,2,1,2], sqlite=True)
    member('numbered-reordered', '($4,$1)', 'SELECT $3,$2', [1,2], [[1,2]], types='int,int,int,int', values=[2,2,1,1])
    member('numbered-repeated', '($1,$1)', 'SELECT $1,$1', [3,3], [[3,3]], types='int', values=[3])
    member('nullable-parameter', '($1,2)', 'SELECT 1,2', [None,2], [[1,2]], types='int?', values=[None])
    add('visible-cte', 'WITH c(a,b) AS(SELECT 1,2) SELECT (1,2) IN(SELECT a,b FROM c) AS v', [[True]], sqlite=True)
    member('derived-child', '(1,2)', 'SELECT a,b FROM (SELECT 1 AS a,2 AS b) q', [1,2], [[1,2]], sqlite=True)
    member('child-set-order-limit', '(2,3)', 'SELECT 1 AS a,2 AS b UNION ALL SELECT 2,3 ORDER BY a DESC LIMIT 1 OFFSET 0', [2,3], [[2,3]])
    member('scalar-fields', '((SELECT 1),(SELECT 2))', 'SELECT 1,2', [1,2], [[1,2]], sqlite=True)
    add('case-result', "SELECT CASE WHEN (1,2) IN(SELECT 1,2) THEN 'yes' ELSE 'no' END AS v", [['yes']], output=[col('text',False)])
    add('coalesce-result', 'SELECT COALESCE((NULL,2) IN(SELECT 1,2),FALSE) AS v', [[False]], output=[col('bool',False)], sqlite=True)
    add('null-predicate', 'SELECT ((NULL,2) IN(SELECT 1,2)) IS NULL AS v', [[True]], output=[col('bool',False)], sqlite=True)
    add('outer-items', 'SELECT (i.id,i.score) IN(SELECT id,score FROM items) AS v FROM items i',
        [[row_in([i[0],i[1]], [[x[0],x[1]] for x in data['items']])] for i in data['items']], sqlite=True)
    add('outer-labels', 'SELECT (l.id,l.category) IN(SELECT id,category FROM labels) AS v FROM labels l',
        [[row_in([l[0],l[1]], [[x[0],x[1]] for x in data['labels']])] for l in data['labels']], sqlite=True)
    member('item-score-membership', '(1,10)', 'SELECT id,score FROM items', [1,10], [[x[0],x[1]] for x in data['items']], sqlite=True)
    add('join-duplicate-membership', 'SELECT (i.id,l.id) IN(SELECT id,id FROM items) AS v FROM items i JOIN labels l ON i.id=l.id',
        [[row_in([i[0],l[0]], [[x[0],x[0]] for x in data['items']])] for i in data['items'] for l in data['labels'] if i[0]==l[0]], sqlite=True)
    add('cte-anonymous-global-order', 'WITH c(a,b) AS(SELECT ?,?) SELECT (?,?) IN(SELECT a,b FROM c WHERE ?>0) AS v',
        [[True]], types='int,int,int,int,int', values=[1,2,1,2,1], sqlite=True)
    assert len(result) == len({r['id'] for r in result}) == len({r['sql'] for r in result}) == 50
    return result


def all_cases():
    rows = cases()
    by_state = {state: {r['id']: r['expected_rows'] for r in cases(population(state))} for state in STATES}
    for row in rows:
        row['expected_rows_by_state'] = {state: by_state[state][row['id']] for state in STATES}
    return rows


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--check', action='store_true')
    args = parser.parse_args()
    for name, value in [('schema.json', schema()), ('synthetic.json', all_cases())]:
        content = json.dumps(value, indent=2, ensure_ascii=False) + '\n'
        path = FIXTURES / name
        if args.check:
            assert path.read_text() == content, f'stale {path}'
        else:
            path.parent.mkdir(parents=True, exist_ok=True)
            path.write_text(content)
    print('PASS: 50 authored row-IN subqueries with four independent table populations')


if __name__ == '__main__':
    main()
