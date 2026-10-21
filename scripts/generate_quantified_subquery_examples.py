#!/usr/bin/env python3
"""Author fifty quantified-query comparisons with a separate three-valued model."""
import argparse
from decimal import Decimal
import json
from pathlib import Path

from generate_subquery_examples import DATA, STATES, population, schema, col, sql_not

ROOT = Path(__file__).resolve().parents[1]
FIXTURES = ROOT / 'fixtures/quantified_subqueries'


def compare(left, operator, right):
    if left is None or right is None:
        return None
    if operator == '=': return left == right
    if operator == '<>': return left != right
    if operator == '<': return left < right
    if operator == '<=': return left <= right
    if operator == '>': return left > right
    if operator == '>=': return left >= right
    raise ValueError(operator)


def quantified(left, operator, quantifier, right):
    observations = [compare(left, operator, value) for value in right]
    if quantifier in ('ANY', 'SOME'):
        return True if any(value is True for value in observations) else None if any(value is None for value in observations) else False
    if quantifier == 'ALL':
        return False if any(value is False for value in observations) else None if any(value is None for value in observations) else True
    raise ValueError(quantifier)


def cases(data=DATA):
    rows = []
    def add(shape, sql, expected, *, types='', values=None, output=None):
        rows.append({'id': f'quantified-query-{len(rows)+1:02d}-{shape}',
                     'factor': 'quantified_subquery', 'shape': shape, 'source_kind': 'synthetic',
                     'sql': sql+';', 'catalogFile': 'fixtures/quantified_subqueries/schema.json',
                     'parameter_types': types, 'parameter_values': [] if values is None else values,
                     'output_columns': [col('bool', False)] if output is None else output,
                     'expected_rows': expected})
    def member(shape, lhs_sql, operator, quantifier, child_sql, left, right, *, nullable=False, **options):
        add(shape, f'SELECT {lhs_sql} {operator} {quantifier}({child_sql}) AS v',
            [[quantified(left, operator, quantifier, right)]], output=[col('bool',nullable)], **options)
    for name, operator in [('equal','='),('unequal','<>'),('less','<'),('less-equal','<='),('greater','>'),('greater-equal','>=')]:
        for quantifier in ('ANY','SOME','ALL'):
            member(f'{name}-{quantifier.lower()}', '2', operator, quantifier,
                   'SELECT 1 UNION ALL SELECT 2 UNION ALL SELECT 3', 2, [1,2,3])
    for quantifier in ('ANY','SOME','ALL'):
        member(f'null-empty-{quantifier.lower()}', 'NULL', '=', quantifier, 'SELECT 1 WHERE FALSE', None, [], nullable=True)
    for quantifier in ('ANY','SOME','ALL'):
        member(f'dominant-{quantifier.lower()}', '2', '=', quantifier,
               'SELECT NULL::INTEGER UNION ALL SELECT 2 UNION ALL SELECT 3', 2, [None,2,3], nullable=True)
        member(f'unknown-{quantifier.lower()}', '2', '=', quantifier,
               'SELECT NULL::INTEGER UNION ALL SELECT 3', 2, [None,3], nullable=True)
    for quantifier in ('ANY','SOME','ALL'):
        member(f'null-only-{quantifier.lower()}', '2', '=', quantifier,
               'SELECT NULL::INTEGER', 2, [None], nullable=True)
    add('negated-unknown', 'SELECT NOT (2 = ANY(SELECT NULL::INTEGER)) AS v', [[sql_not(quantified(2,'=','ANY',[None]))]], output=[col('bool',True)])
    member('contextual-left', "'2'", '<=', 'ALL', 'SELECT 2', 2, [2])
    member('numeric-modifiers', '1.23::NUMERIC(5,2)', '=', 'SOME', 'SELECT 1.230::NUMERIC(6,3)', Decimal('1.23'), [Decimal('1.230')])
    member('date', "DATE '2024-01-01'", '<', 'ALL', "SELECT DATE '2024-01-02'", '2024-01-01', ['2024-01-02'])
    member('explicit-collation', "'a' COLLATE \"C\"", '=', 'ANY', "SELECT 'a' COLLATE \"POSIX\"", 'a', ['a'])
    member('boolean', 'TRUE', '<>', 'ALL', 'SELECT FALSE', True, [False])
    member('bytea', "'abc'::BYTEA", '=', 'SOME', "SELECT 'abc'::BYTEA", b'abc', [b'abc'])
    member('array-output', 'ARRAY[1,2]', '=', 'ANY', 'SELECT ARRAY[1,2]', [1,2], [[1,2]])
    member('anonymous-order', '?', '<', 'ANY', 'SELECT ?', 2, [3], types='int,int', values=[2,3])
    member('numbered-reordered', '$2', '>=', 'ALL', 'SELECT $1', 7, [2], types='int,int', values=[2,7])
    member('numbered-repeated', '$1', '=', 'SOME', 'SELECT $1', 4, [4], types='int', values=[4])
    member('nullable-parameter', '$1', '=', 'ALL', 'SELECT 1', None, [1], nullable=True, types='int?', values=[None])
    add('visible-cte', 'WITH c(x) AS(SELECT 3) SELECT 2 < ANY(SELECT x FROM c) AS v', [[True]])
    add('cte-shadow', 'WITH c(x) AS(SELECT 3) SELECT 2 < ALL(WITH c(x) AS(SELECT 1) SELECT x FROM c) AS v', [[False]])
    member('derived-child', '2', '<=', 'ALL', 'SELECT x FROM(SELECT 3 AS x)q', 2, [3])
    member('child-order-limit', '2', '=', 'ANY', 'SELECT 1 AS x UNION ALL SELECT 2 ORDER BY x DESC LIMIT 1', 2, [2])
    member('scalar-left', '(SELECT 2)', '=', 'ALL', 'SELECT 2', 2, [2], nullable=True)
    add('outer-items', 'SELECT i.score = ANY(SELECT score FROM items) AS v FROM items i',
        [[quantified(row[1],'=','ANY',[r[1] for r in data['items']])] for row in data['items']], output=[col('bool',True)])
    member('table-child', '1', '<', 'ALL', 'SELECT id FROM labels', 1, [row[0] for row in data['labels']])
    add('where-membership', 'SELECT i.id AS v FROM items i WHERE i.id = ANY(SELECT id FROM labels)',
        [[row[0]] for row in data['items'] if quantified(row[0],'=','ANY',[r[0] for r in data['labels']]) is True],
        output=[col('int32',False)])
    assert len(rows) == len({row['id'] for row in rows}) == len({row['sql'] for row in rows}) == 50
    return rows


def all_cases():
    rows = cases()
    observations = {state: {row['id']: row['expected_rows'] for row in cases(population(state))} for state in STATES}
    for row in rows:
        row['expected_rows_by_state'] = {state: observations[state][row['id']] for state in STATES}
    return rows



def operator_direction_cases():
    rows=[]
    for name,op in [('equal','='),('unequal','<>'),('less','<'),('less-equal','<='),('greater','>'),('greater-equal','>=')]:
        for quantifier in ('ANY','SOME','ALL'):
            value=quantified(2,op,quantifier,[3])
            rows.append({'id':f'quantified-direction-{name}-{quantifier.lower()}',
                'factor':'quantified_subquery','shape':f'direction-{name}-{quantifier.lower()}',
                'source_kind':'synthetic','sql':f'SELECT 2 {op} {quantifier}(SELECT 3) AS v;',
                'catalogFile':'fixtures/quantified_subqueries/schema.json','parameter_types':'','parameter_values':[],
                'output_columns':[col('bool',False)],'expected_rows':[[value]],
                'expected_rows_by_state':{state:[[value]] for state in STATES}})
    return rows


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--check',action='store_true')
    args = parser.parse_args()
    for name, value in [('schema.json',schema()),('synthetic.json',all_cases()),('operator_direction.json',operator_direction_cases())]:
        content = json.dumps(value,indent=2,ensure_ascii=False)+'\n'
        path = FIXTURES/name
        if args.check: assert path.read_text() == content, f'stale {path}'
        else:
            path.parent.mkdir(parents=True,exist_ok=True)
            path.write_text(content)
    print('PASS:50 quantified-query examples with independent three-valued expectations')


if __name__ == '__main__': main()
