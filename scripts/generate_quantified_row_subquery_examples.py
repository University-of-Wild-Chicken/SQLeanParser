#!/usr/bin/env python3
"""Fifty flat-row quantified-query fixtures with independent SQL truth tables."""
import argparse
import json
from pathlib import Path
from generate_subquery_examples import DATA,STATES,population,schema,col

ROOT=Path(__file__).resolve().parents[1]
FIXTURES=ROOT/'fixtures/quantified_subqueries'


def row_compare(left,op,right):
    assert left and len(left)==len(right)
    if op in ('=','<>'):
        if any(a is not None and b is not None and a!=b for a,b in zip(left,right)):
            equal=False
        elif any(a is None or b is None for a,b in zip(left,right)): equal=None
        else: equal=True
        return equal if op=='=' or equal is None else not equal
    for a,b in zip(left,right):
        if a is None or b is None: return None
        if a!=b:
            return a<b if op in ('<','<=') else a>b if op in ('>','>=') else invalid_operator(op)
    if op in ('<=','>='): return True
    if op in ('<','>'): return False
    return invalid_operator(op)


def invalid_operator(op): raise ValueError(op)


def row_quantified(left,op,quantifier,right):
    comparisons=[row_compare(left,op,row) for row in right]
    if quantifier in ('ANY','SOME'):
        return True if any(value is True for value in comparisons) else None if any(value is None for value in comparisons) else False
    if quantifier=='ALL':
        return False if any(value is False for value in comparisons) else None if any(value is None for value in comparisons) else True
    raise ValueError(quantifier)


def cases(data=DATA):
    rows=[]
    def add(shape,sql,expected,*,types='',values=None):
        rows.append({'id':f'quantified-row-query-{len(rows)+1:02d}-{shape}','factor':'quantified_row_subquery',
                     'shape':shape,'source_kind':'synthetic','sql':sql+';',
                     'catalogFile':'fixtures/quantified_subqueries/schema.json',
                     'parameter_types':types,'parameter_values':[] if values is None else values,
                     'output_columns':[col('bool',True)],'expected_rows':expected})
    def member(shape,lhs,op,quantifier,child,left,right,**options):
        add(shape,f'SELECT {lhs} {op} {quantifier}({child}) AS v',[[row_quantified(left,op,quantifier,right)]],**options)
    for name,op in [('equal','='),('unequal','<>'),('less','<'),('less-equal','<='),('greater','>'),('greater-equal','>=')]:
        for quantifier in ('ANY','SOME','ALL'):
            member(f'{name}-{quantifier.lower()}','(0,1)',op,quantifier,'SELECT 1,0',[0,1],[[1,0]])
    for quantifier in ('ANY','SOME','ALL'):
        member('empty-'+quantifier.lower(),'(NULL,2)','=',quantifier,'SELECT 1,2 WHERE FALSE',[None,2],[])
        member('lexical-dominance-'+quantifier.lower(),'(0,NULL)','<',quantifier,'SELECT 1,NULL::INTEGER',[0,None],[[1,None]])
        member('equality-dominance-'+quantifier.lower(),'(1,2)','=',quantifier,'SELECT 1,NULL::INTEGER UNION ALL SELECT 1,2 UNION ALL SELECT 3,4',[1,2],[[1,None],[1,2],[3,4]])
        member('unknown-'+quantifier.lower(),'(1,2)','=',quantifier,'SELECT 1,NULL::INTEGER',[1,2],[[1,None]])
    member('one-field','ROW(1)','<=','ALL','SELECT 2',[1],[[2]])
    member('three-fields','(1,2,3)','>','ANY','SELECT 1,2,2',[1,2,3],[[1,2,2]])
    member('four-fields','(1,2,3,4)','<>','SOME','SELECT 1,2,3,5',[1,2,3,4],[[1,2,3,5]])
    member('contextual-string',"('1',2)",'=','ANY','SELECT 1,2',[1,2],[[1,2]])
    member('bigint','(1::BIGINT,2)','<','ALL','SELECT 2,2::BIGINT',[1,2],[[2,2]])
    member('numeric-modifiers','(1.23::NUMERIC(5,2),2)','=','SOME','SELECT 1.230::NUMERIC(6,3),2',[123,2],[[123,2]])
    member('text',"('a','b')",'<','ANY',"SELECT 'a','c'",['a','b'],[['a','c']])
    member('date',"(DATE '2024-01-01',2)",'<','ALL',"SELECT DATE '2024-01-02',2",['2024-01-01',2],[['2024-01-02',2]])
    member('bytea',"('abc'::BYTEA,2)",'=','SOME',"SELECT 'abc'::BYTEA,2",['abc',2],[['abc',2]])
    member('boolean','(TRUE,FALSE)','>=','ALL','SELECT TRUE,FALSE',[True,False],[[True,False]])
    member('array-field','(ARRAY[1,2],2)','=','ANY','SELECT ARRAY[1,2],2',[[1,2],2],[[[1,2],2]])
    member('independent-field-collations',"('a' COLLATE \"C\",'b' COLLATE \"POSIX\")",'=','ALL',"SELECT 'a' COLLATE \"C\",'b' COLLATE \"POSIX\"",['a','b'],[['a','b']])
    member('left-explicit-wins',"('a' COLLATE \"C\",2)",'=','SOME',"SELECT 'a' COLLATE \"POSIX\",2",['a',2],[['a',2]])
    member('anonymous-order','(?,?)','<','ANY','SELECT ?,?',[1,2],[[1,3]],types='int,int,int,int',values=[1,2,1,3])
    member('numbered-reordered','($4,$1)','>=','ALL','SELECT $3,$2',[2,3],[[2,1]],types='int,int,int,int',values=[3,1,2,2])
    member('numbered-repeated','($1,$1)','=','SOME','SELECT $1,$1',[4,4],[[4,4]],types='int',values=[4])
    add('visible-cte','WITH c(a,b) AS(SELECT 1,2) SELECT (1,2) = ANY(SELECT a,b FROM c) AS v',[[True]])
    member('derived-child','(1,2)','=','ALL','SELECT a,b FROM(SELECT 1 AS a,2 AS b)q',[1,2],[[1,2]])
    member('table-child','(1,10)','=','ANY','SELECT id,score FROM items',[1,10],[[r[0],r[1]] for r in data['items']])
    add('outer-items','SELECT (i.id,i.score) = ANY(SELECT id,score FROM items) AS v FROM items i',
        [[row_quantified([r[0],r[1]],'=','ANY',[[s[0],s[1]] for s in data['items']])] for r in data['items']])
    assert len(rows)==len({r['id'] for r in rows})==len({r['sql'] for r in rows})==50
    return rows


def all_cases():
    rows=cases()
    states={state:{r['id']:r['expected_rows'] for r in cases(population(state))} for state in STATES}
    for row in rows: row['expected_rows_by_state']={state:states[state][row['id']] for state in STATES}
    return rows


def main():
    parser=argparse.ArgumentParser(description=__doc__);parser.add_argument('--check',action='store_true');args=parser.parse_args()
    content=json.dumps(all_cases(),indent=2,ensure_ascii=False)+'\n';path=FIXTURES/'row_synthetic.json'
    if args.check: assert path.read_text()==content,f'stale {path}'
    else:
        path.parent.mkdir(parents=True,exist_ok=True);path.write_text(content)
    print('PASS:50 flat-row quantified-query examples with independent lexical/equality NULL models')


if __name__=='__main__':main()
