#!/usr/bin/env python3
"""Fifty authored VALUES queries with preregistered finite rows and metadata.

Expectations are declared from the authored literals and ordinary mathematical
operations. They are never populated from SQLean or database output. Native
preflight separately tests PostgreSQL type/modifier/collation interpretations.
"""
import argparse
import json
from pathlib import Path

ROOT=Path(__file__).resolve().parents[1]
FIXTURES=ROOT/'fixtures/values_queries'
NATIVE={
 'int32':('integer','integer',23), 'smallint':('smallint','smallint',21),
 'bigint':('bigint','bigint',20), 'bool':('boolean','boolean',16),
 'text':('text','text',25), 'name':('name','name',19),
 'numeric':('numeric','numeric',1700), 'numeric(5,2)':('numeric(5,2)','numeric',1700),
 'varchar':('character varying','character varying',1043),
 'varchar(3)':('character varying(3)','character varying',1043),
 'char(3)':('character(3)','character',1042), 'bpchar':('bpchar','character',1042),
 'date':('date','date',1082), 'timestamp(2)':('timestamp(2) without time zone','timestamp without time zone',1114),
 'integer[]':('integer[]','integer[]',1007), 'numeric(5,2)[]':('numeric(5,2)[]','numeric[]',1231),
 'name[]':('name[]','name[]',1003),
}
_AUTO=object()

def column(type_='int32',nullable=False,name='column1',collation=_AUTO):
 display,native,oid=NATIVE[type_]
 if collation is _AUTO:
  collation='C' if type_ in ('name','name[]') else 'default' if type_ in ('text','varchar','varchar(3)','char(3)','bpchar') else None
 return {'name':name,'type':type_,'nullable':nullable,'collation':collation,
         'postgres_type':display,'native_type':native,'oid':oid}

def schema():
 return {'tables':[],'collations':{'encoding':'UTF8','entries':[
  {'id':name,'schema':'pg_catalog','name':name,'encoding':None,'deterministic':True,'exposeUnqualified':True}
  for name in ('default','C','POSIX')]}}

def all_cases():
 rows=[]
 def add(shape,sql,expected,columns=None,types='',values=None,ordered=False):
  rows.append({'id':f'values-query-{len(rows)+1:02d}-{shape}','factor':'values_query','shape':shape,
   'source_kind':'synthetic','sql':sql+';','catalogFile':'fixtures/values_queries/schema.json',
   'parameter_types':types,'parameter_values':[] if values is None else values,
   'output_columns':[column()] if columns is None else columns,'expected_rows':expected,'ordered':ordered})
 add('integer','VALUES (1)',[[1]])
 add('duplicates','VALUES (1),(1),(2)',[[1],[1],[2]])
 add('heterogeneous-columns',"VALUES (1,TRUE,'a'),(2,FALSE,'b')",[[1,True,'a'],[2,False,'b']],
     [column(),column('bool',name='column2'),column('text',name='column3')])
 add('all-null','VALUES (NULL),(NULL)',[[None],[None]],[column('text',True)])
 add('unknown-strings',"VALUES ('a'),('b')",[['a'],['b']],[column('text')])
 add('simultaneous-null-null-int','VALUES (NULL),(NULL),(1)',[[None],[None],[1]],[column(nullable=True)])
 add('simultaneous-unknown-conversion',"VALUES (NULL),('2'),(3)",[[None],[2],[3]],[column(nullable=True)])
 add('nullable-per-column',"VALUES (1,NULL),(NULL,'b'),(3,'c')",[[1,None],[None,'b'],[3,'c']],
     [column(nullable=True),column('text',True,'column2')])
 add('numeric-common','VALUES (1),(2.5)',[[1],[2.5]],[column('numeric')])
 add('bigint-common','VALUES (1),(2147483648)',[[1],[2147483648]],[column('bigint')])
 add('smallint','VALUES (1::SMALLINT),(2::SMALLINT)',[[1],[2]],[column('smallint')])
 add('varchar-modifier-agreement',"VALUES ('ab'::VARCHAR(3)),('xy'::VARCHAR(3))",[['ab'],['xy']],[column('varchar(3)')])
 add('varchar-modifier-disagreement',"VALUES ('ab'::VARCHAR(3)),('xy'::VARCHAR(4))",[['ab'],['xy']],[column('varchar')])
 add('varchar-unknown-erases-modifier',"VALUES ('ab'::VARCHAR(3)),('xy')",[['ab'],['xy']],[column('varchar')])
 add('numeric-modifier-agreement','VALUES (1.25::NUMERIC(5,2)),(2.5::NUMERIC(5,2))',[[1.25],[2.5]],[column('numeric(5,2)')])
 add('numeric-modifier-disagreement','VALUES (1.25::NUMERIC(5,2)),(2.5::NUMERIC(6,2))',[[1.25],[2.5]],[column('numeric')])
 add('char-modifier-agreement',"VALUES ('x'::CHAR(3)),('yz'::CHAR(3))",[['x  '],['yz ']],[column('char(3)')])
 add('char-modifier-disagreement',"VALUES ('x'::CHAR(3)),('yz'::CHAR(4))",[['x  '],['yz  ']],[column('bpchar')])
 add('date',"VALUES (DATE '2024-01-02'),(DATE '2024-01-03')",[['2024-01-02'],['2024-01-03']],[column('date')])
 add('timestamp-modifier',"VALUES (TIMESTAMP(2) '2024-01-02 03:04:05.12'),(TIMESTAMP(2) '2024-01-02 03:04:06.25')",
     [['2024-01-02T03:04:05.12'],['2024-01-02T03:04:06.25']],[column('timestamp(2)')])
 add('array-null-elements','VALUES (ARRAY[1,NULL]),(ARRAY[2,3])',[[[1,None]],[[2,3]]],[column('integer[]')])
 add('array-modifiers','VALUES (ARRAY[1.25::NUMERIC(5,2)]),(ARRAY[2.5::NUMERIC(5,2)])',[[[1.25]],[[2.5]]],[column('numeric(5,2)[]')])
 add('name-unknown',"VALUES ('x'::NAME),('y')",[['x'],['y']],[column('name')])
 add('explicit-collation',"VALUES ('x' COLLATE \"C\"),('y')",[['x'],['y']],[column('text',collation='C')])
 add('separate-column-collations',"VALUES ('a' COLLATE \"C\",'b' COLLATE \"POSIX\"),('c','d')",[['a','b'],['c','d']],
     [column('text',collation='C'),column('text',name='column2',collation='POSIX')])
 add('implicit-collation-conflict',"VALUES ((SELECT 'x' COLLATE \"C\")),((SELECT 'y' COLLATE \"POSIX\"))",[['x'],['y']],[column('text',True,collation=None)])
 add('array-coercion-collation',"VALUES (ARRAY[(SELECT 'x'::NAME COLLATE \"POSIX\")]),(ARRAY['y'])",[[['x']],[['y']]],[column('name[]',collation=None)])
 add('coalesce-expressions','VALUES (COALESCE(NULL,1)),(COALESCE(NULL,2))',[[1],[2]])
 add('arithmetic-expressions','VALUES (1+2),(3*4),(9-5)',[[3],[12],[4]])
 add('boolean-null-expressions','VALUES (TRUE AND NULL),(FALSE OR NULL),(NOT FALSE)',[[None],[None],[True]],[column('bool',True)])
 add('derived-alias','SELECT q.n FROM (VALUES (1),(2)) AS q(n)',[[1],[2]],[column(name='n')])
 add('derived-prefix-alias',"SELECT * FROM (VALUES (1,'a'),(2,'b')) AS q(n)",[[1,'a'],[2,'b']],
     [column(name='n'),column('text',name='column2')])
 add('cte-default-labels','WITH q AS (VALUES (1),(2)) SELECT * FROM q',[[1],[2]])
 add('cte-prefix-alias',"WITH q(n) AS (VALUES (1,'a'),(2,'b')) SELECT * FROM q",[[1,'a'],[2,'b']],
     [column(name='n'),column('text',name='column2')])
 add('cte-visible-child','WITH a(n) AS (SELECT 4), q AS (VALUES ((SELECT n FROM a)),(5)) SELECT * FROM q',[[4],[5]],[column(nullable=True)])
 add('union-all','VALUES (1),(2) UNION ALL VALUES (2),(3)',[[1],[2],[2],[3]])
 add('union-distinct','VALUES (1),(2) UNION VALUES (2),(3)',[[1],[2],[3]])
 add('intersect','VALUES (1),(2),(2) INTERSECT VALUES (2),(3)',[[2]])
 add('except-all','VALUES (1),(2),(2) EXCEPT ALL VALUES (2)',[[1],[2]])
 add('ordered-limit','VALUES (3),(1),(2) ORDER BY 1 LIMIT 2',[[1],[2]],ordered=True)
 add('ordered-offset','VALUES (3),(1),(2) ORDER BY column1 DESC OFFSET 1 LIMIT 1',[[2]],ordered=True)
 add('derived-filter','SELECT n FROM (VALUES (1),(2),(3)) AS q(n) WHERE n>1',[[2],[3]],[column(name='n')])
 add('empty-derived','SELECT n FROM (VALUES (1),(2)) AS q(n) WHERE FALSE',[],[column(name='n')])
 add('anonymous-row-order','VALUES (?,?),(?,?)',[[1,2],[3,4]],[column(),column(name='column2')],types='int,int,int,int',values=[1,2,3,4])
 add('numbered-repeated-reordered','VALUES ($2,$1),($1,$2)',[[7,2],[2,7]],[column(),column(name='column2')],types='int,int',values=[2,7])
 add('nullable-parameter','VALUES ($1),(\'x\')',[[None],['x']],[column('text',True)],types='text?',values=[None])
 add('parameter-typmod-erasure',"VALUES ($1),('xy'::VARCHAR(3))",[['ab'],['xy']],[column('varchar')],types='varchar(3)',values=['ab'])
 add('scalar-values-child','SELECT (VALUES (7)) AS v',[[7]],[column(nullable=True,name='v')])
 add('exists-values-child','SELECT EXISTS(VALUES (NULL)) AS v',[[True]],[column('bool',name='v')])
 add('in-values-child','SELECT 2 IN(VALUES (1),(2),(NULL::INTEGER)) AS v',[[True]],[column('bool',True,'v')])
 assert len(rows)==len({r['id'] for r in rows})==len({r['sql'] for r in rows})==50
 return rows

def boundary_cases():
 # Static outcomes and native stage SQLSTATEs are distinct declarations.
 items=[
 ('missing-rows','VALUES','invalid','input.parse','42601',None,None,None),
 ('empty-row','VALUES ()','invalid','input.parse','42601',None,None,None),
 ('mismatched-arity','VALUES (1),(2,3)','invalid','values_arity','42601',None,None,None),
 ('incompatible-types',"VALUES (1),('x'::TEXT)",'invalid','values_common_type','42804',None,None,None),
 ('boolean-integer','VALUES (TRUE),(1)','invalid','values_common_type','42804',None,None,None),
 ('operator-signature','VALUES (1+TRUE)','invalid','operator_signature','42883',None,None,None),
 ('explicit-collation-conflict',"VALUES ('x' COLLATE \"C\"),('y' COLLATE \"POSIX\")",'invalid','collation_conflict','42P21',None,None,None),
 ('values-boundary-finalizes-unknown','VALUES (NULL),(NULL) UNION SELECT 1','invalid','set_common_type','42804',None,None,None),
 ('limit-negative','VALUES (1) LIMIT -1','valid',None,'00000','00000','2201W',[column()]),
 ('offset-negative','VALUES (1) OFFSET -1','valid',None,'00000','00000','2201X',[column()]),
 ('division-runtime','VALUES (1/0)','valid',None,'00000','22012','22012',[column()]),
 ('literal-conversion',"VALUES ('bad'::INTEGER)",'valid',None,'22P02',None,None,[column()]),
 ('scalar-cardinality','SELECT (VALUES (1),(2)) AS v','valid',None,'00000','00000','21000',[column(nullable=True,name='v')]),
 ]
 return [{'id':name,'source_kind':'synthetic','sql':sql,'status':status,'diagnostic':diagnostic,
          'prepare':prepare,'plan':plan,'execute':execute,'output_columns':columns}
         for name,sql,status,diagnostic,prepare,plan,execute,columns in items]

def main():
 p=argparse.ArgumentParser(description=__doc__);p.add_argument('--check',action='store_true');args=p.parse_args()
 for name,value in [('synthetic.json',all_cases()),('schema.json',schema()),('boundaries.json',boundary_cases())]:
  text=json.dumps(value,indent=2,ensure_ascii=False,allow_nan=False)+'\n';path=FIXTURES/name
  if args.check:assert path.read_text()==text,f'stale {path}'
  else:path.parent.mkdir(parents=True,exist_ok=True);path.write_text(text)
 print('PASS:50 authored VALUES queries and13 separately classified native stage boundaries')
if __name__=='__main__':main()
