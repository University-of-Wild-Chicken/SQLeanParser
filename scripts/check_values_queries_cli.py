#!/usr/bin/env python3
"""VALUES static contracts and independent finite PostgreSQL observations.

--source-only checks authored native fixtures before the typed implementation
exists. Actual records, types/OIDs, collations and gdesc modifiers are observed
without an expected-type RETURNS TABLE declaration. Stage controls distinguish
analysis, planning and execution. Downloaded SQL and setup are never executed.
"""
import argparse
from collections import Counter
import json
from pathlib import Path
import subprocess

from check_advanced_cli import literal, question_parameters
from check_assurance_cli import PROFILES, EXIT_CODES
from check_postgresql_cli import connection, run, sql_literal
from check_renderer_corpus import parameters, replay, unique_json, validate_report
from check_renderer_corpus import PROFILES as RENDER_PROFILES
from generate_values_query_examples import all_cases, boundary_cases, schema

ROOT=Path(__file__).resolve().parents[1]
FIXTURES=ROOT/'fixtures/values_queries'
EXE=ROOT/'.lake/build/bin/sqlean'
NATIVE_COLLATIONS={None:None,'default':'"default"','C':'"C"','POSIX':'"POSIX"'}

def frozen(value):return json.dumps(value,sort_keys=True,separators=(',',':'),ensure_ascii=False,allow_nan=False)

def load_cases():
 rows=json.loads((FIXTURES/'synthetic.json').read_text(),object_pairs_hook=unique_json)
 assert frozen(rows)==frozen(all_cases()),'authored VALUES fixture/model mismatch'
 assert frozen(json.loads((FIXTURES/'schema.json').read_text(),object_pairs_hook=unique_json))==frozen(schema())
 assert len(rows)==len({r['id'] for r in rows})==len({r['sql'] for r in rows})==50
 for row in rows:
  assert row['source_kind']=='synthetic' and row['factor']=='values_query'
  assert row['catalogFile']=='fixtures/values_queries/schema.json'
  assert row['output_columns'] and type(row['ordered']) is bool
  assert all(type(c['nullable']) is bool and type(c['oid']) is int and c['collation'] in NATIVE_COLLATIONS for c in row['output_columns'])
  assert all(len(values)==len(row['output_columns']) for values in row['expected_rows'])
  slots={slot for _,slot in parameters(row['sql'],'postgres')}
  assert slots==set(range(1,len(row['parameter_values'])+1))
 return rows

def load_boundaries():
 rows=json.loads((FIXTURES/'boundaries.json').read_text(),object_pairs_hook=unique_json)
 assert frozen(rows)==frozen(boundary_cases()),'VALUES stage boundary registry changed'
 assert len(rows)==len({r['id'] for r in rows})==13
 assert Counter(r['status'] for r in rows)=={'invalid':8,'valid':5}
 return rows

def validate_static(result,row):
 status=row.get('status','valid')
 report=json.loads(result.stdout,object_pairs_hook=unique_json)
 assert result.returncode==EXIT_CODES[status] and isinstance(report,dict),(row['id'],result,report)
 if row.get('diagnostic')=='input.parse':
  for key,value in {'status':'invalid','assurance':'checked-roundtrip','profile':RENDER_PROFILES['identity'],
                    'mode':'identity','evidence':'none','rendererVersion':'0.2'}.items():
   assert report.get(key)==value,(row['id'],key,report)
  assert report.get('diagnostic',{}).get('code')=='input.parse'
  assert report.get('semanticPreservation') is False
  assert not {'sql','parameterMap','theorems','outputColumns','outputCollations'} & report.keys()
  return report
 for k,v in {'status':status,'assurance':'declarative','profile':PROFILES['contract'],
             'evidence':'declarative-derivation' if status=='valid' else 'none'}.items():
  assert report.get(k)==v,(row['id'],k,report)
 if status=='valid':
  assert report.get('catalogUnchanged') is True and report.get('typePrecision')=='exact'
  wanted=[{k:c[k] for k in ('name','type','nullable')} for c in row['output_columns']]
  assert frozen(report.get('outputColumns'))==frozen(wanted),(row['id'],report,wanted)
  assert report.get('outputCollations')==[c['collation'] for c in row['output_columns']]
  assert 'diagnostic' not in report
 else:
  assert report.get('diagnostic',{}).get('code')==row['diagnostic'],(row['id'],report)
  assert 'outputColumns' not in report and 'outputCollations' not in report
 return report

def validity(row,sql=None):
 args=([str(EXE),'--render-assurance','identity'] if row.get('diagnostic')=='input.parse'
       else [str(EXE),'--assurance','contract','--schema',str(FIXTURES/'schema.json')])
 if row.get('parameter_types'):args+=['--param-types',row['parameter_types']]
 result=subprocess.run(args,input=row['sql'] if sql is None else sql,text=True,capture_output=True,timeout=30,check=False,cwd=ROOT)
 return validate_static(result,row)

def render(mode,sql):
 result=subprocess.run([str(EXE),'--render-assurance',mode],input=sql,text=True,capture_output=True,timeout=30,check=False,cwd=ROOT)
 return validate_report(result,mode,sql)

def metadata_sql(row,sql):
 assert row['source_kind']=='synthetic','only authored SQL may execute'
 names=','.join('c'+str(i) for i in range(len(row['output_columns'])))
 fields=[]
 for i in range(len(row['output_columns'])):
  value=f'q.c{i}'
  fields.append("jsonb_build_object('type',pg_typeof("+value+")::TEXT,'oid',pg_typeof("+value+")::OID::BIGINT,'collation',CASE WHEN EXISTS(SELECT 1 FROM pg_catalog.pg_type t WHERE t.oid=pg_typeof("+value+") AND t.typcollation<>0) THEN pg_collation_for("+value+") ELSE NULL::TEXT END)")
 return 'SELECT jsonb_build_array('+','.join(fields)+') AS observed FROM (VALUES(0)) seed(dummy) LEFT JOIN ('+sql.strip().removesuffix(';')+') q('+names+') ON TRUE LIMIT 1'

CAPTURE=r'''CREATE FUNCTION pg_temp.values_capture(command TEXT) RETURNS JSONB LANGUAGE plpgsql AS $$
DECLARE item RECORD; observed JSONB:='[]'; BEGIN
 FOR item IN EXECUTE command LOOP observed:=observed||jsonb_build_array(to_jsonb(item)); END LOOP;
 RETURN jsonb_build_object('sqlstate','00000','rows',observed);
 EXCEPTION WHEN OTHERS THEN RETURN jsonb_build_object('sqlstate',SQLSTATE,'rows',NULL);
END $$;'''
STAGES=r'''CREATE FUNCTION pg_temp.values_stages(q TEXT) RETURNS JSONB LANGUAGE plpgsql AS $$
DECLARE observed JSONB; BEGIN
 BEGIN EXECUTE 'PREPARE values_guard AS '||q; observed:=jsonb_build_object('prepare','00000');
 EXCEPTION WHEN OTHERS THEN RETURN jsonb_build_object('prepare',SQLSTATE,'plan',NULL,'execute',NULL); END;
 BEGIN EXECUTE 'EXPLAIN '||q; observed:=observed||jsonb_build_object('plan','00000');
 EXCEPTION WHEN OTHERS THEN observed:=observed||jsonb_build_object('plan',SQLSTATE); END;
 BEGIN EXECUTE 'EXECUTE values_guard'; observed:=observed||jsonb_build_object('execute','00000');
 EXCEPTION WHEN OTHERS THEN observed:=observed||jsonb_build_object('execute',SQLSTATE); END;
 DEALLOCATE values_guard; RETURN observed;
END $$;'''

def native_script(rows,canonical=None,boundaries=None,boundary_canonical=None):
 assert rows and len({r['id'] for r in rows})==len(rows)
 assert all(r['source_kind']=='synthetic' for r in rows),'only authored SQL may execute'
 if canonical is not None:assert len(rows)==len(canonical) and all(isinstance(sql,str) and sql.strip() for sql in canonical),'missing canonical VALUES query'
 if boundaries is None:boundaries=[]
 assert all(r['source_kind']=='synthetic' for r in boundaries),'only authored stage queries may execute'
 assert len({r['id'] for r in boundaries})==len(boundaries)
 if boundary_canonical is not None:
  assert len(boundaries)==len(boundary_canonical),'missing canonical VALUES boundary'
  for row,sql in zip(boundaries,boundary_canonical):
   assert (sql is None if row['diagnostic']=='input.parse' else isinstance(sql,str) and bool(sql.strip())), 'missing or unexpected canonical VALUES boundary'
 commands=['BEGIN;',"SET LOCAL statement_timeout='5s';",'SET LOCAL standard_conforming_strings=on;',
           'SET LOCAL search_path=public,pg_catalog;','SET LOCAL datestyle=ISO,YMD;',CAPTURE,STAGES]
 expected=[]
 for i,row in enumerate(rows):
  declarations='('+row['parameter_types'].replace('?','')+')' if row['parameter_types'] else ''
  bindings='('+','.join(map(literal,row['parameter_values']))+')' if row['parameter_values'] else ''
  execute='EXECUTE values_parameters'+bindings
  forms=[('source',row['sql'])]+([] if canonical is None else [('postgres',canonical[i])])
  wanted_rows=[dict(zip([c['name'] for c in row['output_columns']],values)) for values in row['expected_rows']]
  wanted_metadata=[{'type':c['native_type'],'oid':c['oid'],'collation':NATIVE_COLLATIONS[c['collation']]} for c in row['output_columns']]
  for form,sql in forms:
   key=row['id']+':'+form
   commands+=['PREPARE values_parameters'+declarations+' AS '+question_parameters(sql).strip().removesuffix(';')+';',
    '\\echo values-descriptor:'+key,execute,'\\gdesc','\\echo values-rows:'+key,
    'SELECT pg_temp.values_capture('+sql_literal(execute)+');','DEALLOCATE values_parameters;',
    'PREPARE values_parameters'+declarations+' AS '+question_parameters(metadata_sql(row,sql))+';',
    '\\echo values-metadata:'+key,'SELECT pg_temp.values_capture('+sql_literal(execute)+');','DEALLOCATE values_parameters;']
   expected.append({'kind':'query','key':key,'descriptors':[c['name']+'|'+c['postgres_type'] for c in row['output_columns']],
                    'rows':{'sqlstate':'00000','rows':wanted_rows},'metadata':{'sqlstate':'00000','rows':[{'observed':wanted_metadata}]},'ordered':row['ordered']})
 for i,row in enumerate(boundaries):
  forms=[('source',row['sql'])]
  if boundary_canonical is not None and boundary_canonical[i] is not None:forms.append(('postgres',boundary_canonical[i]))
  for form,sql in forms:
   key=row['id']+':'+form
   commands+=['\\echo values-stages:'+key,'SELECT pg_temp.values_stages('+sql_literal(sql.strip().removesuffix(';'))+');']
   expected.append({'kind':'stages','key':key,'stages':{k:row[k] for k in ('prepare','plan','execute')}})
 commands.append('ROLLBACK;')
 return '\n'.join(commands),expected

def validate_native(stdout,expected):
 lines=stdout.splitlines();offset=0
 assert expected and len({r['key'] for r in expected})==len(expected)
 def take(wanted):
  nonlocal offset
  assert lines[offset:offset+len(wanted)]==wanted,(lines[offset:offset+len(wanted)],wanted)
  offset+=len(wanted)
 def record():
  nonlocal offset
  assert offset<len(lines),'missing native observation'
  result=json.loads(lines[offset],object_pairs_hook=unique_json);offset+=1
  return result
 for item in expected:
  if item['kind']=='stages':
   take(['values-stages:'+item['key']]);actual=record()
   assert frozen(actual)==frozen(item['stages']),(item['key'],actual,item['stages'])
  else:
   take(['values-descriptor:'+item['key'],*item['descriptors'],'values-rows:'+item['key']])
   actual=record();wanted=item['rows']
   assert isinstance(actual,dict) and set(actual)=={'sqlstate','rows'}
   assert actual['sqlstate']=='00000' and isinstance(actual['rows'],list),(item['key'],actual)
   if item['ordered']:assert frozen(actual)==frozen(wanted),(item['key'],actual,wanted)
   else:assert Counter(map(frozen,actual['rows']))==Counter(map(frozen,wanted['rows'])),(item['key'],actual,wanted)
   take(['values-metadata:'+item['key']]);actual=record()
   assert frozen(actual)==frozen(item['metadata']),(item['key'],actual,item['metadata'])
 assert offset==len(lines),('unexpected native observations',lines[offset:])

def main():
 global EXE
 p=argparse.ArgumentParser(description=__doc__);target=p.add_mutually_exclusive_group(required=True)
 target.add_argument('--local-bin');target.add_argument('--dsn');p.add_argument('--psql')
 p.add_argument('--source-only',action='store_true');p.add_argument('--exe',type=Path,default=EXE);args=p.parse_args();EXE=args.exe
 rows=load_cases();boundaries=load_boundaries();canonical=boundary_canonical=None
 if not args.source_only:
  canonical=[];boundary_canonical=[]
  for row in rows:
   validity(row);replay('identity',row['sql'],invoke_fn=render)
   sql=replay('postgres',row['sql'],invoke_fn=render)['sql'];validity(row,sql);canonical.append(sql)
  for row in boundaries:
   validity(row)
   if row['diagnostic']=='input.parse':boundary_canonical.append(None)
   else:
    sql=replay('postgres',row['sql'],invoke_fn=render)['sql'];validity(row,sql);boundary_canonical.append(sql)
 script,expected=native_script(rows,canonical,boundaries,boundary_canonical)
 with connection(args) as psql:
  version=run([*psql,'-X','-At','-c','SHOW server_version']).stdout.strip();assert version.startswith('16.')
  result=run([*psql,'-X','-qAt','-v','ON_ERROR_STOP=1'],input=script,timeout=180)
  validate_native(result.stdout,expected)
 query=[item for item in expected if item['kind']=='query'];stages=[item for item in expected if item['kind']=='stages']
 mode='source-only native preflight; no typed/canonical claim' if args.source_only else 'source/canonical contracts'
 print(f'PASS:50 VALUES fixtures; {mode}; PostgreSQL {version}')
 print(f'PASS:{len(query)} row captures,{len(query)} metadata captures,{sum(len(i["descriptors"]) for i in query)} exact descriptor positions,{len(stages)} separate stage controls')
 print('Scope:finite authored observations; semantic nullability is a conservative declared expectation, not native catalog inference.')
if __name__=='__main__':main()
