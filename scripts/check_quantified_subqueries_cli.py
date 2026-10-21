#!/usr/bin/env python3
"""Static/rendering contracts and finite native quantified-subquery observations."""
import argparse
import hashlib
import json
from pathlib import Path

import check_subqueries_cli as shared
from check_assurance_cli import assert_report
from check_pagination_cli import replay
from check_postgresql_cli import connection, parse_results, run
from check_join_contract_cli import validate_native
from generate_quantified_subquery_examples import all_cases, schema, operator_direction_cases
from generate_quantified_row_subquery_examples import all_cases as row_cases
from check_renderer_corpus import parameters

ROOT = Path(__file__).resolve().parents[1]
FIXTURES = ROOT/'fixtures/quantified_subqueries'


def frozen_json(value):
    return json.dumps(value,sort_keys=True,separators=(',',':'),ensure_ascii=False,allow_nan=False)


def load_cases():
    rows = json.loads((FIXTURES/'synthetic.json').read_text())
    assert frozen_json(rows) == frozen_json(all_cases())
    assert frozen_json(json.loads((FIXTURES/'schema.json').read_text())) == frozen_json(schema())
    row_records=json.loads((FIXTURES/'row_synthetic.json').read_text())
    assert frozen_json(row_records)==frozen_json(row_cases())
    assert len(rows)==len(row_records)==50
    rows += row_records
    assert len(rows) == len({r['id'] for r in rows}) == len({r['sql'] for r in rows}) == 100
    for row in rows:
        assert row['source_kind'] == 'synthetic' and row['factor'] in {'quantified_subquery','quantified_row_subquery'}
        assert row['catalogFile'] == 'fixtures/quantified_subqueries/schema.json'
        assert set(row['expected_rows_by_state']) == set(shared.STATES)
        assert {slot for _,slot in parameters(row['sql'],'postgres')} == set(range(1,len(row['parameter_values'])+1))
        assert all(len(value) == len(row['output_columns']) for state in row['expected_rows_by_state'].values() for value in state)
    return rows


def load_direction_cases():
    rows=json.loads((FIXTURES/'operator_direction.json').read_text())
    assert frozen_json(rows)==frozen_json(operator_direction_cases())
    assert len(rows)==len({r['sql'] for r in rows})==18
    return rows


def boundary_cases():
    # Native expectations were authored before the new typed checker was built.
    cases = [
        ('too-many-columns','SELECT 1 = ANY(SELECT 1,2)','invalid','quantified_subquery_arity','42601'),
        ('finalized-text',"SELECT 1 = ANY(SELECT '1')",'invalid','quantified_subquery_signature','42883'),
        ('finalized-null','SELECT 1 < ALL(SELECT NULL)','invalid','quantified_subquery_signature','42883'),
        ('json-equality',"SELECT '{}'::JSON = ANY(SELECT '{}'::JSON)",'invalid','quantified_subquery_signature','42883'),
        ('array-output-is-not-array-expression','SELECT 1 = ANY(SELECT ARRAY[1])','invalid','quantified_subquery_signature','42883'),
        ('parenthesized-query-is-still-query','SELECT 1 = ANY((SELECT ARRAY[1]))','invalid','quantified_subquery_signature','42883'),
        ('explicit-collation-conflict',"SELECT COALESCE('a' COLLATE \"C\",'a' COLLATE \"POSIX\") = ANY(SELECT 'a')",'invalid','collation_conflict','42P21'),
        ('correlated-child','SELECT 1 = ANY(SELECT q.x) FROM(SELECT 1 AS x)q','unsupported','subquery_correlation','00000'),
        ('row-zero-fields','SELECT ROW() = ANY(SELECT 1)','invalid','quantified_row_subquery_arity','42601'),
        ('row-too-few-columns','SELECT (1,2) < ANY(SELECT 1)','invalid','quantified_row_subquery_arity','42601'),
        ('row-too-many-columns','SELECT ROW(1) = ALL(SELECT 1,2)','invalid','quantified_row_subquery_arity','42601'),
        ('row-finalized-text',"SELECT (1,2) < ALL(SELECT '1',2)",'invalid','quantified_row_subquery_signature','42883'),
        ('row-json-equality',"SELECT ('{}'::JSON,2) = ANY(SELECT '{}'::JSON,2)",'invalid','quantified_row_subquery_signature','42883'),
        ('row-json-ordering',"SELECT ('{}'::JSON,2) < ALL(SELECT '{}'::JSON,2)",'invalid','quantified_row_subquery_signature','42883'),
        ('row-nested-record','SELECT (ROW(1,2),3) = ANY(SELECT ROW(1,2),3)','unsupported','record_value','00000'),
    ]
    return [{'id':name,'source_kind':'synthetic','sql':sql,'status':status,'diagnostic':diagnostic,'prepare':prepare}
            for name,sql,status,diagnostic,prepare in cases]


def boundaries():
    rendered=[]
    for row in boundary_cases():
        for sql in (row['sql'],replay('postgres',row['sql'])['sql']):
            report=assert_report(['--assurance','contract',sql],row['status'],'contract')
            assert report['diagnostic']['code'] == row['diagnostic'], (row['id'],report)
        rendered.append(replay('postgres',row['sql'])['sql'])
    return rendered


def source_checks():
    from extract_quantified_subquery_corpus import reproduce,validate_registry
    manifest=json.loads((FIXTURES/'concrete_sources.json').read_text())
    registry=json.loads((FIXTURES/'source_contracts.json').read_text())
    rows=[json.loads(line) for line in (FIXTURES/'concrete.jsonl').read_text().splitlines()]
    validate_registry(manifest,registry)
    assert frozen_json(rows)==frozen_json(reproduce(manifest))
    assert len(rows)==len({r['id'] for r in rows})==len({r['sql'] for r in rows})==101
    assert manifest['expected_classes']=={'scalar':50,'row':51}
    by_id={row['id']:row for row in rows}
    for row in rows:
        assert row['source_kind']!='synthetic' and row['sql']==row['raw_sql']
        assert hashlib.sha256(row['sql'].encode()).hexdigest()==row['sql_sha256']
        replay('identity',row['sql']);replay('postgres',row['sql'])
    for entry in registry:
        row={**by_id[entry['id']],'output_columns':entry['output_columns']}
        catalog=ROOT/entry['catalogFile'] if entry['catalogFile'] else False
        shared.validity(row,catalog=catalog)
        shared.validity(row,replay('postgres',row['sql'])['sql'],catalog)
    return len(registry),len(rows)


def main():
    parser=argparse.ArgumentParser(description=__doc__)
    target=parser.add_mutually_exclusive_group(required=True)
    target.add_argument('--local-bin');target.add_argument('--dsn')
    parser.add_argument('--psql');parser.add_argument('--source-only',action='store_true')
    parser.add_argument('--source-registry',action='store_true')
    args=parser.parse_args()
    assert not(args.source_only and args.source_registry)
    rows=load_cases()+load_direction_cases();canonical=[]
    for row in rows:
        if args.source_only: canonical.append(row['sql'])
        else:
            shared.validity(row,catalog=FIXTURES/'schema.json')
            replay('identity',row['sql'])
            rendered=replay('postgres',row['sql'])['sql']
            shared.validity(row,rendered,FIXTURES/'schema.json')
            canonical.append(rendered)
    values_sql,values=shared.postgres_script(rows,canonical)
    describe_sql,descriptions=shared.describe_script(rows,canonical)
    guards_sql,guards=shared.prepare_only_script(boundary_cases(),None if args.source_only else boundaries())
    with connection(args) as psql:
        result=run([*psql,'-X','-q','-v','ON_ERROR_STOP=1'],input=values_sql,timeout=180)
        validate_native(parse_results(result.stdout),values)
        result=run([*psql,'-X','-qAt','-v','ON_ERROR_STOP=1'],input=describe_sql,timeout=120)
        assert result.stdout.splitlines()==descriptions
        result=run([*psql,'-X','-qAt','-v','ON_ERROR_STOP=1'],input=guards_sql,timeout=120)
        shared.validate_stages(result.stdout,guards)
        version=run([*psql,'-X','-At','-c','SHOW server_version']).stdout.strip()
        assert version.startswith('16.')
    source_counts=source_checks() if args.source_registry else None
    print(f'PASS:50 scalar + 50 row + 18 direction quantified-query fixtures; PostgreSQL {version}: {len(values)//2} typed rows + {len(values)//2} collation captures, {len(descriptions)} descriptors, {len(guards)} PREPARE controls')
    if source_counts: print(f'PASS:{source_counts[0]} fixed authentic certificates; all {source_counts[1]} unchanged sources rendered, none executed')


if __name__=='__main__':main()
