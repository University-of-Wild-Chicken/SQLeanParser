#!/usr/bin/env python3
"""Exact static/render checks and finite authored row-IN native observations."""
import argparse
import hashlib
import json
from pathlib import Path

import check_subqueries_cli as shared
from check_assurance_cli import assert_report
from check_pagination_cli import replay
from check_postgresql_cli import connection, parse_results, run
from check_join_contract_cli import validate_native
from generate_row_in_subquery_examples import all_cases, schema
from check_renderer_corpus import parameters

ROOT = Path(__file__).resolve().parents[1]
FIXTURES = ROOT / 'fixtures/row_in_subqueries'


def frozen_json(value):
    return json.dumps(value, sort_keys=True, separators=(',', ':'), ensure_ascii=False, allow_nan=False)


def load_cases():
    rows = json.loads((FIXTURES / 'synthetic.json').read_text())
    assert frozen_json(rows) == frozen_json(all_cases())
    assert frozen_json(json.loads((FIXTURES / 'schema.json').read_text())) == frozen_json(schema())
    assert len(rows) == len({r['id'] for r in rows}) == len({r['sql'] for r in rows}) == 50
    for row in rows:
        assert row['source_kind'] == 'synthetic' and row['factor'] == 'row_in_subquery'
        assert row['catalogFile'] == 'fixtures/row_in_subqueries/schema.json'
        assert set(row['expected_rows_by_state']) == set(shared.STATES)
        slots = {index for _, index in parameters(row['sql'], 'postgres')}
        assert slots == set(range(1,len(row['parameter_values'])+1))
        assert all(len(values) == len(row['output_columns']) for rows_ in row['expected_rows_by_state'].values() for values in rows_)
    return rows


def boundary_cases():
    values = [
        ('zero-fields', 'SELECT ROW() IN(SELECT 1)', 'invalid', 'in_row_subquery_arity', '42601'),
        ('too-few-columns', 'SELECT (1,2) IN(SELECT 1)', 'invalid', 'in_row_subquery_arity', '42601'),
        ('too-many-columns', 'SELECT ROW(1) IN(SELECT 1,2)', 'invalid', 'in_row_subquery_arity', '42601'),
        ('finalized-text', "SELECT (1,2) IN(SELECT '1',2)", 'invalid', 'in_row_subquery_signature', '42883'),
        ('finalized-null', 'SELECT (1,2) IN(SELECT NULL,2)', 'invalid', 'in_row_subquery_signature', '42883'),
        ('boolean-integer', 'SELECT (TRUE,2) IN(SELECT 1,2)', 'invalid', 'in_row_subquery_signature', '42883'),
        ('json-missing-equality', "SELECT ('{}'::JSON,2) IN(SELECT '{}'::JSON,2)", 'invalid', 'in_row_subquery_signature', '42883'),
        ('left-explicit-conflict', "SELECT (COALESCE('a' COLLATE \"C\",'a' COLLATE \"POSIX\"),2) IN(SELECT 'a',2)", 'invalid', 'collation_conflict', '42P21'),
        ('child-explicit-conflict', "SELECT ('a',2) IN(SELECT COALESCE('a' COLLATE \"C\",'a' COLLATE \"POSIX\"),2)", 'invalid', 'collation_conflict', '42P21'),
        ('correlated-child', 'SELECT (1,2) IN(SELECT q.a,2) FROM (SELECT 1 AS a) q', 'unsupported', 'subquery_correlation', '00000'),
        ('nested-record-field', 'SELECT (ROW(1,2),3) IN(SELECT ROW(1,2),3)', 'unsupported', 'record_value', '00000'),
    ]
    return [{'id':id_, 'sql':sql, 'source_kind':'synthetic', 'status':status,
             'diagnostic':diagnostic, 'prepare':prepare} for id_,sql,status,diagnostic,prepare in values]


def boundaries():
    rendered = []
    for row in boundary_cases():
        report = assert_report(['--assurance','contract',row['sql']], row['status'],'contract')
        assert report['diagnostic']['code'] == row['diagnostic'], (row['id'],report)
        rendered.append(replay('postgres',row['sql'])['sql'])
    return rendered


def source_checks():
    from extract_row_in_subquery_corpus import reproduce, validate_registry
    rows = [json.loads(line) for line in (FIXTURES/'concrete.jsonl').read_text().splitlines()]
    registry = json.loads((FIXTURES/'source_contracts.json').read_text())
    manifest = json.loads((FIXTURES/'concrete_sources.json').read_text())
    validate_registry(manifest, registry)
    assert frozen_json(rows) == frozen_json(reproduce(manifest)), 'source inputs differ from closed unchanged extraction'
    assert len(rows) == len({r['id'] for r in rows}) == len({r['sql'] for r in rows}) == 50
    by_id = {r['id']:r for r in rows}
    assert len({r['id'] for r in registry}) == len(registry)
    for row in rows:
        assert row['source_kind'] != 'synthetic' and row['sql'] == row['raw_sql']
        assert hashlib.sha256(row['sql'].encode()).hexdigest() == row['sql_sha256']
        replay('identity',row['sql']); replay('postgres',row['sql'])
    for record in registry:
        source = by_id[record['id']]
        row = {**source, 'output_columns':record['output_columns']}
        catalog = ROOT/record['catalogFile'] if record['catalogFile'] else False
        shared.validity(row,catalog=catalog)
        canonical = replay('postgres',row['sql'])['sql']
        shared.validity(row,canonical,catalog)
    return len(registry),len(rows)


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    target = parser.add_mutually_exclusive_group(required=True)
    target.add_argument('--local-bin'); target.add_argument('--dsn')
    parser.add_argument('--psql'); parser.add_argument('--source-only',action='store_true')
    parser.add_argument('--source-registry',action='store_true')
    args = parser.parse_args()
    assert not(args.source_only and args.source_registry)
    rows = load_cases()
    canonical = []
    for row in rows:
        if args.source_only:
            canonical.append(row['sql'])
        else:
            shared.validity(row,catalog=FIXTURES/'schema.json')
            replay('identity',row['sql'])
            rendered = replay('postgres',row['sql'])['sql']
            shared.validity(row,rendered,FIXTURES/'schema.json')
            canonical.append(rendered)
    selected = [{**r,'sqlite_sql':r['sql'], 'sqlite_expected_rows_by_state':r['expected_rows_by_state']}
                for r in rows if r['sqlite_supported']]
    sqlite_canonical = [r['sqlite_sql'] if args.source_only else replay('sqlite',r['sqlite_sql'])['sql'] for r in selected]
    sqlite_count = shared.sqlite_observations(selected,sqlite_canonical)
    values_sql,values = shared.postgres_script(rows,canonical)
    describe_sql,descriptions = shared.describe_script(rows,canonical)
    guards_sql,guards = shared.prepare_only_script(boundary_cases(),None if args.source_only else boundaries())
    with connection(args) as psql:
        result = run([*psql,'-X','-q','-v','ON_ERROR_STOP=1'],input=values_sql,timeout=180)
        validate_native(parse_results(result.stdout),values)
        result = run([*psql,'-X','-qAt','-v','ON_ERROR_STOP=1'],input=describe_sql,timeout=120)
        assert result.stdout.splitlines() == descriptions
        result = run([*psql,'-X','-qAt','-v','ON_ERROR_STOP=1'],input=guards_sql,timeout=120)
        shared.validate_stages(result.stdout,guards)
        version = run([*psql,'-X','-At','-c','SHOW server_version']).stdout.strip()
        assert version.startswith('16.')
    source_counts = source_checks() if args.source_registry else None
    print(f'PASS:50 authored row-IN queries; PostgreSQL {version}: {len(values)//2} typed rows + {len(values)//2} collation captures, {len(descriptions)} descriptor positions, {len(guards)} PREPARE controls')
    print(f'PASS: {sqlite_count} authored SQLite source/canonical row and label observations')
    if source_counts:
        print(f'PASS: {source_counts[0]} fixed authentic certificates; all {source_counts[1]} unchanged sources rendered, none executed')


if __name__ == '__main__':
    main()
