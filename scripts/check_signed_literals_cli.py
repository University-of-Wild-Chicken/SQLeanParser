#!/usr/bin/env python3
"""Frozen, independently authored PostgreSQL signed-integer regression oracles.

The first 62 descriptors were observed before repairing ASTRA2-001. Expected
values use exact integer arithmetic, never the SQLean checker. Additional cast,
parameter and SubLink barriers keep excluded evaluation errors separate from
static validity. --source-only checks these oracles without invoking SQLean.
"""
import argparse
from collections import Counter
import hashlib
import json
from pathlib import Path
import subprocess

from check_advanced_cli import literal, question_parameters
from check_assurance_cli import PROFILES
from check_postgresql_cli import connection, run, sql_literal
from check_renderer_corpus import replay, unique_json, validate_report

ROOT = Path(__file__).resolve().parents[1]
EXE = ROOT / '.lake/build/bin/sqlean'
FIXTURE = ROOT / 'fixtures/review_regressions/signed_integer.json'
DIGEST = '90e9d8c9e0f82475638fa34035cb04e5bedf028d4a106a633bd9c6385003f3cc'


def canonical_json(value):
    return json.dumps(value, sort_keys=True, separators=(',', ':'))


def load_cases():
    rows = json.loads(FIXTURE.read_text(), object_pairs_hook=unique_json)
    assert hashlib.sha256(canonical_json(rows).encode()).hexdigest() == DIGEST, 'signed literal registry changed'
    assert len(rows) == len({r['id'] for r in rows}) == len({r['sql'] for r in rows}) == 70
    assert Counter(r['execution']['classification'] for r in rows) == {
        'success': 61, 'excluded-runtime-overflow': 8, 'excluded-literal-conversion': 1}
    for row in rows:
        assert row['source_kind'] == 'synthetic' and row['static_status'] == 'valid'
        assert len(row['output_columns']) == 1
        col = row['output_columns'][0]
        assert type(col['nullable']) is bool and col['collation'] is None
        assert len(row['parameter_values']) == len([t for t in row['parameter_types'].split(',') if t])
        execution = row['execution']
        assert execution['sqlstate'] == {
            'success': '00000', 'excluded-runtime-overflow': '22003',
            'excluded-literal-conversion': '22P02'}[execution['classification']]
        assert (execution['rows'] is not None) == (execution['sqlstate'] == '00000')
    return rows


def validate_static(result, row):
    report = json.loads(result.stdout, object_pairs_hook=unique_json)
    assert result.returncode == 0 and isinstance(report, dict), (row['id'], result, report)
    for key, expected in {
        'status': 'valid', 'assurance': 'declarative', 'profile': PROFILES['contract'],
        'evidence': 'declarative-derivation', 'typePrecision': 'exact',
    }.items():
        assert report.get(key) == expected, (row['id'], key, report)
    assert report.get('catalogUnchanged') is True, report
    assert 'diagnostic' not in report and 'sql' not in report, report
    expected = [{k: c[k] for k in ('name', 'type', 'nullable')} for c in row['output_columns']]
    assert report.get('outputColumns') == expected, (row['id'], report, expected)
    assert all(type(c.get('nullable')) is bool for c in report['outputColumns']), report
    assert report.get('outputCollations') == [c['collation'] for c in row['output_columns']], report
    return report


def static_check(row, sql=None):
    args = [str(EXE), '--assurance', 'contract']
    if row['parameter_types']:
        args += ['--param-types', row['parameter_types']]
    result = subprocess.run(args, input=row['sql'] if sql is None else sql,
                            text=True, capture_output=True, timeout=30, check=False, cwd=ROOT)
    return validate_static(result, row)


def render(mode, sql):
    result = subprocess.run([str(EXE), '--render-assurance', mode], input=sql,
                            text=True, capture_output=True, timeout=30, check=False, cwd=ROOT)
    return validate_report(result, mode, sql)


def native_script(rows, canonical):
    assert len(rows) == len(canonical), 'missing canonical signed literal query'
    assert all(row['source_kind'] == 'synthetic' for row in rows), 'only authored SQL may execute'
    assert len({row['id'] for row in rows}) == len(rows), 'duplicate observation identity'
    # RECORD obtains the actual native output. No RETURNS TABLE declaration,
    # guessed casts or replacement literals can coerce the type under review.
    commands = ['BEGIN;', "SET LOCAL statement_timeout='5s';",
                "SET LOCAL standard_conforming_strings=on;", "SET LOCAL search_path=public,pg_catalog;",
                "CREATE FUNCTION pg_temp.signed_capture(command TEXT) RETURNS JSONB LANGUAGE plpgsql AS $$ "
                "DECLARE item RECORD; observed JSONB := '[]'::JSONB; BEGIN "
                "FOR item IN EXECUTE command LOOP observed := observed || jsonb_build_array(to_jsonb(item)); END LOOP; "
                "RETURN jsonb_build_object('sqlstate','00000','rows',observed); "
                "EXCEPTION WHEN OTHERS THEN RETURN jsonb_build_object('sqlstate',SQLSTATE,'rows',NULL); END $$;"]
    expected = []
    for row, rendered in zip(rows, canonical):
        types = row['parameter_types'].replace('?', '')
        declarations = '(' + types + ')' if types else ''
        values = '(' + ','.join(map(literal, row['parameter_values'])) + ')' if row['parameter_values'] else ''
        execute = 'EXECUTE signed_parameters' + values
        for form, sql in (('source', row['sql']), ('postgres', rendered)):
            assert isinstance(sql, str) and sql.strip(), 'empty native query'
            key = row['id'] + ':' + form
            commands += ['\\echo signed-descriptor:' + key,
                         'PREPARE signed_parameters' + declarations + ' AS ' +
                         question_parameters(sql).strip().removesuffix(';') + ';',
                         execute, '\\gdesc',
                         '\\echo signed-execution:' + key,
                         'SELECT pg_temp.signed_capture(' + sql_literal(execute) + ');',
                         'DEALLOCATE signed_parameters;']
            expected.append({'key': key,
                             'descriptors': [c['name'] + '|' + c['postgres_type'] for c in row['output_columns']],
                             'execution': {k: row['execution'][k] for k in ('sqlstate', 'rows')}})
    commands.append('ROLLBACK;')
    return '\n'.join(commands), expected


def validate_native(stdout, expected):
    lines, offset = stdout.splitlines(), 0
    for observation in expected:
        descriptor = ['signed-descriptor:' + observation['key'], *observation['descriptors'],
                      'signed-execution:' + observation['key']]
        assert lines[offset:offset + len(descriptor)] == descriptor, (observation['key'], lines[offset:], descriptor)
        offset += len(descriptor)
        assert offset < len(lines), ('missing execution outcome', observation['key'])
        actual = json.loads(lines[offset], object_pairs_hook=unique_json)
        offset += 1
        wanted = observation['execution']
        assert isinstance(actual, dict) and set(actual) == {'sqlstate', 'rows'}, actual
        assert actual['sqlstate'] == wanted['sqlstate'], (observation['key'], actual, wanted)
        if wanted['rows'] is None:
            assert actual['rows'] is None, (observation['key'], actual)
        else:
            assert isinstance(actual['rows'], list), actual
            # SQL has no ORDER BY here. Preserve multiplicity and exact JSON
            # numeric types while comparing the finite result bag.
            assert Counter(map(canonical_json, actual['rows'])) == Counter(map(canonical_json, wanted['rows'])), (
                observation['key'], actual, wanted)
    assert offset == len(lines), ('unexpected native output', lines[offset:])


def main():
    global EXE
    parser = argparse.ArgumentParser(description=__doc__)
    target = parser.add_mutually_exclusive_group(required=True)
    target.add_argument('--local-bin')
    target.add_argument('--dsn')
    parser.add_argument('--psql')
    parser.add_argument('--exe', type=Path, default=EXE, help='explicit frozen CLI to check')
    parser.add_argument('--source-only', action='store_true', help='native preflight; never invoke the CLI')
    args = parser.parse_args()
    EXE = args.exe
    rows, canonical = load_cases(), []
    for row in rows:
        if args.source_only:
            canonical.append(row['sql'])
        else:
            static_check(row)
            replay('identity', row['sql'], invoke_fn=render)
            sql = replay('postgres', row['sql'], invoke_fn=render)['sql']
            static_check(row, sql)
            canonical.append(sql)
    script, expected = native_script(rows, canonical)
    with connection(args) as psql:
        version = run([*psql, '-X', '-At', '-c', 'SHOW server_version;']).stdout.strip()
        assert version.startswith('16.'), ('PostgreSQL 16 required', version)
        result = run([*psql, '-X', '-qAt', '-v', 'ON_ERROR_STOP=1'], input=script, timeout=120)
        validate_native(result.stdout, expected)
    mode = 'native-only preflight (source duplicated; no CLI claim)' if args.source_only else 'source/canonical certificates'
    print(f'PASS: {len(rows)} authored signed-integer cases; {mode}; PostgreSQL {version}')
    print(f'PASS: {len(expected)} exact descriptors and execution outcomes; 9 excluded evaluation failures per form remain statically valid')
    print('Scope: finite ASTRA2-001 regression evidence; no general PostgreSQL semantics or release approval.')


if __name__ == '__main__':
    main()
