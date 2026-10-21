#!/usr/bin/env python3
"""Frozen authored witnesses for ASTRA1-001 array-coercion collation metadata.

Expected types, nullability and identities are independent fixture declarations.
Native gdesc checks exact modifiers; pg_typeof/OID and pg_collation_for observe
the actual input/output expressions without a coercing result declaration.
JSON null is a required indeterminate collation, never an omitted observation.
Only authored SELECTs execute. --source-only never invokes SQLean.
"""
import argparse
from collections import Counter
import hashlib
import json
from pathlib import Path
import subprocess

from check_assurance_cli import PROFILES
from check_postgresql_cli import connection, run
from check_renderer_corpus import replay, unique_json, validate_report

ROOT = Path(__file__).resolve().parents[1]
EXE = ROOT / '.lake/build/bin/sqlean'
FIXTURE = ROOT / 'fixtures/review_regressions/array_coercion_collation.json'
DIGEST = '5132bf0fab20c74e4153fc7542ccc11e0fba247c2c352bc7d897084eba57e4c0'
NATIVE_COLLATIONS = {None: None, 'default': '"default"', 'C': '"C"', 'POSIX': '"POSIX"'}


def canonical_json(value):
    return json.dumps(value, sort_keys=True, separators=(',', ':'))


def load_cases():
    rows = json.loads(FIXTURE.read_text(), object_pairs_hook=unique_json)
    assert hashlib.sha256(canonical_json(rows).encode()).hexdigest() == DIGEST, 'array collation registry changed'
    assert len(rows) == len({r['id'] for r in rows}) == len({r['sql'] for r in rows}) == 181
    assert Counter(r['category'] for r in rows) == {
        'controls': 5, 'cast-matrix': 144, 'raw-array-controls': 16,
        'same-oid': 2, 'composition': 9, 'set': 2, 'null-input': 3}
    for row in rows:
        assert row['source_kind'] == 'synthetic' and row['static_status'] == 'valid'
        assert len(row['output_columns']) == 1 and row['inputs']
        for col in row['output_columns'] + [item['column'] for item in row['inputs']]:
            assert col['name'] == 'v' and type(col['nullable']) is bool
            assert type(col['oid']) is int and col['oid'] > 0
            assert col['collation'] in NATIVE_COLLATIONS
    return rows


def validate_static(result, row):
    report = json.loads(result.stdout, object_pairs_hook=unique_json)
    assert result.returncode == 0 and isinstance(report, dict), (row['id'], result, report)
    expected = [{k: col[k] for k in ('name', 'type', 'nullable')} for col in row['output_columns']]
    assert report.get('outputColumns') == expected, (row['id'], report, expected)
    assert all(type(col.get('nullable')) is bool for col in report['outputColumns']), report
    assert report.get('outputCollations') == [col['collation'] for col in row['output_columns']], (row['id'], report)
    for key, wanted in {
        'status': 'valid', 'assurance': 'declarative', 'profile': PROFILES['contract'],
        'evidence': 'declarative-derivation', 'typePrecision': 'exact',
    }.items():
        assert report.get(key) == wanted, (row['id'], key, report)
    assert report.get('catalogUnchanged') is True and 'diagnostic' not in report, report
    assert 'sql' not in report, report
    return report


def static_check(row, sql=None):
    result = subprocess.run([str(EXE), '--assurance', 'contract'],
                            input=row['sql'] if sql is None else sql,
                            text=True, capture_output=True, timeout=30, check=False, cwd=ROOT)
    return validate_static(result, row)


def render(mode, sql):
    result = subprocess.run([str(EXE), '--render-assurance', mode], input=sql,
                            text=True, capture_output=True, timeout=30, check=False, cwd=ROOT)
    return validate_report(result, mode, sql)


def metadata_query(sql):
    # The observed value is neither cast to a fixture-specified type nor routed
    # through RETURNS TABLE. pg_collation_for is called even for expected NULL.
    return ("SELECT json_build_object('type', pg_typeof(q.v)::TEXT, "
            "'oid', pg_typeof(q.v)::OID::BIGINT, 'collation', pg_collation_for(q.v)) FROM (" +
            sql.strip().removesuffix(';') + ') q LIMIT 1;')


def native_script(rows, canonical=None):
    assert rows and len({row['id'] for row in rows}) == len(rows), 'empty or duplicate observation identity'
    assert all(row['source_kind'] == 'synthetic' for row in rows), 'only authored SQL may execute'
    if canonical is not None:
        assert len(rows) == len(canonical), 'missing canonical array-coercion query'
        assert all(isinstance(sql, str) and sql.strip() for sql in canonical), 'empty canonical query'
    commands = ['BEGIN;', "SET LOCAL statement_timeout='5s';",
                'SET LOCAL standard_conforming_strings=on;', 'SET LOCAL search_path=public,pg_catalog;']
    expected = []
    for index, row in enumerate(rows):
        observations = [(f"{row['id']}:input-{i}", item['sql'], item['column'])
                        for i, item in enumerate(row['inputs'])]
        observations.append((row['id'] + ':source', row['sql'], row['output_columns'][0]))
        if canonical is not None:
            observations.append((row['id'] + ':postgres', canonical[index], row['output_columns'][0]))
        for key, sql, col in observations:
            assert isinstance(sql, str) and sql.strip(), 'empty native query'
            commands += ['\\echo array-descriptor:' + key, sql.strip().removesuffix(';'), '\\gdesc',
                         '\\echo array-metadata:' + key, metadata_query(sql)]
            expected.append({'key': key, 'descriptor': col['name'] + '|' + col['postgres_type'],
                             'metadata': {'type': col['native_type'], 'oid': col['oid'],
                                          'collation': NATIVE_COLLATIONS[col['collation']]}})
    commands.append('ROLLBACK;')
    assert len({item['key'] for item in expected}) == len(expected), 'duplicate native key'
    return '\n'.join(commands), expected


def validate_native(stdout, expected):
    assert expected and len({row['key'] for row in expected}) == len(expected), 'invalid observation registry'
    lines, offset = stdout.splitlines(), 0
    for observation in expected:
        prefix = ['array-descriptor:' + observation['key'], observation['descriptor'],
                  'array-metadata:' + observation['key']]
        assert lines[offset:offset + 3] == prefix, (observation['key'], lines[offset:offset + 3], prefix)
        offset += 3
        assert offset < len(lines), ('missing metadata observation', observation['key'])
        actual = json.loads(lines[offset], object_pairs_hook=unique_json)
        offset += 1
        assert isinstance(actual, dict) and set(actual) == {'type', 'oid', 'collation'}, (observation['key'], actual)
        assert canonical_json(actual) == canonical_json(observation['metadata']), (observation['key'], actual, observation)
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
    rows = load_cases()
    canonical = None if args.source_only else []
    if canonical is not None:
        for row in rows:
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
    mode = 'source-only native preflight; no CLI claim' if args.source_only else 'source/canonical certificates'
    print(f'PASS: {len(rows)} authored array-coercion cases; {mode}; PostgreSQL {version}')
    print(f'PASS: {len(expected)} exact descriptors and type/OID/collation observations, including real JSON null collations')
    print('Scope: finite ASTRA1-001 regression evidence; no general PostgreSQL semantics or release approval.')


if __name__ == '__main__':
    main()
