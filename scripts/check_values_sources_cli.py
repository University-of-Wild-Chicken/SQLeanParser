#!/usr/bin/env python3
"""Check frozen whole VALUES sources using static/rendering reports only.

No source SQL, DDL or expected-result setup executes. No native database tools
are invoked. --inputs-only validates provenance and fixed metadata without a
CLI claim. The 54 internal VALUES-body descriptors are retained, not certified
by this whole-query gate.
"""
import argparse
from collections import Counter
from contextlib import contextmanager
import hashlib
import json
from pathlib import Path
import subprocess

import check_assurance_cli as assurance
import check_renderer_corpus as renderer
import check_subqueries_cli as shared
import extract_values_query_corpus as corpus

ROOT = Path(__file__).resolve().parents[1]
FIXTURES = ROOT / 'fixtures/values_queries'
EXE = ROOT / '.lake/build/bin/sqlean'
EXPECTED_CONTRACT_PROFILE = 'sqlean-basic-select-v0.36'
SOURCE_MANIFEST_SHA256 = 'cce4b0b252bdb0216e380be9b92542fb05564140854d1e72b14adfe9a2dd6106'
SOURCE_REGISTRY_SHA256 = '0d220fed00761035100956d5067d85b5a849de59a8971ed3d8bf254f74ce13dd'
COLLATIONS = {None, 'default', 'C', 'POSIX'}
STATIC_KEYS = {'status', 'assurance', 'profile', 'evidence', 'catalogUnchanged',
               'typePrecision', 'outputColumns', 'outputCollations'}
RENDER_KEYS = {'status', 'assurance', 'profile', 'mode', 'evidence', 'rendererVersion',
               'semanticPreservation', 'scope', 'assumptions', 'trustedFoundations',
               'sql', 'parameterMap', 'theorems'}
PHASES = ('source-static', 'identity-render', 'identity-replay', 'identity-static',
          'postgres-render', 'postgres-replay', 'postgres-static')


def frozen(value):
    return json.dumps(value, sort_keys=True, separators=(',', ':'), ensure_ascii=False, allow_nan=False)


def digest(value):
    return hashlib.sha256(corpus.canonical(value).encode()).hexdigest()


def reject_constant(value):
    raise ValueError('nonfinite JSON constant: ' + value)


def strict_json(text):
    return json.loads(text, object_pairs_hook=renderer.unique_json, parse_constant=reject_constant)


def load_sources():
    manifest = strict_json((FIXTURES / 'concrete_sources.json').read_text())
    registry = strict_json((FIXTURES / 'source_contracts.json').read_text())
    rows = [strict_json(line) for line in (FIXTURES / 'concrete.jsonl').read_text().splitlines()]
    assert digest(manifest) == SOURCE_MANIFEST_SHA256, 'fixed VALUES source provenance changed'
    assert digest(registry) == SOURCE_REGISTRY_SHA256, 'fixed VALUES source metadata changed'
    corpus.validate_registry(manifest, registry)
    assert frozen(rows) == frozen(corpus.reproduce(manifest)), 'source records differ from unchanged whole-input extraction'
    assert len(rows) == len({r['id'] for r in rows}) == len({r['sql'] for r in rows}) == 50
    assert len(registry) == len({r['id'] for r in registry}) == 50
    assert sum(len(r['output_columns']) for r in registry) == 65
    assert Counter(r['query_class'] for r in rows) == {'standalone-values': 7, 'select-containing-values': 43}
    assert Counter(r['source'] for r in rows) == {'postgres': 9, 'duckdb': 41}
    assert [r['id'] for r in rows] == [r['id'] for r in registry], 'registry order/identity mismatch'
    paired = []
    for source, entry in zip(rows, registry):
        assert set(entry) == {'id', 'catalogFile', 'output_columns'}
        assert entry['catalogFile'] is None, 'all registered sources require the empty catalog'
        assert source['source_kind'] != 'synthetic' and source['factor'] == 'values_query'
        assert source['sql'] == source['raw_sql'] and source['transformations'] == []
        assert hashlib.sha256(source['sql'].encode()).hexdigest() == source['sql_sha256']
        assert source['source_sql_executed'] is False and source['parameter_types'] is None
        assert source['observed_parameter_slots'] == [] and renderer.parameters(source['sql'], 'postgres') == []
        for column in entry['output_columns']:
            assert set(column) == {'name', 'type', 'nullable', 'collation'}
            assert type(column['name']) is str and type(column['type']) is str and column['type']
            assert type(column['nullable']) is bool
            assert column['collation'] is None or type(column['collation']) is str
            assert column['collation'] in COLLATIONS
        paired.append((source, entry))
    return paired


def validate_static(report, row):
    assert type(report) is dict and set(report) == STATIC_KEYS, (row['id'], report)
    for key, wanted in {'status': 'valid', 'assurance': 'declarative',
                        'profile': EXPECTED_CONTRACT_PROFILE, 'evidence': 'declarative-derivation',
                        'typePrecision': 'exact'}.items():
        assert report[key] == wanted, (row['id'], key, report)
    assert report['catalogUnchanged'] is True, (row['id'], report)
    columns = report['outputColumns']
    assert type(columns) is list and all(type(c) is dict and set(c) == {'name', 'type', 'nullable'} for c in columns)
    assert all(type(c['name']) is str and type(c['type']) is str and type(c['nullable']) is bool for c in columns)
    wanted = [{k: c[k] for k in ('name', 'type', 'nullable')} for c in row['output_columns']]
    assert frozen(columns) == frozen(wanted), (row['id'], columns, wanted)
    assert type(report['outputCollations']) is list
    assert all(c is None or type(c) is str for c in report['outputCollations'])
    assert frozen(report['outputCollations']) == frozen([c['collation'] for c in row['output_columns']]), (row['id'], report)
    return report


def invoke(args, sql):
    # This sole process boundary admits only the two SQLean analysis/report
    # operations. SQL is stdin data, never a shell command or database request.
    assert args in (['--assurance', 'contract'], ['--render-assurance', 'identity'],
                    ['--render-assurance', 'postgres']), 'only inert SQLean source checks are allowed'
    assert type(sql) is str and sql.strip()
    result = subprocess.run([str(EXE), *args], input=sql, cwd=ROOT,
                            text=True, capture_output=True, check=False, timeout=30)
    assert type(result.returncode) is int and result.returncode == 0, (args, result.returncode, result.stdout, result.stderr)
    assert result.stderr == '', (args, result.stderr)
    report = strict_json(result.stdout)
    assert type(report) is dict, 'expected exactly one JSON report object'
    return result, report


@contextmanager
def shared_static_transport():
    """Keep shared.validity(catalog=False), with strict JSON at its boundary.

    The shared helper calls assurance.invoke through assert_report. This local,
    exception-safe replacement preserves its validation and forbids a schema or
    parameter argument. No global helper files or profile oracles are changed.
    """
    previous = assurance.invoke
    def strict_invoke(args, *, stdin=None):
        assert stdin is None and len(args) == 3 and args[:2] == ['--assurance', 'contract'], 'source must use empty catalog and no parameter declarations'
        result, _ = invoke(args[:2], args[2])
        return result
    assurance.invoke = strict_invoke
    try:
        yield
    finally:
        assurance.invoke = previous


def validity(row, sql):
    assert row.get('parameter_types') is None and row['observed_parameter_slots'] == []
    with shared_static_transport():
        report = shared.validity(row, sql=sql, catalog=False)
    return validate_static(report, row)


def render(mode, sql):
    result, report = invoke(['--render-assurance', mode], sql)
    assert set(report) == RENDER_KEYS, report
    for key in ('theorems', 'trustedFoundations', 'assumptions'):
        assert type(report[key]) is list and all(type(v) is str for v in report[key])
        assert len(report[key]) == len(set(report[key])), ('duplicate renderer evidence', key)
    assert report['parameterMap'] == [], 'closed VALUES sources cannot acquire parameter bindings'
    renderer.validate_report(result, mode, sql)
    return report


def validate_observations(pairs, observations):
    """Check exact source/phase order; no dropped or reordered canonical cases."""
    expected = [(source['id'], phase) for source, _ in pairs for phase in PHASES]
    assert len(pairs) == 50 and len({s['id'] for s, _ in pairs}) == 50
    assert len(observations) == 350
    assert [(o['id'], o['phase']) for o in observations] == expected, 'missing, extra, duplicate or reordered source/canonical observation'
    for index, (source, entry) in enumerate(pairs):
        group = observations[index * 7:(index + 1) * 7]
        assert all(set(o) == {'id', 'phase', 'sql', 'source_sha256', 'column_count'} for o in group)
        assert all(o['source_sha256'] == source['sql_sha256'] for o in group)
        assert group[0]['sql'] == source['sql'], 'original query was changed'
        assert all(type(o['sql']) is str and o['sql'].strip() for o in group), 'canonical SQL omitted'
        for begin in (1, 4):
            assert group[begin]['sql'] == group[begin + 1]['sql'] == group[begin + 2]['sql'], 'canonical SQL changed or static check did not use canonical input'
        assert all(type(o['column_count']) is int and o['column_count'] ==
                   (len(entry['output_columns']) if o['phase'].endswith('-static') else 0) for o in group)
    return {'source_count': 50, 'static_reports': 150, 'static_column_positions': 195,
            'render_reports': 200, 'canonical_forms': 100, 'internal_values_bodies_checked': 0,
            'source_sql_executed': False, 'contract_profile': EXPECTED_CONTRACT_PROFILE}


def source_checks():
    pairs = load_sources()
    # Integration must advance the shared profile with the actual v36 core.
    assert assurance.PROFILES['contract'] == EXPECTED_CONTRACT_PROFILE, 'shared contract profile is not the required v0.36; no oracle downgrade allowed'
    observations = []
    for source, entry in pairs:
        row = {**source, 'output_columns': entry['output_columns']}
        def record(phase, sql):
            observations.append({'id': source['id'], 'phase': phase, 'sql': sql,
                                 'source_sha256': source['sql_sha256'],
                                 'column_count': len(entry['output_columns']) if phase.endswith('-static') else 0})
        validity(row, source['sql'])
        record('source-static', source['sql'])
        for mode in ('identity', 'postgres'):
            report = render(mode, source['sql'])
            canonical = report['sql']
            record(mode + '-render', canonical)
            replay = render(mode, canonical)
            assert replay['sql'] == canonical and replay['parameterMap'] == [], (source['id'], mode, 'canonical replay changed')
            record(mode + '-replay', replay['sql'])
            validity(row, canonical)
            record(mode + '-static', canonical)
    return validate_observations(pairs, observations)


def main():
    global EXE
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--exe', type=Path, default=EXE)
    parser.add_argument('--inputs-only', action='store_true')
    args = parser.parse_args()
    EXE = args.exe
    if args.inputs_only:
        load_sources()
        print('PASS: 50 immutable whole VALUES sources / 65 preregistered output columns; inputs only, no CLI or native claim')
        return
    summary = source_checks()
    print('PASS: 50 whole VALUES sources; 150 exact static reports / 195 ordered column positions; 200 identity/PostgreSQL renderer reports / 100 canonical forms')
    print('Scope: original and canonical whole-query metadata only; 54 internal VALUES-body descriptors are not separately certified; no source SQL or DDL executed')
    print(frozen(summary))


if __name__ == '__main__':
    main()
