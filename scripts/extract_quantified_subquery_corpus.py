#!/usr/bin/env python3
"""Reproduce whole unchanged quantified-query inputs; never execute SQL.

Offline extraction uses fixed source/selector/license hashes. --oracle also
replays pinned pglast 7.21 raw syntax and lexical observations, not PG16 analysis.
The separate registry fixes conditional static metadata before checker replay.
"""
import argparse
from collections import Counter
import json
from pathlib import Path
import re

from extract_pagination_corpus import checked_file, comparison_key, sha256
from extract_row_in_subquery_corpus import selection
from extract_subquery_corpus import declaration_table

ROOT = Path(__file__).resolve().parents[1]
DIRECTORY = ROOT / 'fixtures/quantified_subqueries'
MANIFEST_SHA256 = '344a22eb5ced8b9de448297c449cc24c35dc6b1021d645a8f15103eaf2a3748c'
SOURCE_REGISTRY_SHA256 = 'dd563a258ab8dd608d4e004d8b92f451e56df2a499215d8f71e6760e0f2f3055'
ORIGINAL_SELECTIONS_SHA256 = '1d681dc55687e84d4a5346534ffebf35fb33122fedc91437c3c76984d6cf0a99'
ORIGINAL_REGISTRY_SHA256 = '373a558b17f343ddc67946a8df6e444c0f66d14de5d5cbed5ef3f120fec3c30f'


def canonical(value):
    return json.dumps(value, sort_keys=True, separators=(',', ':'))


def written_declaration(source, selector):
    keys = {'kind', 'header_start', 'start', 'end'}
    if (set(selector) != keys or selector['kind'] != 'sqllogic_table_declaration'
            or any(type(selector[k]) is not int for k in keys - {'kind'})):
        raise ValueError('invalid declaration selector')
    header, start, end = (selector[k] for k in ('header_start', 'start', 'end'))
    if not 0 <= header < start < end < len(source) or (header and source[header - 1] != '\n'):
        raise ValueError('declaration is not a complete SQLLogicTest input')
    match = re.match(r'statement ok\n(CREATE TABLE[^\n]+)\n\n', source[header:])
    if match is None or (header + match.start(1), header + match.end(1)) != (start, end):
        raise ValueError('declaration is not a complete positive input')
    sql = source[start:end]
    return sql, declaration_table(sql)


def validate_contexts(manifest, data):
    contexts = {c['id']: c for c in manifest['contexts']}
    if len(contexts) != len(manifest['contexts']) or len(contexts) != 4 or len(manifest['catalogs']) != 4:
        raise ValueError('written declaration population changed')
    for context in contexts.values():
        sql, table = written_declaration(data[context['source'], context['source_file']], context['selector'])
        if (sql != context['sql'] or sha256(sql.encode()) != context['sql_sha256']
                or table != context['table']):
            raise ValueError('written declaration bytes or metadata changed')
    catalogs = {}
    for entry in manifest['catalogs']:
        value = json.loads(checked_file(ROOT, entry['local_path'], entry['sha256']))
        ids = entry['context_ids']
        if (value['tables'] != [contexts[id_]['table'] for id_ in ids]
                or value['sourceProvenance']['context_ids'] != ids
                or value['sourceProvenance']['source_sql_executed'] is not False):
            raise ValueError('catalog differs from written declarations')
        catalogs[entry['local_path']] = ids
    for row in manifest['selections'] + manifest['deferred_selections']:
        ids = row['context_ids']
        if not ids:
            if row['candidate_catalog_file'] is not None or row['scope_catalog_columns']:
                raise ValueError('catalog without source declarations')
            continue
        if ids != catalogs[row['candidate_catalog_file']]:
            raise ValueError('candidate uses a different conditional catalog')
        chosen = [contexts[id_] for id_ in ids]
        if any((c['source'], c['source_file']) != (row['source'], row['source_file'])
               or c['selector']['end'] >= row['selector']['start'] for c in chosen):
            raise ValueError('declaration must precede the complete query in the same file')
        if row['scope_catalog_columns'] != {
                c['table']['name']: [f['name'] for f in c['table']['columns']] for c in chosen}:
            raise ValueError('scope inventory differs from written declarations')


def validate_registry(manifest, registry):
    if sha256(canonical(registry).encode()) != SOURCE_REGISTRY_SHA256:
        raise ValueError('preregistered source certificate metadata changed')
    if (len(registry) != 80 or sum(len(r['output_columns']) for r in registry) != 93
            or sha256(canonical(registry[:47]).encode()) != ORIGINAL_REGISTRY_SHA256):
        raise ValueError('fixed certificate population changed')
    selected = {s['id']: s for s in manifest['selections']}
    for entry in registry:
        source = selected[entry['id']]
        obs = source['observation']
        if (set(entry) != {'id', 'catalogFile', 'output_columns'}
                or entry['catalogFile'] != source['candidate_catalog_file']
                or obs['parameters'] or obs['correlated'] or obs['uncertain_scope'] or obs['unresolved_scope']
                or (entry['catalogFile'] is None and not obs['source_free'])):
            raise ValueError('static candidate lacks a complete uncorrelated context')
        if any(set(c) != {'name', 'type', 'nullable', 'collation'} or type(c['nullable']) is not bool
               for c in entry['output_columns']):
            raise ValueError('incomplete expected output descriptor')
    if {e['id'] for e in registry} != {s['id'] for s in selected.values()
                                     if s['assurance_tier'] == 'fixed-static-certificate-candidate'}:
        raise ValueError('static candidate identity set changed')
    return registry


def syntax_observation(sql, catalog):
    from pglast import parser, scan
    from observe_subquery_source import observe, walk
    observation = observe(sql, catalog)  # Enforces the pinned oracle version.
    tree = json.loads(parser.parse_sql_json(sql))
    links = [s for s in walk(tree, 'SubLink')
             if s['subLinkType'] in {'ANY_SUBLINK', 'ALL_SUBLINK'} and s.get('operName')]
    quantified = [{'operator': s['operName'][0]['String']['sval'], 'kind': s['subLinkType'],
                   'left_arity': len(s['testexpr']['RowExpr']['args']) if 'RowExpr' in s.get('testexpr', {}) else 1,
                   'row_left': 'RowExpr' in s.get('testexpr', {})} for s in links]
    encoded = sql.encode()
    tokens = [(t.name, encoded[t.start:t.end + 1].decode()) for t in scan(sql)
              if t.name not in {'SQL_COMMENT', 'C_COMMENT'} and encoded[t.start:t.end + 1] != b';']
    quantifiers = [tokens[i][1].upper() for i in range(len(tokens) - 1)
                  if tokens[i][0] in {'ANY', 'SOME', 'ALL'} and tokens[i + 1][1] == '(']
    digest = sha256(json.dumps([(a, b.lower()) for a, b in tokens], separators=(',', ':')).encode())
    return observation, quantified, quantifiers, digest


def query_class(selection):
    """A whole input containing a row comparison belongs to the row class.

    The selected population has no mixed scalar/row inputs; never count the
    same whole statement twice toward independent class minima.
    """
    kinds = {q['row_left'] for q in selection['quantified_queries']}
    if len(kinds) != 1:
        raise ValueError('mixed or empty quantified query class')
    return 'row' if True in kinds else 'scalar'


def reproduce(manifest, oracle=False, deferred=False):
    if sha256(canonical(manifest).encode()) != MANIFEST_SHA256:
        raise ValueError('closed quantified source manifest changed')
    if sha256(canonical(manifest['selections'][:50]).encode()) != ORIGINAL_SELECTIONS_SHA256:
        raise ValueError('original source population changed')
    all_selections = manifest['selections'] + manifest['deferred_selections']
    if (len({s['id'] for s in all_selections}) != len(all_selections)
            or len({s['normalized_tokens_sha256'] for s in all_selections}) != len(all_selections)):
        raise ValueError('active/deferred source overlap')
    data = {}
    for name, info in manifest['sources'].items():
        if re.fullmatch(r'[0-9a-f]{40}', info['commit']) is None:
            raise ValueError('source revision must be an immutable full pin')
        checked_file(ROOT, info['license_file'], info['license_sha256'])
        for notice in info.get('additional_notices', []):
            checked_file(ROOT, notice['local_path'], notice['sha256'])
        for file in info['files']:
            data[name, file['path']] = checked_file(ROOT, file['local_path'], file['sha256']).decode()
    validate_contexts(manifest, data)
    rows = []
    chosen_population = manifest['deferred_selections'] if deferred else manifest['selections']
    for chosen in chosen_population:
        name, path = chosen['source'], chosen['source_file']
        info = manifest['sources'][name]
        sql, line, detail = selection(data[name, path], chosen['selector'])
        if sha256(sql.encode()) != chosen['sql_sha256']:
            raise ValueError('complete source input bytes changed')
        if not chosen['quantified_queries'] or any(q['operator'] not in {'=', '<>', '<', '<=', '>', '>='}
                                                  for q in chosen['quantified_queries']):
            raise ValueError('missing closed quantified-comparison inventory')
        if oracle and syntax_observation(sql, chosen['scope_catalog_columns']) != (
                chosen['observation'], chosen['quantified_queries'], chosen['quantifiers'], chosen['normalized_tokens_sha256']):
            raise ValueError('raw syntax, dependency or token observation changed')
        rows.append({'id': chosen['id'], 'factor': 'quantified_query', 'query_class': query_class(chosen), 'source': name,
                     'source_kind': info['source_kind'], 'source_file': path,
                     'source_url': f"{info['repository']}/blob/{info['commit']}/{path}#L{line}",
                     'commit': info['commit'], 'license': info['license'], 'line': line,
                     'sql': sql, 'raw_sql': sql, 'sql_sha256': chosen['sql_sha256'], 'transformations': [],
                     'parameter_types': None, 'observed_parameter_slots': chosen['observation']['parameters'],
                     'observed_syntax': chosen['observation'], 'quantified_queries': chosen['quantified_queries'],
                     'quantifiers': chosen['quantifiers'], 'extraction': detail,
                     'source_context_ids': chosen['context_ids'], 'validity_scope': chosen['assurance_tier'],
                     'coverage_gaps': chosen.get('coverage_gaps', []),
                     'scope_claim': 'uncorrelated under fixed declarations' if chosen['assurance_tier'] == 'fixed-static-certificate-candidate'
                         else 'no static scope or catalog claim; conservative observations retained',
                     'source_sql_executed': False})
    expected_count = manifest['expected_deferred_count'] if deferred else manifest['expected_count']
    expected_sources = manifest['expected_deferred_sources'] if deferred else manifest['expected_sources']
    if (len(rows) != expected_count or len({r['id'] for r in rows}) != expected_count
            or len({comparison_key(r['sql'].strip().removesuffix(';')) for r in rows}) != expected_count
            or Counter(r['source'] for r in rows) != expected_sources):
        raise ValueError('closed count, identity or normalized population changed')
    if not deferred:
        classes = Counter(r['query_class'] for r in rows)
        if (classes != manifest['expected_classes'] or manifest['coverage_shortfall'] != {
                k: max(0, n - classes[k]) for k, n in manifest['required_classes'].items()}):
            raise ValueError('class population or honest shortage changed')
    elif any(r['query_class'] != 'row' or not r['coverage_gaps'] for r in rows):
        raise ValueError('deferred syntax gap not explicitly retained')
    return rows


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--check', action='store_true')
    parser.add_argument('--oracle', action='store_true')
    args = parser.parse_args()
    manifest = json.loads((DIRECTORY / 'concrete_sources.json').read_text())
    validate_registry(manifest, json.loads((DIRECTORY / 'source_contracts.json').read_text()))
    for deferred, name in [(False, 'concrete.jsonl'), (True, 'deferred_values.jsonl')]:
        rows = reproduce(manifest, args.oracle, deferred)
        text = ''.join(json.dumps(row, ensure_ascii=False) + '\n' for row in rows)
        path = DIRECTORY / name
        if args.check:
            if path.read_text() != text:
                raise ValueError('saved fixtures differ from whole unchanged source extraction')
        else:
            path.write_text(text)
    print('84 unchanged sources (50 scalar / 34 row); 16-row coverage shortage; '
          '17 VALUES inputs deferred; 80 fixed certificate candidates / 93 columns; '
          'no source SQL or DDL executed')


if __name__ == '__main__':
    main()
