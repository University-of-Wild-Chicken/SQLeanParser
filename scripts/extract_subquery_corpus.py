#!/usr/bin/env python3
"""Reproduce 150 unchanged uncorrelated expression-subquery source witnesses.

Default checks use only the standard library and retained hashed snapshots.
--oracle additionally recomputes conservative syntax observations with pglast
7.21. No mode executes upstream SQL, declarations, expected results or controls.
"""
from __future__ import annotations

import argparse
from collections import Counter
import json
import re
from pathlib import Path

from extract_pagination_corpus import checked_file, comparison_key, sha256
from extract_statement_corpus import selected_sql, statement_spans
from extract_tcl_sql import selected_tcl_sql
from extract_subquery_sqllogic import selected_subquery_sqllogic
from extract_subquery_inputs import go_query, view_body, yaml_query, quidem_query
from check_renderer_corpus import parameters

ROOT = Path(__file__).resolve().parents[1]
DIRECTORY = ROOT / 'fixtures/subqueries'
FACTORS = ('exists', 'scalar', 'in')
# The complete source selection and syntax metadata are closed, not discovered
# by accepting whatever happens to pass a parser/checker on a subsequent run.
MANIFEST_SHA256 = '291ffef3a9326a42ce5b75858bd152ec596f797205c9bcc5f90b3e274230702c'


def canonical(value):
    return json.dumps(value, sort_keys=True, separators=(',', ':'))


SOURCE_REGISTRY_SHA256 = '6f7849b733d871fdc74123f2d32a193571b6849a794f9fda7eec5defce51f792'

def selection(source, selector):
    kind = selector['kind']
    if kind in {'sql_slice', 'go_constant'}:
        return selected_sql(source, selector, statement_spans(source) if kind == 'sql_slice' else [])
    if kind == 'setop_sqllogic_query':
        return selected_subquery_sqllogic(source, selector)
    if kind == 'tcl_sql_statement':
        return selected_tcl_sql(source, selector)
    readers = {'go_query_token': go_query, 'sql_query_body': view_body,
               'yaml_sql_statement': yaml_query, 'whole_query_input': quidem_query}
    if kind not in readers:
        raise ValueError('unknown subquery input selector')
    return readers[kind](source, selector)


def validate_observation(value, factor):
    if (not isinstance(value, dict) or type(value.get('source_free')) is not bool
            or factor not in value.get('factors', {})
            or any(type(n) is not int or n <= 0 for n in value['factors'].values())
            or value.get('correlated') or value.get('uncertain_scope') or value.get('unresolved_scope')):
        raise ValueError('source does not carry the closed noncorrelated syntax evidence')
    if value['source_free'] != (not value['external_relations'] and not value['parameters']):
        raise ValueError('source-free syntax flag contradicts recorded dependencies')
    slots = value['parameters']
    if slots != sorted(set(slots)) or any(type(n) is not int or n < 1 for n in slots):
        raise ValueError('malformed explicit parameter-slot inventory')


def declaration_table(sql):
    match = re.fullmatch(
        r"CREATE (?:TEMP )?TABLE (?:IF NOT EXISTS )?([A-Za-z_][A-Za-z_0-9]*)\s*\(([\s\S]*)\);?",
        sql, re.I)
    if match is None:
        raise ValueError('declaration is outside the finite table-field input grammar')
    body = re.sub(r",\s*PRIMARY KEY \(key, value\)\s*$", "", match[2], flags=re.I)
    columns = []
    for part in body.split(','):
        field = re.fullmatch(r"\s*([A-Za-z_][A-Za-z_0-9]*)\s+(INT|INTEGER|BOOL|BOOLEAN)(\s+NOT NULL)?\s*", part, re.I)
        if field is None:
            raise ValueError('table field has an unregistered type or constraint')
        columns.append({'name': field[1].lower(),
                        'type': 'int' if field[2].upper() in {'INT', 'INTEGER'} else 'bool',
                        'nullable': field[3] is None})
    if len({c['name'] for c in columns}) != len(columns):
        raise ValueError('duplicate declared field')
    return {'name': match[1].lower(), 'columns': columns}


def validate_contexts(manifest, data):
    contexts = {c['id']: c for c in manifest['contexts']}
    if len(contexts) != len(manifest['contexts']):
        raise ValueError('duplicate written declaration identity')
    used = {c for row in manifest['selections'] for c in row.get('context_ids', [])}
    if used != set(contexts):
        raise ValueError('missing or unreferenced declaration context')
    for context in contexts.values():
        text = data[context['source'], context['source_file']]
        a, b = context['start'], context['end']
        if (type(a) is not int or type(b) is not int or not 0 <= a < b <= len(text)
                or text[a:b] != context['sql'] or sha256(text[a:b].encode()) != context['sql_sha256']
                or declaration_table(context['sql']) != context['table']):
            raise ValueError('written declaration bytes or field metadata changed')
        kind = context['input_kind']
        if kind == 'sql-statement-input':
            if (a, b) not in statement_spans(text):
                raise ValueError('declaration is not a whole SQL source statement')
        elif kind == 'sqllogic-statement-input':
            if (not text[:a].endswith('statement ok\n')
                    or not text[b:].startswith('\n\n')):
                raise ValueError('declaration is not a complete SQLLogicTest input')
        elif kind != 'yaml-input':
            raise ValueError('unknown declaration context origin')
    for row in manifest['selections']:
        ids = row.get('context_ids', [])
        if not ids:
            if row.get('scope_catalog_columns'):
                raise ValueError('scope names have no written declaration provenance')
            continue
        chosen = [contexts[i] for i in ids]
        if any((c['source'], c['source_file']) != (row['source'], row['source_file']) for c in chosen):
            raise ValueError('declaration from a different source context')
        columns = {c['table']['name']: [f['name'] for f in c['table']['columns']] for c in chosen}
        if columns != row.get('scope_catalog_columns'):
            raise ValueError('scope field inventory differs from written declarations')
        for c in chosen:
            if c['input_kind'] == 'yaml-input':
                _, _, evidence = selection(data[row['source'], row['source_file']], row['selector'])
                if c['sql'] not in evidence['preceding_inputs'] or not evidence['block_start'] <= c['start'] < c['end'] <= row['selector']['start']:
                    raise ValueError('YAML declaration is not a preceding input of this exact block')
    for entry in manifest['catalogs']:
        value = json.loads(checked_file(ROOT, entry['local_path'], entry['sha256']))
        expected = [contexts[i]['table'] for i in value['sourceProvenance']['context_ids']]
        if (value['tables'] != expected or set(entry['context_ids']) != set(value['sourceProvenance']['context_ids'])
                or value['sourceProvenance']['source_sql_executed'] is not False):
            raise ValueError('conditional catalog differs from its written input declarations')
    return contexts


def reproduce(manifest, oracle=False):
    if sha256(canonical(manifest).encode()) != MANIFEST_SHA256:
        raise ValueError('closed source manifest changed')
    data = {}
    for name, info in manifest['sources'].items():
        checked_file(ROOT, info['license_file'], info['license_sha256'])
        for notice in info.get('additional_notices', []):
            checked_file(ROOT, notice['local_path'], notice['sha256'])
        for file in info['files']:
            data[name, file['path']] = checked_file(ROOT, file['local_path'], file['sha256']).decode()
    validate_contexts(manifest, data)
    result = []
    for chosen in manifest['selections']:
        name, path, factor = (chosen[k] for k in ('source', 'source_file', 'factor'))
        info = manifest['sources'][name]
        sql, line, evidence = selection(data[name, path], chosen['selector'])
        if sha256(sql.encode()) != chosen['sql_sha256']:
            raise ValueError('whole source input bytes changed')
        observation = chosen['observation']
        validate_observation(observation, factor)
        if sorted({index for _, index in parameters(sql, "postgres")}) != observation["parameters"]:
            raise ValueError("source parameter observation changed")
        if oracle:
            from observe_subquery_source import observe
            if observe(sql, chosen.get('scope_catalog_columns')) != observation:
                raise ValueError('raw-tree syntax/dependency observation changed: ' + chosen['id'])
        result.append({
            'id': chosen['id'], 'factor': factor, 'source': name,
            'source_kind': info['source_kind'], 'source_file': path,
            'source_url': f"{info['repository']}/blob/{info['commit']}/{path}#L{line}",
            'commit': info['commit'], 'license': info['license'], 'line': line,
            'sql': sql, 'raw_sql': sql, 'sql_sha256': chosen['sql_sha256'],
            'transformations': [], 'parameter_types': None,
            'observed_parameter_slots': observation['parameters'],
            'observed_syntax': observation, 'extraction': evidence,
            'source_context_ids': chosen.get('context_ids', []),
            'validity_scope': 'explicit fixed source_contracts registry only; other records rendering-only',
            'source_sql_executed': False,
        })
    if len(result) != 150 or len({r['id'] for r in result}) != 150:
        raise ValueError('closed source cardinality/identity changed')
    if len({comparison_key(r['sql']) for r in result}) != 150:
        raise ValueError('duplicate source query text')
    if oracle:
        from pglast import scan
        tokens = [tuple((t.name, row['sql'].encode()[t.start:t.end + 1])
                        for t in scan(row['sql']) if t.name not in {'SQL_COMMENT', 'C_COMMENT'})
                  for row in result]
        if len(set(tokens)) != 150:
            raise ValueError('duplicate source token sequence')
    for factor in FACTORS:
        rows = [r for r in result if r['factor'] == factor]
        if (len(rows) != 50 or Counter(r['source'] for r in rows)
                != manifest['expected_factors'][factor]):
            raise ValueError('per-factor/source inventory changed')
    return result


def validate_registry(manifest, registry):
    if sha256(canonical(registry).encode()) != SOURCE_REGISTRY_SHA256:
        raise ValueError('preregistered source certificate identities or output metadata changed')
    selections = {row['id']: row for row in manifest['selections']}
    counts = {'scalar': (32, 37), 'exists': (22, 23), 'in': (24, 24)}
    if set(registry) != set(counts):
        raise ValueError('source registry factors changed')
    for factor, entries in registry.items():
        if (len(entries), sum(len(e['output_columns']) for e in entries)) != counts[factor]:
            raise ValueError('fixed certificate/column population changed')
        for entry in entries:
            source = selections[entry['id']]
            if (source['factor'] != factor or source['observation']['parameters']
                    or entry['catalogFile'] != source.get('candidate_catalog_file')
                    or any(type(c['nullable']) is not bool for c in entry['output_columns'])):
                raise ValueError('source certificate has an undeclared context or malformed metadata')
            if entry['catalogFile'] is None and not source['observation']['source_free']:
                raise ValueError('catalog-dependent source has no declared certificate context')
    return registry


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--check', action='store_true')
    parser.add_argument('--oracle', action='store_true')
    args = parser.parse_args()
    manifest = json.loads((DIRECTORY / 'concrete_sources.json').read_text())
    validate_registry(manifest, json.loads((DIRECTORY / 'source_contracts.json').read_text()))
    rows = reproduce(manifest, args.oracle)
    for factor in FACTORS:
        text = ''.join(json.dumps(r, ensure_ascii=False) + '\n' for r in rows if r['factor'] == factor)
        path = DIRECTORY / f'{factor}_concrete.jsonl'
        if args.check:
            if path.read_text() != text:
                raise ValueError('source fixture differs from unchanged extraction: ' + factor)
        else:
            path.write_text(text)
    print('150 unchanged expression-subquery sources: 50 EXISTS, 50 scalar, 50 IN; no source SQL executed')


if __name__ == '__main__':
    main()
