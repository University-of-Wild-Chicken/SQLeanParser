#!/usr/bin/env python3
"""Reproduce 50 unchanged row-IN source inputs without executing source SQL.

The default is offline and standard-library only. --oracle additionally checks
pinned pglast syntax observations and token identity, never native execution.
Only source_contracts.json fixes candidate static certificates; rendering-only
records do not assert uncorrelated scope, catalog completeness or static validity.
"""
from __future__ import annotations

import argparse
from collections import Counter
import json
import re
from pathlib import Path

from extract_pagination_corpus import checked_file, comparison_key, sha256
from extract_subquery_corpus import selection as legacy_selection
from extract_subquery_inputs import complete_select
from extract_tcl_sql import COMMAND, block_end
from extract_statement_corpus import statement_spans

ROOT = Path(__file__).resolve().parents[1]
DIRECTORY = ROOT / 'fixtures/row_in_subqueries'
MANIFEST_SHA256 = '4cd2b65eed83f1f62640f969e1e9c491b1c05a1cb0eb94f7ab64717d4fcc19aa'
SOURCE_REGISTRY_SHA256 = '39d9f324cefb1dd4a90e1df76e778645891b00e6a8860e06eff1a872f7929ee5'


def canonical(value):
    return json.dumps(value, sort_keys=True, separators=(',', ':'))


def whole_tcl_argument(source, selector):
    keys = {'kind', 'command_start', 'block_start', 'block_end'}
    if (set(selector) != keys or selector['kind'] != 'whole_tcl_sql_argument'
            or any(type(selector[k]) is not int for k in keys - {'kind'})):
        raise ValueError('invalid whole Tcl SQL argument selector')
    pos, start, end = (selector[k] for k in ('command_start', 'block_start', 'block_end'))
    if not 0 <= pos < len(source) or (pos and source[pos - 1] != '\n'):
        raise ValueError('Tcl command must begin on its complete source line')
    command = COMMAND.match(source, pos)
    if command is None or command['command'] not in {'do_execsql_test', 'execsql'}:
        raise ValueError('whole argument is not a positive SQL input command')
    args = command['arguments'].strip()
    if command['command'] == 'execsql':
        if args:
            raise ValueError('execsql argument assembly is outside this reader')
    elif not re.fullmatch(r'[^\s{}"\\;\[\]]+', args):
        raise ValueError('test name must be one simple source token')
    if command.end() != start or block_end(source, start - 1) != end:
        raise ValueError('selection is not the complete literal Tcl SQL argument')
    if end + 1 < len(source) and not source[end + 1].isspace():
        raise ValueError('literal argument has no complete word boundary')
    sql = source[start:end]
    if re.search(r'\\\r?\n', sql):
        raise ValueError('Tcl backslash-newline substitution changes SQL bytes')
    complete_select(sql)
    return sql, source.count('\n', 0, start) + 1, {
        'extraction': 'whole literal positive Tcl SQL argument',
        'command_start': pos, 'source_start': start, 'source_end': end,
        'tcl_command': command['command'], 'controls_executed': False,
    }


def selection(source, selector):
    if selector['kind'] == 'whole_tcl_sql_argument':
        return whole_tcl_argument(source, selector)
    if selector['kind'] == 'quidem_complete_query_input':
        if (set(selector) != {'kind', 'start', 'end'}
                or any(type(selector[k]) is not int for k in ('start', 'end'))):
            raise ValueError('invalid Quidem complete query selector')
        a, b = selector['start'], selector['end']
        if not 0 <= a < b < len(source) or (a and source[a - 1] != '\n') or source[b] != '\n':
            raise ValueError('Quidem query must have complete line boundaries')
        before = source[:a].splitlines()
        if before and before[-1].strip() and not before[-1].startswith('#'):
            raise ValueError('selection starts inside an earlier Quidem input')
        sql = source[a:b]
        if statement_spans(sql) != [(0, len(sql))]:
            raise ValueError('Quidem selection must be exactly one terminated input')
        complete_select(sql)
        return sql, source.count('\n', 0, a) + 1, {
            'extraction': 'complete terminated Quidem SQL input',
            'source_start': a, 'source_end': b, 'controls_executed': False,
        }
    return legacy_selection(source, selector)


def declaration_table(sql):
    """Finite transcription of the six retained written table declarations."""
    match = re.fullmatch(r'CREATE (?:TEMP )?TABLE ([A-Za-z_][A-Za-z_0-9]*)\s*\(([\s\S]*)\);?', sql, re.I)
    if match is None:
        raise ValueError('unregistered table declaration grammar')
    columns, collations = [], []
    for part in match[2].split(','):
        field = re.fullmatch(r'\s*([A-Za-z_][A-Za-z_0-9]*)\s+(INT|INTEGER|INT4|INT8|FLOAT|TEXT)(?:\s+(PRIMARY KEY|NOT NULL|COLLATE "(?:C|POSIX)"))?\s*', part, re.I)
        if field is None:
            raise ValueError('unregistered field declaration grammar')
        name, type_, constraint = field[1].lower(), field[2].upper(), field[3] or ''
        base = {'INT': 'int', 'INTEGER': 'int', 'INT4': 'int', 'INT8': 'bigint', 'FLOAT': 'double', 'TEXT': 'text'}[type_]
        columns.append({'name': name, 'type': base, 'nullable': constraint.upper() not in {'PRIMARY KEY', 'NOT NULL'}})
        if constraint.upper().startswith('COLLATE'):
            collations.append({'column': name, 'collation': constraint.split('"')[1]})
    if len({c['name'] for c in columns}) != len(columns):
        raise ValueError('duplicate table field')
    table = {'name': match[1].lower(), 'columns': columns}
    if collations:
        table['columnCollations'] = collations
    return table


def validate_contexts(manifest, data):
    contexts = {c['id']: c for c in manifest['contexts']}
    if len(contexts) != 6 or len(manifest['catalogs']) != 5:
        raise ValueError('written declaration inventory changed')
    for context in contexts.values():
        text = data[context['source'], context['source_file']]
        a, b = context['start'], context['end']
        if (type(a) is not int or type(b) is not int or not 0 <= a < b <= len(text)
                or text[a:b] != context['sql'] or sha256(text[a:b].encode()) != context['sql_sha256']
                or declaration_table(context['sql']) != context['table']):
            raise ValueError('written declaration bytes or metadata changed')
    catalog_contexts = {}
    for entry in manifest['catalogs']:
        value = json.loads(checked_file(ROOT, entry['local_path'], entry['sha256']))
        ids = entry['context_ids']
        if (value['tables'] != [contexts[i]['table'] for i in ids]
                or value['sourceProvenance']['context_ids'] != ids
                or value['sourceProvenance']['source_sql_executed'] is not False):
            raise ValueError('conditional catalog differs from written declarations')
        catalog_contexts[entry['local_path']] = ids
    for row in manifest['selections']:
        ids = row.get('context_ids', [])
        if not ids:
            continue
        if ids != catalog_contexts[row['candidate_catalog_file']]:
            raise ValueError('candidate uses a different declaration catalog')
        chosen = [contexts[i] for i in ids]
        if any((c['source'], c['source_file']) != (row['source'], row['source_file'])
               or c['end'] > row['selector'].get('start', len(data[row['source'], row['source_file']])) for c in chosen):
            raise ValueError('declaration is not a preceding input in this source')
        if row['scope_catalog_columns'] != {c['table']['name']: [f['name'] for f in c['table']['columns']] for c in chosen}:
            raise ValueError('scope field inventory differs from written declarations')


def validate_registry(manifest, registry):
    if sha256(canonical(registry).encode()) != SOURCE_REGISTRY_SHA256:
        raise ValueError('preregistered source certificate metadata changed')
    if len(registry) != 12 or sum(len(e['output_columns']) for e in registry) != 20:
        raise ValueError('fixed certificate population changed')
    selected = {s['id']: s for s in manifest['selections']}
    for entry in registry:
        source = selected[entry['id']]
        observation = source['observation']
        if (set(entry) != {'id', 'catalogFile', 'output_columns'}
                or entry['catalogFile'] != source['candidate_catalog_file']
                or observation['parameters'] or observation['correlated']
                or observation['uncertain_scope'] or observation['unresolved_scope']
                or (entry['catalogFile'] is None and not observation['source_free'])):
            raise ValueError('candidate has no complete uncorrelated fixed context')
    if {e['id'] for e in registry} != {s['id'] for s in selected.values() if s['assurance_tier'] == 'fixed-static-certificate-candidate'}:
        raise ValueError('fixed certificate identities changed')
    return registry


def reproduce(manifest, oracle=False):
    if sha256(canonical(manifest).encode()) != MANIFEST_SHA256:
        raise ValueError('closed row-IN source manifest changed')
    data = {}
    for name, info in manifest['sources'].items():
        if re.fullmatch(r'[0-9a-f]{40}', info['commit']) is None:
            raise ValueError('source revision must be a full immutable pin')
        checked_file(ROOT, info['license_file'], info['license_sha256'])
        for notice in info.get('additional_notices', []):
            checked_file(ROOT, notice['local_path'], notice['sha256'])
        for file in info['files']:
            data[name, file['path']] = checked_file(ROOT, file['local_path'], file['sha256']).decode()
    validate_contexts(manifest, data)
    result = []
    for chosen in manifest['selections']:
        name, path = chosen['source'], chosen['source_file']
        info = manifest['sources'][name]
        sql, line, evidence = selection(data[name, path], chosen['selector'])
        if sha256(sql.encode()) != chosen['sql_sha256']:
            raise ValueError('complete source input bytes changed')
        if not chosen['row_in_arities'] or any(type(n) is not int or n < 2 for n in chosen['row_in_arities']):
            raise ValueError('missing positive row-valued IN syntax inventory')
        if oracle:
            from observe_subquery_source import observe, walk
            from pglast import parser, scan
            observation = observe(sql, chosen.get('scope_catalog_columns'))
            tree = json.loads(parser.parse_sql_json(sql))
            arities = [len(s['testexpr']['RowExpr']['args']) for s in walk(tree, 'SubLink') if s['subLinkType'] == 'ANY_SUBLINK' and not s.get('operName') and 'RowExpr' in s.get('testexpr', {})]
            tokens = [(t.name, sql.encode()[t.start:t.end + 1].decode()) for t in scan(sql) if t.name not in {'SQL_COMMENT', 'C_COMMENT'}]
            if (observation != chosen['observation'] or arities != chosen['row_in_arities']
                    or sha256(json.dumps(tokens, separators=(',', ':')).encode()) != chosen['normalized_tokens_sha256']):
                raise ValueError('raw syntax/dependency/token observation changed')
        result.append({
            'id': chosen['id'], 'factor': 'row_in', 'source': name,
            'source_kind': info['source_kind'], 'source_file': path,
            'source_url': f"{info['repository']}/blob/{info['commit']}/{path}#L{line}",
            'commit': info['commit'], 'license': info['license'], 'line': line,
            'sql': sql, 'raw_sql': sql, 'sql_sha256': chosen['sql_sha256'],
            'transformations': [], 'parameter_types': None,
            'observed_parameter_slots': chosen['observation']['parameters'],
            'observed_syntax': chosen['observation'], 'row_in_arities': chosen['row_in_arities'],
            'extraction': evidence, 'source_context_ids': chosen.get('context_ids', []),
            'validity_scope': chosen['assurance_tier'],
            'scope_claim': 'uncorrelated under fixed declarations' if chosen['assurance_tier'] == 'fixed-static-certificate-candidate' else 'no static scope or catalog claim; conservative observations retained',
            'source_sql_executed': False,
        })
    if (len(result) != 50 or len({r['id'] for r in result}) != 50
            or len({comparison_key(r['sql']) for r in result}) != 50
            or len({s['normalized_tokens_sha256'] for s in manifest['selections']}) != 50
            or Counter(r['source'] for r in result) != manifest['expected_sources']):
        raise ValueError('closed count, identity or normalized source population changed')
    return result


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--check', action='store_true')
    parser.add_argument('--oracle', action='store_true')
    args = parser.parse_args()
    manifest = json.loads((DIRECTORY / 'concrete_sources.json').read_text())
    validate_registry(manifest, json.loads((DIRECTORY / 'source_contracts.json').read_text()))
    rows = reproduce(manifest, args.oracle)
    text = ''.join(json.dumps(row, ensure_ascii=False) + '\n' for row in rows)
    path = DIRECTORY / 'concrete.jsonl'
    if args.check:
        if path.read_text() != text:
            raise ValueError('saved source fixtures differ from complete unchanged extraction')
    else:
        path.write_text(text)
    print('50 unchanged row-IN sources; 12 fixed certificate candidates / 20 columns; no source SQL or DDL executed')


if __name__ == '__main__':
    main()
