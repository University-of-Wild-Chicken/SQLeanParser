#!/usr/bin/env python3
"""Reproduce whole unchanged VALUES query inputs without executing SQL.

Offline reproduction is standard-library only. --oracle additionally replays
pinned pglast 7.21 syntax observations; it is not a PG16 semantic analyzer.
Fixed output metadata is independently preregistered, never learned from SQLean.
"""
import argparse
from collections import Counter
import json
from pathlib import Path
import re

from extract_extended_type_corpus import sql_code
from extract_pagination_corpus import checked_file, comparison_key, sha256
from extract_statement_corpus import selected_sql, statement_spans

ROOT = Path(__file__).resolve().parents[1]
DIRECTORY = ROOT / 'fixtures/values_queries'
MANIFEST_SHA256 = 'cce4b0b252bdb0216e380be9b92542fb05564140854d1e72b14adfe9a2dd6106'
SOURCE_REGISTRY_SHA256 = '0d220fed00761035100956d5067d85b5a849de59a8971ed3d8bf254f74ce13dd'


def canonical(value):
    return json.dumps(value, sort_keys=True, separators=(',', ':'))


def complete_query(sql):
    code = sql_code(sql).strip()
    if (not re.match(r'\(*\s*(?:SELECT|WITH|VALUES)\b', code, re.I)
            or ';' in code.removesuffix(';') or '\x00' in sql
            or re.search(r'\$\{|[$][A-Za-z_]|__TEST_DIR__', sql)):
        raise ValueError('selection is not one literal VALUES/SELECT query input')


def sqllogic_inputs(source):
    """Read the finite retained simple SQLLogicTest dialect, never its results.

    Both query and statement-ok headers can contain complete VALUES queries.
    All setup, errors and result data are opaque. Unsupported control directives
    fail closed, so a matching-looking line inside a result cannot become input.
    """
    lines = source.splitlines(keepends=True)
    offsets = [0]
    for line in lines:
        offsets.append(offsets[-1] + len(line))
    i = 0
    query = re.compile(r'query [IRTB]+(?: (?:nosort|rowsort|valuesort|colnames|colnames,rowsort))?')
    while i < len(lines):
        header = lines[i].rstrip('\r\n')
        if not header.strip() or header.startswith('#'):
            i += 1
            continue
        is_query = query.fullmatch(header) is not None
        positive = header == 'statement ok' or is_query
        if not is_query and re.fullmatch(r'statement (?:ok|error(?: .*)?)', header) is None:
            raise ValueError(f'unsupported SQLLogicTest directive at line {i + 1}')
        header_line, start = i + 1, offsets[i + 1]
        i += 1
        while i < len(lines) and lines[i].strip() and lines[i].rstrip('\r\n') != '----':
            i += 1
        end = offsets[i]
        if start == end:
            raise ValueError('empty SQLLogicTest input')
        delimiter = i < len(lines) and lines[i].rstrip('\r\n') == '----'
        if is_query and not delimiter:
            raise ValueError('ordinary query lacks separate expected-result delimiter')
        if header == 'statement ok' and delimiter:
            raise ValueError('statement-ok result block is outside retained dialect')
        if positive:
            yield source[start:end], header_line + 1, {
                'kind': 'values_sqllogic_input', 'header_line': header_line,
                'start': start, 'end': end,
            }, header
        if delimiter:
            i += 1
            while i < len(lines) and lines[i].strip():
                i += 1


def selection(source, selector):
    if selector.get('kind') == 'sql_slice':
        if set(selector) != {'kind', 'start', 'end', 'statement_index'}:
            raise ValueError('invalid complete SQL statement selector')
        sql, line, detail = selected_sql(source, selector, statement_spans(source))
    elif selector.get('kind') == 'values_sqllogic_input':
        if (set(selector) != {'kind', 'header_line', 'start', 'end'}
                or any(type(selector[k]) is not int for k in ('header_line', 'start', 'end'))):
            raise ValueError('invalid VALUES SQLLogicTest selector')
        found = [(sql, line, header) for sql, line, sel, header in sqllogic_inputs(source) if sel == selector]
        if len(found) != 1:
            raise ValueError('selector is not a whole positive SQLLogicTest input')
        sql, line, header = found[0]
        detail = {'extraction': 'whole unchanged positive SQLLogicTest input',
                  'header_line': selector['header_line'], 'input_header': header,
                  'source_start': selector['start'], 'source_end': selector['end'],
                  'controls_executed': False}
    else:
        raise ValueError('unsupported VALUES source selector')
    complete_query(sql)
    return sql, line, detail


def syntax_observation(sql):
    from pglast import parser, scan, __version__
    from observe_subquery_source import walk, queries
    if __version__ != 'v7.21':
        raise ValueError('source oracle requires pinned pglast 7.21')
    statements = json.loads(parser.parse_sql_json(sql))['stmts']
    if len(statements) != 1 or set(statements[0]['stmt']) != {'SelectStmt'}:
        raise ValueError('source is not a whole query')
    tree = statements[0]['stmt']
    if any(list(walk(tree, kind)) for kind in ['InsertStmt', 'UpdateStmt', 'DeleteStmt', 'MergeStmt']):
        raise ValueError('DML VALUES is not a VALUES query source')
    values = [q for q in queries(tree) if q.get('valuesLists')]
    if not values:
        raise ValueError('source has no VALUES query body')
    tokens = [(t.name, sql.encode()[t.start:t.end + 1].decode().lower()) for t in scan(sql)
              if t.name not in {'SQL_COMMENT', 'C_COMMENT'} and sql.encode()[t.start:t.end + 1] != b';']
    ctes = sorted(c['ctename'] for c in walk(tree, 'CommonTableExpr'))
    refs = sorted({'.'.join(filter(None, [r.get('schemaname'), r['relname']])) for r in walk(tree, 'RangeVar')})
    observation = {
        'values_bodies': [{'rows': len(q['valuesLists']),
                           'widths': [len(row['List']['items']) for row in q['valuesLists']]}
                          for q in values],
        'query_class': 'standalone-values' if tree['SelectStmt'].get('valuesLists') else 'select-containing-values',
        'relation_references': refs, 'cte_names': ctes,
        # This lexical inventory is not a general scope analyzer. Each selected
        # CTE reference has a separately reviewed nonrecursive local definition.
        'external_relation_candidates': [r for r in refs if r not in ctes],
        'parameters': sorted({r['number'] for r in walk(tree, 'ParamRef')}),
        'functions': sorted({'.'.join(s['String']['sval'] for s in f['funcname']) for f in walk(tree, 'FuncCall')}),
        'lateral': any(r.get('lateral', False) for r in walk(tree, 'RangeSubselect')),
        'anonymous_derived_relations': sum(not r.get('alias') for r in walk(tree, 'RangeSubselect')),
        'ast_sha256': sha256(canonical(tree).encode()),
    }
    return observation, sha256(json.dumps(tokens, separators=(',', ':')).encode())


def validate_registry(manifest, registry):
    if sha256(canonical(registry).encode()) != SOURCE_REGISTRY_SHA256:
        raise ValueError('preregistered VALUES output metadata changed')
    if (len(registry) != 50 or manifest['expected_output_columns'] != 65
            or sum(len(e['output_columns']) for e in registry) != 65):
        raise ValueError('fixed VALUES certificate population changed')
    selections = {s['id']: s for s in manifest['selections']}
    if {r['id'] for r in registry} != set(selections) or len(selections) != 50:
        raise ValueError('VALUES registry identities changed')
    for r in registry:
        s = selections[r['id']]
        obs = s['observation']
        if (set(r) != {'id', 'catalogFile', 'output_columns'} or r['catalogFile'] is not None
                or obs['external_relation_candidates'] or obs['parameters'] or obs['functions'] or obs['lateral']
                or s['scope_basis'] not in {'closed expressions and local derived VALUES', 'closed expressions and retained local nonrecursive CTE'}):
            raise ValueError('VALUES candidate lacks its independently reviewed closed context')
        if any(set(c) != {'name', 'type', 'nullable', 'collation'} or type(c['nullable']) is not bool
               for c in r['output_columns']):
            raise ValueError('incomplete VALUES output descriptor')
        if len(s['values_body_columns']) != len(obs['values_bodies']):
            raise ValueError('missing preregistered VALUES body columns')
        for shape, columns in zip(obs['values_bodies'], s['values_body_columns']):
            if (shape['rows'] <= 0 or shape['widths'] != [len(columns)] * shape['rows'] or not columns
                    or [c['name'] for c in columns] != ['column' + str(i + 1) for i in range(len(columns))]
                    or any(set(c) != {'name', 'type', 'nullable', 'collation'} or type(c['nullable']) is not bool
                           for c in columns)):
                raise ValueError('invalid preregistered VALUES body metadata')
    return registry


def reproduce(manifest, oracle=False):
    if sha256(canonical(manifest).encode()) != MANIFEST_SHA256:
        raise ValueError('closed VALUES source manifest changed')
    data = {}
    for name, info in manifest['sources'].items():
        if re.fullmatch(r'[0-9a-f]{40}', info['commit']) is None:
            raise ValueError('source revision must be an immutable full pin')
        checked_file(ROOT, info['license_file'], info['license_sha256'])
        for notice in info.get('additional_notices', []):
            checked_file(ROOT, notice['local_path'], notice['sha256'])
        for file in info['files']:
            data[name, file['path']] = checked_file(ROOT, file['local_path'], file['sha256']).decode()
    for primary in manifest['primary_sources']:
        checked_file(ROOT, primary['local_path'], primary['sha256'])
    result = []
    for chosen in manifest['selections']:
        name, path = chosen['source'], chosen['source_file']
        info = manifest['sources'][name]
        sql, line, detail = selection(data[name, path], chosen['selector'])
        if sha256(sql.encode()) != chosen['sql_sha256']:
            raise ValueError('whole VALUES input bytes changed')
        if oracle and syntax_observation(sql) != (chosen['observation'], chosen['normalized_tokens_sha256']):
            raise ValueError('VALUES raw syntax or token observation changed')
        result.append({'id': chosen['id'], 'factor': 'values_query',
                       'query_class': chosen['observation']['query_class'], 'source': name,
                       'source_kind': info['source_kind'], 'source_file': path,
                       'source_url': f"{info['repository']}/blob/{info['commit']}/{path}#L{line}",
                       'commit': info['commit'], 'license': info['license'], 'line': line,
                       'sql': sql, 'raw_sql': sql, 'sql_sha256': chosen['sql_sha256'], 'transformations': [],
                       'parameter_types': None, 'observed_parameter_slots': chosen['observation']['parameters'],
                       'observed_syntax': chosen['observation'], 'extraction': detail,
                       'validity_scope': 'fixed-static-certificate-candidate',
                       'scope_claim': chosen['scope_basis'], 'source_sql_executed': False})
    if (len(result) != 50 or len({r['id'] for r in result}) != 50
            or len({comparison_key(r['sql'].strip().removesuffix(';')) for r in result}) != 50
            or len({s['normalized_tokens_sha256'] for s in manifest['selections']}) != 50
            or Counter(r['source'] for r in result) != manifest['expected_sources']
            or Counter(r['query_class'] for r in result) != manifest['expected_classes']):
        raise ValueError('closed VALUES count, class or identity population changed')
    return result


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--check', action='store_true')
    parser.add_argument('--oracle', action='store_true')
    args = parser.parse_args()
    manifest = json.loads((DIRECTORY / 'concrete_sources.json').read_text())
    registry = json.loads((DIRECTORY / 'source_contracts.json').read_text())
    validate_registry(manifest, registry)
    rows = reproduce(manifest, args.oracle)
    text = ''.join(json.dumps(r, ensure_ascii=False) + '\n' for r in rows)
    path = DIRECTORY / 'concrete.jsonl'
    if args.check:
        if path.read_text() != text:
            raise ValueError('saved VALUES corpus differs from whole-source extraction')
    else:
        path.write_text(text)
    print(f"50 unchanged VALUES query inputs; 50 preregistered closed candidates / {manifest['expected_output_columns']} columns; no source SQL or DDL executed")


if __name__ == '__main__':
    main()
