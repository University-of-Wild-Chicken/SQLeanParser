"""Raw-tree syntax observations for the fixed noncorrelated source population.

This is a conservative lexical dependency screen, not a database analyzer or
independent validity specification. Unknown table fields remain unknown; supplied
column inventories must be backed by retained input declarations. Outputs and
runtime cardinality are never inferred here. Neither source SQL nor setup runs.
"""
from __future__ import annotations
import collections
import json

def walk(v, key):
    if isinstance(v, list):
        for x in v:
            yield from walk(x, key)
    elif isinstance(v, dict):
        if key in v:
            yield v[key]
        for x in v.values():
            yield from walk(x, key)

def queries(v):
    if isinstance(v, list):
        for x in v:
            yield from queries(x)
    elif isinstance(v, dict):
        if 'SelectStmt' in v:
            q = v['SelectStmt']
            yield q
            yield from queries(q)
            return
        for k, x in v.items():
            if k in ('larg', 'rarg') and isinstance(x, dict) and ('op' in x):
                yield x
            yield from queries(x)

def observe(sql, catalog=None):
    from pglast import parser, __version__
    if __version__ != 'v7.21':
        raise ValueError('source oracle requires pinned pglast 7.21')
    stmts = json.loads(parser.parse_sql_json(sql))['stmts']
    if len(stmts) != 1:
        raise ValueError('source must be one complete PostgreSQL statement')
    return observe_tree(stmts[0]['stmt'], catalog)

def observe_tree(t, catalog=None):
    catalog = catalog or {}
    if set(t) != {'SelectStmt'}:
        raise ValueError('source must be an ordinary SELECT statement')
    links = list(walk(t, 'SubLink'))
    if not links:
        raise ValueError('source does not contain an expression subquery')
    kinds = collections.Counter(('exists' if x['subLinkType'] == 'EXISTS_SUBLINK' else 'scalar' if x['subLinkType'] == 'EXPR_SUBLINK' else 'in' if x['subLinkType'] == 'ANY_SUBLINK' and (not x.get('operName')) else 'other' for x in links))
    deps = collections.Counter()
    for q in queries(t):
        for key in ['valuesLists', 'groupClause', 'havingClause', 'distinctClause', 'windowClause', 'intoClause']:
            if q.get(key):
                deps[key] += 1
        if q.get('withClause', {}).get('recursive'):
            deps['recursive'] += 1
    for key in ['RangeFunction', 'RangeTableSample', 'WindowDef', 'InsertStmt', 'UpdateStmt', 'DeleteStmt', 'MergeStmt']:
        if list(walk(t, key)):
            deps[key] += len(list(walk(t, key)))
    for c in walk(t, 'CommonTableExpr'):
        if c.get('ctematerialized', 'CTEMaterializeDefault') != 'CTEMaterializeDefault':
            deps['materialized'] += 1
    funcs = sorted({'.'.join((s['String']['sval'] for s in f['funcname'])) for f in walk(t, 'FuncCall')})
    if funcs:
        deps['function_calls'] = len(funcs)
    if kinds['other']:
        deps['other_sublinks'] = kinds['other']
    external = []
    correlated = []
    uncertain = []
    unresolved = []

    def output_name(v):
        if 'ColumnRef' in v:
            a = v['ColumnRef']['fields']
            return a[-1].get('String', {}).get('sval')
        if 'TypeCast' in v:
            return v['TypeCast']['typeName']['names'][-1]['String']['sval']
        if 'FuncCall' in v:
            return v['FuncCall']['funcname'][-1]['String']['sval']
        if 'SubLink' in v:
            return {'EXISTS_SUBLINK': 'exists', 'EXPR_SUBLINK': None}.get(v['SubLink']['subLinkType'], '?column?')
        return '?column?'

    def query(q, ctes, outer, depth):
        visible = dict(ctes)
        for wrapper in q.get('withClause', {}).get('ctes', []):
            c = wrapper['CommonTableExpr']
            if 'SelectStmt' not in c['ctequery']:
                continue
            cols = query(c['ctequery']['SelectStmt'], visible, outer, depth)
            aliases = [x['String']['sval'] for x in c.get('aliascolnames', [])]
            visible[c['ctename']] = aliases + cols[len(aliases):] if cols is not None else None
        if q.get('op', 'SETOP_NONE') != 'SETOP_NONE':
            left = query(q['larg'], visible, outer, depth)
            query(q['rarg'], visible, outer, depth)
            return left
        names = set()
        cols = []
        unknown = False

        def source(v):
            nonlocal unknown
            if 'RangeVar' in v:
                n = v['RangeVar']
                name = '.'.join((x for x in [n.get('catalogname'), n.get('schemaname'), n['relname']] if x))
                names.add(n.get('alias', {}).get('aliasname', n['relname']))
                cs = visible.get(name, catalog.get(name))
                if name not in visible:
                    external.append(name)
                if cs is None:
                    unknown = True
                else:
                    aliases = [x['String']['sval'] for x in n.get('alias', {}).get('colnames', [])]
                    cols.extend(aliases + cs[len(aliases):])
            elif 'RangeSubselect' in v:
                n = v['RangeSubselect']
                a = n.get('alias', {})
                names.add(a.get('aliasname', ''))
                cs = query(n['subquery']['SelectStmt'], visible, outer, depth)
                if cs is None:
                    unknown = True
                else:
                    aliases = [x['String']['sval'] for x in a.get('colnames', [])]
                    cols.extend(aliases + cs[len(aliases):])
                if n.get('lateral'):
                    deps['lateral'] += 1
            elif 'JoinExpr' in v:
                n = v['JoinExpr']
                source(n['larg'])
                source(n['rarg'])
                if n.get('alias'):
                    names.add(n['alias']['aliasname'])
            else:
                unknown = True
        for s in q.get('fromClause', []):
            source(s)
        frame = (names, set((x for x in cols if x is not None)), unknown)

        def expr(v):
            if isinstance(v, list):
                for x in v:
                    expr(x)
            elif isinstance(v, dict):
                if 'SubLink' in v:
                    n = v['SubLink']
                    expr(n.get('testexpr'))
                    query(n['subselect']['SelectStmt'], visible, [frame, *outer], depth + 1)
                    return
                if 'RangeSubselect' in v or 'RangeVar' in v:
                    return
                if 'ColumnRef' in v:
                    n = v['ColumnRef']
                    parts = [x.get('String', {}).get('sval', '*') for x in n['fields']]
                    if depth:
                        if len(parts) > 1:
                            if parts[0] not in names:
                                (correlated if any((parts[0] in f[0] for f in outer)) else unresolved).append(parts)
                        elif parts[0] != '*' and parts[0] not in frame[1]:
                            if unknown:
                                if any((f[0] or f[1] or f[2] for f in outer)):
                                    uncertain.append(parts)
                            else:
                                (correlated if any((parts[0] in f[1] or f[2] for f in outer)) else unresolved).append(parts)
                    return
                for k, x in v.items():
                    if k not in {'withClause', 'fromClause'}:
                        expr(x)
        expr(q)
        for s in q.get('fromClause', []):
            for join in walk(s, 'JoinExpr'):
                expr(join.get('quals'))
        out = []
        for w in q.get('targetList', []):
            r = w['ResTarget']
            v = r.get('val', {})
            if 'ColumnRef' in v and any(('A_Star' in n for n in v['ColumnRef']['fields'])):
                if unknown:
                    return None
                out.extend(cols)
            else:
                out.append(r.get('name') or output_name(v))
        return out
    query(t['SelectStmt'], {}, [], 0)
    return dict(factors=dict(kinds), dependencies=dict(deps), functions=funcs, external_relations=sorted(set(external)), parameters=sorted({p['number'] for p in walk(t, 'ParamRef')}), source_free=not external and (not list(walk(t, 'ParamRef'))), correlated=correlated, uncertain_scope=uncertain, unresolved_scope=unresolved, types=sorted({'.'.join((s['String']['sval'] for s in n['names'])) for n in walk(t, 'TypeName')}))
