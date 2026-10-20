#!/usr/bin/env python3
"""Finite authored NULL-predicate precedence regressions; never execute source corpora.

The default run compares 680 source/canonical statements on native SQLite and
72 IS versus DISTINCT spelling pairs, including SQLite's Boolean-literal rule.
This tests target-native observations, not PostgreSQL/SQLite equivalence. The
optional --postgres-ast uses pglast v7.21 / PostgreSQL 17.7 solely as a pinned
raw-parse comparison for 252 authored forms. It is not the PostgreSQL 16 grammar
certificate, semantic analysis, or execution oracle.
"""
from __future__ import annotations

import argparse
import json
from pathlib import Path
import sqlite3
import subprocess

ROOT = Path(__file__).resolve().parents[1]
EXE = ROOT / '.lake/build/bin/sqlean'
BINARY = ('=', '<>', '<', '<=', '>', '>=', 'IS DISTINCT FROM',
          'IS NOT DISTINCT FROM', 'AND', 'OR', '+', '||')
POSTFIX = ('ISNULL', 'NOTNULL', 'IS NULL', 'IS NOT NULL')
PROFILES = {'identity': 'sqlean-select-render-v0.1', 'sqlite': 'sqlite-3.39-select-render-v0.1'}
# Authored values independently anchor the source/canonical comparison. In
# particular a Boolean literal and a unary-plus Boolean have different IS rules.
ANCHORS = {
    'SELECT 2 IS TRUE': 1,
    'SELECT 2 IS +TRUE': 0,
    'SELECT NULL IS TRUE': 0,
    'SELECT NULL IS NOT FALSE': 1,
    "SELECT '1' IS TRUE": 1,
    "SELECT 'x' IS FALSE": 1,
    'SELECT 1 IS NULL || 0': 0,
    'SELECT 1 IS NOT NULL || 0': 1,
    'SELECT 1 IS DISTINCT FROM 2 < 0': 1,
    'SELECT 1 IS DISTINCT FROM 2 > 0': 0,
    'SELECT 1 = 2 LIKE 0': 1,
    'SELECT 1 = 1 IN (1)': 1,
    'SELECT 1 LIKE 2 = 0': 1,
    'SELECT 1 BETWEEN 0 AND 2 = 1': 1,
    'SELECT 1 LIKE 2 BETWEEN 0 AND 3': 1,
    'SELECT 1 IS DISTINCT FROM 2 LIKE 0': 0,
    'SELECT 1 LIKE 2 IS DISTINCT FROM 0': 0,
    'SELECT 0 LIKE 2 IS DISTINCT FROM 1': 1,
    'SELECT 0 BETWEEN 0 AND 0 = 2': 0,
}


def sqlite_cases():
    sources = set()
    for postfix in POSTFIX:
        for operator in BINARY:
            for prefix in ('', 'NOT '):
                for left, right in (('NULL', '0'), ('1', '0'), ('2', 'NULL')):
                    sources.add(f'SELECT {prefix}{left} {postfix} {operator} {right}')
                    sources.add(f'SELECT {prefix}{left} {operator} {right} {postfix}')
        for following in POSTFIX:
            sources.add(f'SELECT NULL {postfix} {following}')
    for first in BINARY:
        for second in BINARY:
            if 'DISTINCT' in first or 'DISTINCT' in second:
                for left, right in (('1', '0'), ('NULL', 'NULL')):
                    sources.add(f'SELECT {left} {first} 2 {second} {right}')
    assert len(sources) == 680
    return sorted(sources)


def postgres_cases():
    sources = set()
    for postfix in POSTFIX:
        for operator in BINARY:
            for prefix in ('', 'NOT '):
                sources.add(f'SELECT {prefix}1 {postfix} {operator} 2')
                sources.add(f'SELECT {prefix}1 {operator} 2 {postfix}')
        for following in POSTFIX:
            sources.add(f'SELECT 1 {postfix} {following}')
    for first in BINARY:
        for second in BINARY:
            if 'DISTINCT' in first or 'DISTINCT' in second:
                sources.add(f'SELECT 1 {first} 2 {second} 3')
    assert len(sources) == 252
    return sorted(sources)


def spelling_pairs():
    pairs = []
    for left in ('0', '1', '2', 'NULL', "'x'", "'1'"):
        for right in ('TRUE', 'FALSE', '+TRUE', '(TRUE)', 'TRUE+0', '(NOT NULL)'):
            for negated in (False, True):
                pairs.append((f'SELECT {left} IS {"NOT " if negated else ""}{right}',
                              f'SELECT {left} IS {"" if negated else "NOT "}DISTINCT FROM {right}'))
    assert len(pairs) == 72
    return pairs


def invoke(sql, mode, executable=EXE):
    process = subprocess.run([str(executable), '--render-assurance', mode, sql],
                             cwd=ROOT, text=True, capture_output=True, timeout=20)
    assert not process.stderr.strip(), f'unexpected renderer stderr: {process.stderr}'
    report = json.loads(process.stdout)
    assert isinstance(report, dict) and report.get('mode') == mode, report
    assert report.get('profile') == PROFILES[mode], report
    assert report.get('assurance') == 'checked-roundtrip', report
    assert report.get('semanticPreservation') is False, report
    status = report.get('status')
    if status == 'rendered':
        assert process.returncode == 0, (process.returncode, report)
        assert report.get('parameterMap') == [], report
        assert isinstance(report.get('sql'), str) and report['sql'].strip(), report
    else:
        assert status == 'invalid' and process.returncode == 1, (process.returncode, report)
        assert report.get('diagnostic', {}).get('code') == 'input.parse', report
    return report


def observation(database, sql):
    """Retain both native values and storage classes; do not equate 1 with 1.0."""
    ticks = 0
    def budget():
        nonlocal ticks
        ticks += 1
        return int(ticks >= 100)
    database.set_progress_handler(budget, 1000)
    try:
        rows = database.execute(sql).fetchall()
    finally:
        database.set_progress_handler(None, 0)
    assert len(rows) == 1 and len(rows[0]) == 1, (sql, rows)
    return type(rows[0][0]).__name__, rows[0][0]


def compare_sqlite(database, source, canonical):
    expected, actual = observation(database, source), observation(database, canonical)
    assert expected == actual, (source, canonical, expected, actual)


def check_sqlite(executable=EXE):
    assert sqlite3.sqlite_version_info >= (3, 39, 0), 'SQLite 3.39+ is required for DISTINCT aliases'
    database = sqlite3.connect(':memory:')
    try:
        sources = sqlite_cases()
        for source in sources:
            report = invoke(source, 'sqlite', executable)
            assert report['status'] == 'rendered', (source, report)
            compare_sqlite(database, source, report['sql'])
        pairs = spelling_pairs()
        for source, alias in pairs:
            compare_sqlite(database, source, alias)
        for source, expected in ANCHORS.items():
            assert observation(database, source) == ('int', expected), (source, expected)
            report = invoke(source, 'sqlite', executable)
            assert report['status'] == 'rendered', (source, report)
            assert observation(database, report['sql']) == ('int', expected), (source, report, expected)
    finally:
        database.close()
    return len(sources), len(pairs), len(ANCHORS)


def clean_pg_tree(value):
    if isinstance(value, dict):
        return {key: clean_pg_tree(item) for key, item in value.items()
                if key not in {'location', 'stmt_len', 'stmt_location', 'version'}}
    if isinstance(value, list):
        return [clean_pg_tree(item) for item in value]
    return value


def check_postgres_ast(executable=EXE):
    import pglast
    from pglast import parser
    assert pglast.__version__ == 'v7.21', 'the optional raw-AST oracle requires pinned pglast v7.21'
    assert pglast.get_postgresql_version() == (17, 7), 'the optional raw-AST oracle requires PostgreSQL 17.7'
    sources = postgres_cases()
    for source in sources:
        try:
            expected = clean_pg_tree(json.loads(parser.parse_sql_json(source)))
        except parser.ParseError:
            expected = None
        report = invoke(source, 'identity', executable)
        if expected is None:
            assert report['status'] == 'invalid', (source, report)
        else:
            assert report['status'] == 'rendered', (source, report)
            actual = clean_pg_tree(json.loads(parser.parse_sql_json(report['sql'])))
            assert expected == actual, (source, report['sql'], expected, actual)
    return len(sources)


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--executable', type=Path, default=EXE)
    parser.add_argument('--postgres-ast', action='store_true', help='also use pinned pglast v7.21 (optional)')
    args = parser.parse_args()
    count, pairs, anchors = check_sqlite(args.executable)
    print(f'SQLite {sqlite3.sqlite_version}: {count} authored source/canonical precedence pairs, '
          f'{pairs} IS spelling pairs, {anchors} independently authored value anchors passed.')
    if args.postgres_ast:
        print(f'Optional pglast v7.21 / PostgreSQL 17.7 raw parser: {check_postgres_ast(args.executable)} authored raw-AST/rejection comparisons passed.')


if __name__ == '__main__':
    main()
