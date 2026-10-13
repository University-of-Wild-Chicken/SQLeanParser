#!/usr/bin/env python3
"""Certify 300 PostgreSQL examples and check them with a real PostgreSQL server.

Run lake build first. This uses only Python's standard library and PostgreSQL
binaries. --local-bin /path/to/pg/bin starts and removes a private cluster with
Unix sockets only (no TCP listener). Alternatively --dsn connects to PostgreSQL;
all schema creation, seed data, mutations, and checks then occur in one rolled-
back transaction in a fresh random schema. Existing schemas/data are untouched.

Each original and canonical statement runs on empty and populated tables. Its
result arity/rows are compared; RETURNING also compares the whole database state
after the mutation, then rolls back to the starting savepoint. Explicit result
oracles cover all six classes. statement_timeout bounds each PostgreSQL query.
These finite checks do not prove execution equivalence on arbitrary databases.
"""
from __future__ import annotations

import argparse
from contextlib import contextmanager
import csv
import io
import json
from pathlib import Path
import shutil
import subprocess
import tempfile
import uuid

ROOT = Path(__file__).resolve().parents[1]
EXE = ROOT / '.lake/build/bin/sqlean'
FIXTURES = ROOT / 'fixtures/postgresql'
CATEGORIES = ('distinct_on', 'aggregate_filter', 'casts', 'predicates', 'null_ordering', 'returning')
NULL = '__SQLEAN_NULL_697c193c__'
SEED = {
    'users': [(1, 24, 'Alice', 'Paris'), (2, 17, 'Bob', 'Paris'), (3, 38, 'Carol', 'Rome'),
              (4, 71, 'Dora', 'Rome'), (5, 33, "O'Brien", ''), (6, 40, 'Fran', 'Paris')],
    'orders': [(101, 1, 120, 'paid'), (102, 1, 50, 'paid'), (103, 2, 50, 'pending'),
               (104, 3, 220, 'paid'), (105, 999, 10, 'cancelled'), (106, 1, 0, 'pending')],
    'departments': [(1, 'Engineering'), (2, 'Sales'), (3, 'Vacant')],
    'employees': [(1, 1, 99, 'Ann', 100), (2, 1, 1, 'Ben', 80),
                  (3, 2, 1, 'Cara', 90), (4, 77, 99, 'Dale', 70)],
    'flags': [(1, True, 'Enabled'), (2, False, 'Disabled'), (3, True, 'Preview')],
}


def run(command: list[str], **kwargs) -> subprocess.CompletedProcess:
    result = subprocess.run(command, text=True, capture_output=True, check=False,
                            timeout=kwargs.pop('timeout', 30), **kwargs)
    if result.returncode:
        raise RuntimeError(f"Command failed ({result.returncode}): {command[0]}\n{result.stdout[-3000:]}\n{result.stderr}")
    return result


def sql_identifier(value: str) -> str:
    return '"' + value.replace('"', '""') + '"'


def sql_literal(value) -> str:
    if isinstance(value, bool):
        return 'TRUE' if value else 'FALSE'
    if isinstance(value, int):
        return str(value)
    return "'" + value.replace("'", "''") + "'"


@contextmanager
def connection(args):
    if args.local_bin:
        binaries = Path(args.local_bin).resolve()
        for name in ('initdb', 'pg_ctl', 'psql'):
            if not (binaries / name).is_file():
                raise SystemExit(f'Missing PostgreSQL binary: {binaries / name}')
        with tempfile.TemporaryDirectory(prefix='sqlean-pg-') as temporary:
            root = Path(temporary)
            data, sockets = root / 'data', root / 'sockets'
            sockets.mkdir(mode=0o700)
            run([str(binaries / 'initdb'), '-D', str(data), '--no-locale', '--encoding=UTF8',
                 '--auth=trust', '--username=sqlean_test'])
            started = False
            try:
                run([str(binaries / 'pg_ctl'), '-D', str(data), '-l', str(root / 'server.log'),
                     '-o', f"-k {sockets} -c listen_addresses='' -c fsync=off", '-w', 'start'])
                started = True
                yield [str(binaries / 'psql'), '-h', str(sockets), '-U', 'sqlean_test', '-d', 'postgres']
            finally:
                if started:
                    run([str(binaries / 'pg_ctl'), '-D', str(data), '-m', 'immediate', '-w', 'stop'])
    else:
        psql = args.psql or shutil.which('psql')
        if not psql:
            raise SystemExit('Use --local-bin /path/to/postgresql/bin or install psql and supply --dsn.')
        yield [psql, '--dbname', args.dsn]


def table_setup(schema: dict, populated: bool) -> list[str]:
    commands = []
    sql_types = {'int': 'INTEGER', 'text': 'TEXT', 'bool': 'BOOLEAN'}
    for table in schema['tables']:
        columns = ', '.join(f'{sql_identifier(c["name"])} {sql_types[c["type"]]} NOT NULL'
                            for c in table['columns'])
        commands.append(f'CREATE TABLE {sql_identifier(table["name"])} ({columns});')
    if populated:
        for table, rows in SEED.items():
            values = ', '.join('(' + ', '.join(map(sql_literal, row)) + ')' for row in rows)
            commands.append(f'INSERT INTO {sql_identifier(table)} VALUES {values};')
    return commands


def state_query() -> str:
    terms = []
    for table in sorted(SEED):
        terms.append(f"SELECT '{table}' AS table_name, COALESCE(json_agg(row_to_json(r)), '[]'::json)::text AS rows "
                     f'FROM (SELECT * FROM {sql_identifier(table)} ORDER BY id) r')
    return ' UNION ALL '.join(terms) + ';'


def load_cases() -> list[tuple[str, int, str, str]]:
    result = []
    for category in CATEGORIES:
        sources = (FIXTURES / f'{category}.sql').read_text().splitlines()
        assert len(sources) == len(set(sources)) == 50, category
        for index, source in enumerate(sources, 1):
            try:
                output = run([str(EXE), '--schema', str(FIXTURES / 'schema.json'), source], cwd=ROOT).stdout
                assert 'Valid query.' in output, output
                result.append((category, index, source, output.splitlines()[-1]))
            except Exception as error:
                raise AssertionError(f'{category} example {index}: {source}') from error
    return result


def parse_results(output: str) -> dict[str, tuple[int, list[list[str | None]]]]:
    sections: dict[str, list[str]] = {}
    current = None
    for line in output.splitlines():
        if line.startswith('__SQLEAN_CASE_'):
            current = line
            assert current not in sections, current
            sections[current] = []
        elif current is not None:
            sections[current].append(line)
    results = {}
    for name, lines in sections.items():
        rows = list(csv.reader(io.StringIO('\n'.join(lines) + '\n')))
        assert rows, (name, lines)
        arity = len(rows[0])
        rows = [row if row else [''] for row in rows]
        assert all(len(row) == arity for row in rows[1:]), (name, rows)
        results[name] = (arity, [[None if cell == NULL else cell for cell in row] for row in rows[1:]])
    return results


def marker(category: str, index: int, populated: bool, form: str, state=False) -> str:
    return f'__SQLEAN_CASE_{category}_{index}_{int(populated)}_{form}' + ('_state' if state else '')


def run_database(psql: list[str], cases) -> tuple[dict, str]:
    schema = json.loads((FIXTURES / 'schema.json').read_text())
    commands = ['BEGIN;', "SET LOCAL statement_timeout = '5s';", "SET LOCAL client_min_messages = warning;"]
    for populated in (False, True):
        namespace = 'sqlean_verify_' + uuid.uuid4().hex
        commands += [f'CREATE SCHEMA {sql_identifier(namespace)};',
                     f'SET LOCAL search_path = {sql_identifier(namespace)}, pg_catalog;']
        commands.extend(table_setup(schema, populated))
        for category, index, source, canonical in cases:
            for form, sql in (('source', source), ('canonical', canonical)):
                commands += ['SAVEPOINT sqlean_case;',
                             '\\echo ' + marker(category, index, populated, form), sql]
                if category == 'returning':
                    commands += ['\\echo ' + marker(category, index, populated, form, state=True), state_query()]
                commands.append('ROLLBACK TO SAVEPOINT sqlean_case;')
    commands += ['ROLLBACK;']
    output = run([*psql, '-X', '-q', '--csv', '-v', 'ON_ERROR_STOP=1', '-P', f'null={NULL}'],
                 input='\n'.join(commands), timeout=180).stdout
    version = run([*psql, '-X', '-At', '-c', 'SHOW server_version;']).stdout.strip()
    return parse_results(output), version


def independent_oracles(results: dict) -> int:
    # Hand-authored results distinguish selection, filtering, coercion, three-
    # valued predicates, explicit null placement, and old/new RETURNING rows.
    oracles = [
        ('distinct_on', 1, True, [['', "O'Brien"], ['Paris', 'Fran'], ['Rome', 'Dora']]),
        ('distinct_on', 6, True, [['1', '120'], ['2', '50'], ['3', '220'], ['999', '10']]),
        ('distinct_on', 1, False, []),
        ('aggregate_filter', 1, True, [['5']]),
        ('aggregate_filter', 2, True, [['1']]),
        ('aggregate_filter', 5, True, [['390']]),
        ('aggregate_filter', 11, True, [['2', '1']]),
        ('aggregate_filter', 13, True, [['6', None]]),
        ('aggregate_filter', 1, False, [['0']]),
        ('aggregate_filter', 5, False, [[None]]),
        ('casts', 1, True, [['42']]),
        ('casts', 5, True, [['t']]),
        ('casts', 9, True, [['1']]),
        ('casts', 12, True, [['f']]),
        ('casts', 19, True, [['1.23456789012345']]),
        ('casts', 20, True, [['1.2345679']]),
        ('casts', 34, True, [['0.5']]),
        ('casts', 41, False, [[None]]),
        ('predicates', 1, True, [['1']]),
        ('predicates', 2, True, [['1']]),
        ('predicates', 17, True, [['1'], ['3'], ['5']]),
        ('predicates', 18, True, [['2'], ['4'], ['6']]),
        ('predicates', 28, True, [['t']]),
        ('predicates', 29, True, [['1'], ['3'], ['5'], ['6']]),
        ('predicates', 44, False, [['t', 't', 't']]),
        ('null_ordering', 1, True,
         [['4', None], ['5', None], ['6', None], ['1', '0'], ['1', '50'], ['2', '50'], ['1', '120'], ['3', '220']]),
        ('null_ordering', 2, True,
         [['1', '0'], ['1', '50'], ['2', '50'], ['1', '120'], ['3', '220'], ['4', None], ['5', None], ['6', None]]),
        ('null_ordering', 46, True, [[None]]),
        ('returning', 1, False, [['20', '30', 'Zoe', 'Oslo']]),
        ('returning', 11, True, [['30', 'Oslo'], ['31', 'Rome']]),
        ('returning', 19, True, [['25']]),
        ('returning', 19, False, []),
        ('returning', 34, True, [['2', 't']]),
        ('returning', 37, True, [['2', '17', 'Bob', 'Paris']]),
        ('returning', 41, True, [['39']]),
        ('returning', 50, True, [['3', 'Vacant']]),
    ]
    for category, index, populated, expected in oracles:
        actual = results[marker(category, index, populated, 'source')][1]
        assert actual == expected, (category, index, populated, actual, expected)
    return len(oracles)


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    connection_args = parser.add_mutually_exclusive_group(required=True)
    connection_args.add_argument('--local-bin', help='Directory containing initdb, pg_ctl, psql')
    connection_args.add_argument('--dsn', help='PostgreSQL connection string; only a rollback-isolated random schema is used')
    parser.add_argument('--psql', help='psql executable for --dsn (defaults to PATH)')
    args = parser.parse_args()
    if not EXE.is_file():
        parser.error('Build the CLI first: lake build')
    cases = load_cases()
    with connection(args) as psql:
        results, version = run_database(psql, cases)
    assert len(results) == 1400, len(results)
    for category, index, source, canonical in cases:
        for populated in (False, True):
            original = results[marker(category, index, populated, 'source')]
            rendered = results[marker(category, index, populated, 'canonical')]
            assert original == rendered, (category, index, populated, source, canonical, original, rendered)
            if category == 'returning':
                original_state = results[marker(category, index, populated, 'source', True)]
                rendered_state = results[marker(category, index, populated, 'canonical', True)]
                assert original_state == rendered_state, (category, index, populated, original_state, rendered_state)
    oracle_count = independent_oracles(results)
    print(f'PASS: {len(cases)} examples certified by the CLI and executed by PostgreSQL {version}')
    print(f'PASS: 600 source/canonical result comparisons on empty and populated tables')
    print(f'PASS: 100 RETURNING mutation-state comparisons and {oracle_count} independent result oracles')


if __name__ == '__main__':
    main()
