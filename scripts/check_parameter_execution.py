#!/usr/bin/env python3
"""Bounded real EXECUTE/literal/handwritten-oracle comparison (no Lean needed).

Uses the existing isolated PostgreSQL connection and FORCE_QUOTE NULL protocol.
This checks fixture source SQL only, not SQLean canonicalization or general SQL
equivalence. Anonymous ? is translated by the existing fixture adapter.
"""
import argparse
import json
import uuid

import check_advanced_cli as advanced
from check_postgresql_cli import connection, copy_result, marker, parse_results, run, sql_literal


# Expectations are authored independently of bind_parameters and DB output.
# Each pair is (empty database rows, seeded database rows).
ORACLES = {
    2: ([['Paris', '?']], [['Paris', '?']]),
    17: ([['2', '1', '2']], [['2', '1', '2']]),
    22: ([['40', 'Inserted']], [['40', 'Inserted']]),
    23: ([], [['1', '50']]),
    24: ([], [['2']]),
    25: ([['1', 'Updated']], [['1', 'Updated']]),
    27: ([['Paris', '?']], [['Paris', '?']]),
    42: ([['1', '2']], [['1', '2']]),
    47: ([['40', 'Inserted']], [['40', 'Inserted']]),
    48: ([], [['1', '50']]),
    49: ([], [['2']]),
    50: ([['1', 'Updated']], [['1', 'Updated']]),
}


def load_cases():
    metadata = json.loads((advanced.FIXTURES / 'cases.json').read_text())['placeholders']
    lines = (advanced.FIXTURES / 'placeholders.sql').read_text().splitlines()
    cases = []
    for index, expected in ORACLES.items():
        case = metadata[index - 1]
        assert case['sql'] == lines[index - 1]
        cases.append((index, case, expected))
    # Add a fixed NULL-versus-marker boundary without modifying historic fixtures.
    from check_postgresql_cli import NULL
    cases.append((51, dict(sql='SELECT $2, $1, $2, $3;', parameters='Ttt',
                           values=[None, NULL, ''], types='tTtt'),
                  ([[NULL, None, NULL, '']], [[NULL, None, NULL, '']])))
    return cases


def prepared_capture(case):
    types = ', '.join(advanced.PG_TYPES[c.lower()] for c in case['parameters'])
    values = ', '.join(map(advanced.literal, case['values']))
    columns = ', '.join(f'c{i} {advanced.PG_TYPES[c.lower()]}'
                        for i, c in enumerate(case['types'], 1))
    execute = f'EXECUTE sqlean_parameters ({values})'
    # COPY cannot wrap EXECUTE. A typed set-returning bridge captures the rows
    # produced by the SQL EXECUTE command itself, including DML RETURNING.
    # It does not reconstruct the query or call bind_parameters.
    body = 'BEGIN RETURN QUERY EXECUTE ' + sql_literal(execute) + '; END;'
    return [
        f'PREPARE sqlean_parameters ({types}) AS {advanced.question_parameters(case["sql"])}',
        f'CREATE OR REPLACE FUNCTION pg_temp.sqlean_execute_rows() RETURNS TABLE ({columns}) '
        f'LANGUAGE plpgsql VOLATILE AS {sql_literal(body)};',
        copy_result('SELECT * FROM pg_temp.sqlean_execute_rows();'),
    ]


def database_script(cases):
    commands = ['\\encoding UTF8', 'BEGIN;', "SET LOCAL statement_timeout = '10s';",
                "SET LOCAL client_min_messages = warning;",
                'SET LOCAL standard_conforming_strings = on;', advanced.SNAPSHOT_FUNCTION]
    for populated in (False, True):
        namespace = 'sqlean_parameter_' + uuid.uuid4().hex
        commands += [f'CREATE SCHEMA "{namespace}";',
                     f'SET LOCAL search_path = "{namespace}", pg_catalog;']
        commands.extend(advanced.table_setup(populated))
        for index, case, _ in cases:
            for path in ('execute', 'literal'):
                commands.append('SAVEPOINT parameter_case;')
                capture = (prepared_capture(case) if path == 'execute' else
                           [copy_result(advanced.bind_parameters(case['sql'], case))])
                commands += capture[:-1]
                commands += ['\\echo ' + marker('parameter', index, populated, path), capture[-1]]
                if advanced.mutates(case['sql']):
                    commands += ['\\echo ' + marker('parameter', index, populated, path, True),
                                 copy_result('SELECT * FROM pg_temp.sqlean_snapshot() ORDER BY table_name;')]
                # Each path starts from identical data, including INSERT/UPSERT.
                commands.append('ROLLBACK TO SAVEPOINT parameter_case;')
                if path == 'execute':
                    commands.append('DEALLOCATE sqlean_parameters;')
    return '\n'.join(commands + ['ROLLBACK;'])


def verify(results, cases):
    expected_keys = set()
    for index, case, expected in cases:
        for populated in (False, True):
            for path in ('execute', 'literal'):
                key = marker('parameter', index, populated, path)
                expected_keys.add(key)
                want = (len(case['types']), expected[int(populated)])
                if results.get(key) != want:
                    raise AssertionError((key, results.get(key), want))
            if advanced.mutates(case['sql']):
                keys = [marker('parameter', index, populated, path, True)
                        for path in ('execute', 'literal')]
                expected_keys.update(keys)
                if any(key not in results for key in keys) or results[keys[0]] != results[keys[1]]:
                    raise AssertionError(('mutation state', keys))
    if set(results) != expected_keys:
        raise AssertionError(('unexpected/missing sections', set(results) ^ expected_keys))


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    group = parser.add_mutually_exclusive_group(required=True)
    group.add_argument('--local-bin')
    group.add_argument('--dsn')
    parser.add_argument('--psql')
    args = parser.parse_args()
    cases = load_cases()
    with connection(args) as psql:
        output = run([*psql, '-X', '-q', '-v', 'ON_ERROR_STOP=1'],
                     input=database_script(cases).encode(), text=False, timeout=120)
        results = parse_results(output.stdout.decode())
        verify(results, cases)
        version = run([*psql, '-X', '-At', '-c', 'SHOW server_version;']).stdout.strip()
    print(f'PASS: PostgreSQL {version}; {len(cases)} fixed cases x empty/seeded; '
          'real EXECUTE and literal rows each match independent expectations; mutation states match')
    print('Scope: fixture SQL and test adapter only; no canonicalization or universal equivalence claim.')


if __name__ == '__main__':
    main()
