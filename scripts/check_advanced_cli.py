#!/usr/bin/env python3
"""Check the 750 advanced fixtures against isolated PostgreSQL databases.

By default every query is certified/canonicalized by the SQLean CLI. --source-only
is a PostgreSQL fixture audit while a compiler is being developed. The normal
check compares source/canonical results and mutation/DDL catalog+data effects on
empty and seeded databases. Typed parameters are bound through PostgreSQL's
PREPARE mechanism; question marks are translated by a string-aware test adapter.
No existing schema is changed: each run rolls back its random-schema transaction.
"""
from __future__ import annotations
import argparse
import json
from pathlib import Path
import re
import uuid
from check_postgresql_cli import (connection, copy_result, marker, parse_results,
                                  run, sql_identifier, sql_literal, SEED as BASE_SEED)

ROOT = Path(__file__).resolve().parents[1]
FIXTURES = ROOT / 'fixtures/advanced'
EXE = ROOT / '.lake/build/bin/sqlean'
TYPE_NAMES = {'i': 'int', 't': 'text', 'b': 'bool', 'r': 'real'}
PG_TYPES = {'i': 'INTEGER', 't': 'TEXT', 'b': 'BOOLEAN', 'r': 'DOUBLE PRECISION'}
SEED = dict(BASE_SEED, profiles=[(1, 'Paris', 4.5), (2, 'Paris', None), (3, 'Rome', 2.25),
                                (7, 'Oslo', 3.5)], tags=[(1, 'active'), (3, 'vip'), (8, 'orphan')],
            archive=[], scratch=[(1, 'alpha', 1.25, True), (2, None, None, False),
                                 (3, '', 4.5, None)])


def literal(value):
    if value is None:
        return 'NULL'
    if isinstance(value, float):
        return repr(value)
    return sql_literal(value)


def question_parameters(source):
    """Translate true template bindings, retaining PostgreSQL question operators."""
    from sql_parameter_observer import postgres_parameters
    return postgres_parameters(source)


def bind_parameters(source, case):
    """Produce typed literal equivalents after PREPARE/EXECUTE checks binding/types.

    COPY cannot directly wrap EXECUTE, so a lexer-aware adapter substitutes
    explicitly cast test literals for result capture. It never interpolates
    user input; PREPARE/EXECUTE independently runs the same placeholder SQL.
    """
    source = question_parameters(source)
    if not case['parameters']:
        return source
    values = {index: f'({literal(value)}::{PG_TYPES[code.lower()]})'
              for index, (code, value) in enumerate(zip(case['parameters'], case['values']), 1)}
    pattern = re.compile(r"'(?:[^']|'')*'|\"(?:[^\"]|\"\")*\"|\$(\d+)")
    return pattern.sub(lambda match: values[int(match.group(1))] if match.group(1) else match.group(), source)


def table_setup(populated):
    commands = []
    schema = json.loads((FIXTURES / 'schema.json').read_text())
    for table in schema['tables']:
        columns = []
        for column in table['columns']:
            sql_type = {'int': 'INTEGER', 'text': 'TEXT', 'bool': 'BOOLEAN', 'real': 'REAL'}[column['type']]
            text = f'{sql_identifier(column["name"])} {sql_type}'
            if not column.get('nullable', False):
                text += ' NOT NULL'
            if 'default' in column:
                text += ' DEFAULT ' + column['default']
            columns.append(text)
        for key in table.get('uniqueKeys', []):
            columns.append('UNIQUE (' + ', '.join(map(sql_identifier, key)) + ')')
        commands.append(f'CREATE TABLE {sql_identifier(table["name"])} ({", ".join(columns)});')
    if populated:
        for table, rows in SEED.items():
            if rows:
                values = ', '.join('(' + ', '.join(map(literal, row)) + ')' for row in rows)
                commands.append(f'INSERT INTO {sql_identifier(table)} VALUES {values};')
    return commands


SNAPSHOT_FUNCTION = r'''
CREATE FUNCTION pg_temp.sqlean_snapshot()
RETURNS TABLE(table_name TEXT, columns TEXT, constraints TEXT, rows TEXT)
LANGUAGE plpgsql AS $body$
DECLARE relation RECORD;
BEGIN
  FOR relation IN SELECT c.oid, c.relname FROM pg_class c JOIN pg_namespace n ON n.oid = c.relnamespace
                  WHERE n.nspname = current_schema() AND c.relkind = 'r' ORDER BY c.relname LOOP
    table_name := relation.relname;
    SELECT jsonb_agg(jsonb_build_array(a.attname, format_type(a.atttypid, a.atttypmod), a.attnotnull,
                                     pg_get_expr(d.adbin, d.adrelid)) ORDER BY a.attnum)::TEXT
    INTO columns FROM pg_attribute a LEFT JOIN pg_attrdef d ON d.adrelid = a.attrelid AND d.adnum = a.attnum
    WHERE a.attrelid = relation.oid AND a.attnum > 0 AND NOT a.attisdropped;
    SELECT COALESCE(jsonb_agg(jsonb_build_array(c.contype, pg_get_constraintdef(c.oid))
                             ORDER BY c.contype, pg_get_constraintdef(c.oid)), '[]'::jsonb)::TEXT
    INTO constraints FROM pg_constraint c WHERE c.conrelid = relation.oid;
    EXECUTE format('SELECT COALESCE(jsonb_agg(x ORDER BY x::text), ''[]''::jsonb)::text '
                   'FROM (SELECT to_jsonb(t) x FROM %I.%I t) source', current_schema(), relation.relname) INTO rows;
    RETURN NEXT;
  END LOOP;
END
$body$;
'''


def load_cases(source_only=False):
    metadata = json.loads((FIXTURES / 'cases.json').read_text())
    result = []
    for category, cases in metadata.items():
        sources = (FIXTURES / f'{category}.sql').read_text().splitlines()
        assert len(sources) == len(set(sources)) == len(cases) == 50, category
        for index, (source, case) in enumerate(zip(sources, cases), 1):
            assert source == case['sql'], (category, index)
            canonical = source
            if not source_only:
                command = [str(EXE), '--schema', str(FIXTURES / 'schema.json')]
                if case['parameters']:
                    command += ['--param-types', ','.join(TYPE_NAMES[c.lower()] for c in case['parameters'])]
                try:
                    output = run([*command, source], cwd=ROOT).stdout
                    assert 'Valid ' in output, output
                    canonical = output.splitlines()[-1]
                except Exception as error:
                    raise AssertionError(f'{category} example {index}: {source}') from error
            result.append((category, index, case, canonical))
    assert len(result) == 750
    return result


def ordered_result(source):
    """Only a top-level ORDER BY constrains the result row sequence."""
    depth = 0
    tokens = re.compile(r"'(?:[^']|'')*'|\"(?:[^\"]|\"\")*\"|\(|\)|\bORDER\s+BY\b", re.I)
    for token in tokens.finditer(source):
        text = token.group()
        if text == '(':
            depth += 1
        elif text == ')':
            depth -= 1
        elif depth == 0 and text.upper().startswith('ORDER'):
            return True
    return False


def mutates(source):
    return source.split(None, 1)[0] in ('INSERT', 'UPDATE', 'DELETE', 'CREATE', 'ALTER', 'DROP')


def run_database(psql, cases, source_only=False):
    commands = ['\\encoding UTF8', 'BEGIN;', "SET LOCAL statement_timeout = '10s';",
                "SET LOCAL client_min_messages = warning;", SNAPSHOT_FUNCTION]
    for populated in (False, True):
        namespace = 'sqlean_advanced_' + uuid.uuid4().hex
        commands += [f'CREATE SCHEMA {sql_identifier(namespace)};',
                     f'SET LOCAL search_path = {sql_identifier(namespace)}, pg_catalog;']
        commands.extend(table_setup(populated))
        for category, index, case, canonical in cases:
            forms = [('source', case['sql'])] if source_only else [('source', case['sql']), ('canonical', canonical)]
            for form, source in forms:
                commands.append('SAVEPOINT sqlean_case;')
                if case['parameters']:
                    paramtypes = ', '.join(PG_TYPES[c.lower()] for c in case['parameters'])
                    bound_values = ', '.join(map(literal, case['values']))
                    commands += [f'PREPARE sqlean_parameters ({paramtypes}) AS {question_parameters(source)}',
                                 'SAVEPOINT sqlean_bound;', '\\o /dev/null',
                                 f'EXECUTE sqlean_parameters ({bound_values});', '\\o',
                                 'ROLLBACK TO SAVEPOINT sqlean_bound;', 'DEALLOCATE sqlean_parameters;']
                sql = bind_parameters(source, case)
                if case['types']:
                    commands += ['\\echo ' + marker(category, index, populated, form), copy_result(sql)]
                else:
                    commands += [sql, '\\echo ' + marker(category, index, populated, form), copy_result("SELECT 'ok' AS status;")]
                if mutates(source):
                    commands += ['\\echo ' + marker(category, index, populated, form, state=True),
                                 copy_result('SELECT * FROM pg_temp.sqlean_snapshot() ORDER BY table_name;')]
                commands.append('ROLLBACK TO SAVEPOINT sqlean_case;')
    commands.append('ROLLBACK;')
    completed = run([*psql, '-X', '-q', '-v', 'ON_ERROR_STOP=1'],
                    input='\n'.join(commands).encode(), text=False, timeout=240)
    version = run([*psql, '-X', '-At', '-c', 'SHOW server_version;']).stdout.strip()
    return parse_results(completed.stdout.decode()), version


def independent_oracles(results):
    oracles = [
        ('in_subqueries', 1, True, [['1'], ['2'], ['3']]),
        ('in_subqueries', 3, True, [['t']]),
        ('in_subqueries', 10, True, [[str(i)] for i in range(1, 7)]),
        ('in_subqueries', 3, False, [['f']]),
        ('exists', 1, True, [['1'], ['2'], ['3']]),
        ('exists', 8, False, [['t']]),
        ('exists', 9, True, [['f']]),
        ('lateral', 3, True, [['1', '25'], ['2', '18'], ['3', '39'], ['4', '72'], ['5', '34'], ['6', '41']]),
        ('lateral', 4, True, [['1', '2'], ['2', '1'], ['3', '1'], ['4', '0'], ['5', '0'], ['6', '0']]),
        ('lateral', 10, True, [['1', '25', '50'], ['2', '18', '36'], ['3', '39', '78'], ['4', '72', '144'], ['5', '34', '68'], ['6', '41', '82']]),
        ('using_joins', 1, True, [['1', 'Paris', '4.5']]),
        ('natural_joins', 1, True, [['1', 'active'], ['3', 'vip']]),
        ('intersect', 1, True, [['1'], ['2'], ['3']]),
        ('intersect', 2, True, [['1']]),
        ('except', 1, True, [['4'], ['5'], ['6']]),
        ('except', 2, True, [['1'], ['1'], ['2'], ['3'], ['999']]),
        ('intersect', 44, True, [['1'], ['2']]),
        ('intersect', 45, True, [['1'], ['2']]),
        ('intersect', 46, True, [['2']]),
        ('except', 44, True, [['2']]),
        ('except', 45, True, [['2']]),
        ('except', 46, True, [['1']]),
        ('upsert', 1, True, []),
        ('upsert', 1, False, [['1', 'Updated 1']]),
        ('upsert', 2, True, [['1', 'Updated 1']]),
        ('upsert', 6, True, [['130']]),
        ('insert_select', 2, True, [['1', 'Alice']]),
        ('insert_select', 8, True, []),
        ('nulls', 1, True, [[None]]), ('nulls', 15, True, [[None]]),
        ('nulls', 18, True, [['t']]), ('nulls', 21, True, [[None]]),
        ('nulls', 22, True, [['t']]), ('nulls', 32, True, [['2']]),
        ('nulls', 35, True, []), ('nulls', 38, True, [['2']]),
        ('nulls', 39, True, [['5.75']]), ('nulls', 39, False, [[None]]),
        ('nulls', 44, False, [['20', None, None, None]]),
        ('floating', 1, True, [['0.125']]), ('floating', 11, True, [['0.5']]),
        ('floating', 21, True, [['2']]), ('floating', 31, True, [['125']]),
        ('floating', 41, True, [['0.03']]),
        ('placeholders', 12, True, [['1'], ['3'], ['5'], ['6']]),
        ('placeholders', 37, True, [['1'], ['3'], ['5'], ['6']]),
        ('placeholders', 16, True, [['3.75']]),
        ('placeholders', 17, True, [['2', '1', '2']]),
        ('placeholders', 42, True, [['1', '2']]),
        ('placeholders', 2, True, [['Paris', '?']]),
        ('placeholders', 27, True, [['Paris', '?']]),
        ('placeholders', 25, True, [['1', 'Updated']]),
        ('placeholders', 50, True, [['1', 'Updated']]),
    ]
    for category, index, populated, expected in oracles:
        actual = results[marker(category, index, populated, 'source')][1]
        assert actual == expected, (category, index, populated, actual, expected)
    # Independent catalog-effect oracles, separate from source/canonical equality.
    checks = [
        ('create_table', 1, 'made_1_plain', 'value', 'integer', False),
        ('create_table', 2, 'made_1_required', 'value', 'integer', True),
        ('create_table', 3, 'made_1_default', 'value', 'integer', False),
        ('alter_table', 1, 'scratch', 'added_1', 'integer', False),
        ('alter_table', 3, 'scratch', 'added_required_1', 'integer', True),
        ('alter_table', 5, 'scratch', 'renamed_name_1', 'text', False),
    ]
    for category, index, table, column, typ, required in checks:
        state = results[marker(category, index, True, 'source', True)][1]
        row = next(row for row in state if row[0] == table)
        descriptor = next(item for item in json.loads(row[1]) if item[0] == column)
        assert descriptor[:3] == [column, typ, required], (category, index, descriptor)
    renamed = results[marker('alter_table', 7, True, 'source', True)][1]
    assert 'renamed_scratch_1' in [row[0] for row in renamed]
    assert 'scratch' not in [row[0] for row in renamed]
    dropped = results[marker('drop_table', 6, True, 'source', True)][1]
    assert 'scratch' not in [row[0] for row in dropped]
    return len(oracles) + len(checks) + 2


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    group = parser.add_mutually_exclusive_group(required=True)
    group.add_argument('--local-bin')
    group.add_argument('--dsn')
    parser.add_argument('--psql')
    parser.add_argument('--source-only', action='store_true', help='Audit only PostgreSQL fixture execution; does not certify SQLean')
    args = parser.parse_args()
    cases = load_cases(args.source_only)
    with connection(args) as psql:
        results, version = run_database(psql, cases, args.source_only)
    result_checks = state_checks = 0
    for category, index, case, canonical in cases:
        for populated in (False, True):
            for form in (('source',) if args.source_only else ('source', 'canonical')):
                actual = results[marker(category, index, populated, form)]
                assert actual[0] == max(1, len(case['types'])), (category, index, actual[0], case['types'])
    if not args.source_only:
        for category, index, case, canonical in cases:
            for populated in (False, True):
                source = results[marker(category, index, populated, 'source')]
                rendered = results[marker(category, index, populated, 'canonical')]
                # Without ORDER BY, SQL does not promise row order. Comparing
                # multisets preserves duplicate multiplicity and NULL identity.
                normalize = (lambda result: result) if ordered_result(case['sql']) else (
                    lambda result: (result[0], sorted(result[1], key=repr)))
                assert normalize(source) == normalize(rendered), (category, index, populated, source, rendered)
                result_checks += 1
                if mutates(case['sql']):
                    source_state = results[marker(category, index, populated, 'source', True)]
                    rendered_state = results[marker(category, index, populated, 'canonical', True)]
                    assert source_state == rendered_state, (category, index, populated, source_state, rendered_state)
                    state_checks += 1
    oracle_count = independent_oracles(results)
    print(f'PASS: 750 advanced examples executed by PostgreSQL {version}')
    if not args.source_only:
        print(f'PASS: 750 CLI certificates; {result_checks} source/canonical result/status comparisons; {state_checks} mutation/DDL state comparisons')
    print(f'PASS: {oracle_count} independent result/catalog oracles')


if __name__ == '__main__':
    main()
