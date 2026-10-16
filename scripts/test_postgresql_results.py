#!/usr/bin/env python3
"""Offline regression tests for PostgreSQL COPY result identity (no server/Lean)."""
import csv
import io
import itertools
import subprocess
import unittest
from unittest.mock import patch

import check_postgresql_cli as checker


MARKER = checker.marker('returning', 1, True, 'source')


def wire(rows, arity=1, marker=MARKER):
    # Independent model of PostgreSQL's documented FORCE_QUOTE CSV output.
    lines = [marker + '\n', ','.join(['column'] * arity) + '\n']
    for row in rows:
        fields = []
        for cell in row:
            if cell is None:
                fields.append(checker.NULL)
            else:
                out = io.StringIO(newline='')
                csv.writer(out, quoting=csv.QUOTE_ALL, lineterminator='\n').writerow([cell])
                fields.append(out.getvalue()[:-1])
        lines.append(','.join(fields) + '\n')
    return ''.join(lines)


class ResultIdentityTests(unittest.TestCase):
    def test_legacy_collision_and_fixed_distinction(self):
        null = checker.NULL + '\n'
        text = '"' + checker.NULL + '"\n'
        def legacy(value):
            return [[None if c == checker.NULL else c for c in r]
                    for r in csv.reader(io.StringIO(value))]
        self.assertEqual(legacy(null), legacy(text))
        self.assertEqual(checker.parse_results(wire([[None], [checker.NULL]]))[MARKER],
                         (1, [[None], [checker.NULL]]))
        self.assertNotEqual(checker.parse_results(wire([[None]])),
                            checker.parse_results(wire([[checker.NULL]])))

    def test_text_boundaries(self):
        values = ['', checker.NULL, 'NULL', '\\N', ',', '"', '\r', '\n', '\r\n',
                  '中文😀', '\u2028\u2029', '__SQLEAN_CASE_fake',
                  'first\n__SQLEAN_CASE_fake\nlast', '"' + checker.NULL + '"']
        values += [''.join(p) for n in range(4)
                   for p in itertools.product(['a', ',', '"', '\r', '\n'], repeat=n)]
        rows = [[v, None, checker.NULL] for v in values]
        self.assertEqual(checker.parse_results(wire(rows, 3))[MARKER], (3, rows))

    def test_empty_result_preserves_arity(self):
        self.assertEqual(checker.parse_results(wire([], 3))[MARKER], (3, []))
        self.assertEqual(checker.parse_results(wire([['']]))[MARKER], (1, [['']]))

    def test_header_is_not_marker(self):
        data = MARKER + '\n__SQLEAN_CASE_header\n"value"\n'
        self.assertEqual(checker.parse_results(data)[MARKER], (1, [['value']]))

    def test_returning_state_sections(self):
        state = MARKER + '_state'
        rows = [['users', '[{"name":"' + checker.NULL + '"}]']]
        data = wire([[checker.NULL], [None]]) + wire(rows, 2, state)
        self.assertEqual(checker.parse_results(data),
                         {MARKER: (1, [[checker.NULL], [None]]), state: (2, rows)})

    def test_reject_invalid_protocol(self):
        for data in [MARKER + '\nx\n"unterminated', MARKER + '\nx\n"x"oops\n',
                     MARKER + '\nx\nunquoted\n', wire([['a', 'b']]),
                     wire([]) + wire([]), MARKER, 'unexpected\n']:
            with self.subTest(data=data), self.assertRaises(ValueError):
                checker.parse_results(data)

    def test_query_and_dml_wrapping(self):
        for sql in ['SELECT 1;', "SELECT ';';", 'INSERT INTO t VALUES (1) RETURNING *;',
                    'UPDATE t SET a=2 RETURNING a;', 'DELETE FROM t RETURNING *;',
                    checker.state_query()]:
            self.assertEqual(checker.copy_result(sql),
                             f'COPY ({sql[:-1]}) TO STDOUT WITH (FORMAT CSV, HEADER TRUE, '
                             f"NULL '{checker.NULL}', FORCE_QUOTE *);")

    def test_executor_uses_copy_for_results_and_state(self):
        sql = 'DELETE FROM users RETURNING *;'
        with patch.object(checker, 'run', side_effect=[
            subprocess.CompletedProcess([], 0, wire([['a\rb']]).encode(), b''),
            subprocess.CompletedProcess([], 0, '16\n', '')]) as run:
            results, version = checker.run_database(['psql'], [('returning', 1, sql, sql)])
        args, kwargs = run.call_args_list[0]
        script = kwargs['input'].decode()
        self.assertFalse(kwargs['text'])  # Do not normalize CR/CRLF in actual TEXT.
        self.assertEqual(script.count(checker.copy_result(sql)), 4)
        self.assertEqual(script.count(checker.copy_result(checker.state_query())), 4)
        self.assertEqual(script.count('ROLLBACK TO SAVEPOINT sqlean_case;'), 4)
        self.assertTrue(script.endswith('ROLLBACK;'))
        self.assertIn('\\encoding UTF8', script)
        self.assertEqual(results[MARKER], (1, [['a\rb']]))
        self.assertEqual(version, '16')


if __name__ == '__main__':
    unittest.main()
