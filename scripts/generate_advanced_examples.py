#!/usr/bin/env python3
"""Generate 50 distinct examples in each of fifteen advanced SQL classes.

Expected types and parameter values are authored with the statements, not
inferred from SQLean. Lowercase i/t/b/r denote non-null primitive types;
uppercase letters denote nullable types. --check verifies checked-in fixtures.
"""
from __future__ import annotations
import argparse
import copy
import json
from pathlib import Path
from generate_relational_examples import SCHEMA as BASE_SCHEMA

ROOT = Path(__file__).resolve().parents[1]
FIXTURES = ROOT / 'fixtures/advanced'
SCHEMA = copy.deepcopy(BASE_SCHEMA)
for table in SCHEMA['tables']:
    table['uniqueKeys'] = [['id']]
SCHEMA['tables'] += [
    {'name': 'profiles', 'columns': [
        {'name': 'id', 'type': 'int'}, {'name': 'city', 'type': 'text'},
        {'name': 'rating', 'type': 'real', 'nullable': True}], 'uniqueKeys': [['id']]},
    {'name': 'tags', 'columns': [
        {'name': 'id', 'type': 'int'}, {'name': 'label', 'type': 'text'}], 'uniqueKeys': [['id']]},
    {'name': 'archive', 'columns': copy.deepcopy(SCHEMA['tables'][0]['columns']), 'uniqueKeys': [['id']]},
    {'name': 'scratch', 'columns': [
        {'name': 'id', 'type': 'int'}, {'name': 'name', 'type': 'text', 'nullable': True},
        {'name': 'score', 'type': 'real', 'nullable': True},
        {'name': 'enabled', 'type': 'bool', 'nullable': True}], 'uniqueKeys': [['id']]},
]
CATEGORIES = ('in_subqueries', 'exists', 'lateral', 'using_joins', 'natural_joins',
              'intersect', 'except', 'upsert', 'insert_select', 'nulls', 'floating',
              'placeholders', 'create_table', 'alter_table', 'drop_table')
EXAMPLES = {category: [] for category in CATEGORIES}


def add(category, types, sql, parameters='', values=None):
    assert set(types + parameters) <= set('itbrITBR')
    EXAMPLES[category].append({'sql': sql, 'types': types, 'parameters': parameters,
                               'values': values or []})


for n, city in enumerate(('Paris', 'Rome', '', 'Oslo', 'Berlin'), 1):
    # Correlation, negation, text/bool operands, aggregate subqueries, nesting,
    # and empty results all occur independently of changing fixture constants.
    for types, sql in [
        ('i', f'SELECT id FROM users WHERE id IN (SELECT user_id FROM orders WHERE amount >= {n * 25}) ORDER BY id;'),
        ('it', f"SELECT id, name FROM users WHERE id NOT IN (SELECT user_id FROM orders WHERE status = 'paid' AND amount > {n * 20}) ORDER BY id;"),
        ('b', f'SELECT {n} IN (SELECT user_id FROM orders);'),
        ('ib', f'SELECT u.id, u.id IN (SELECT o.user_id FROM orders o WHERE o.amount > u.age + {n}) FROM users u ORDER BY u.id;'),
        ('i', f"SELECT u.id FROM users u WHERE u.city IN (SELECT p.city FROM profiles p WHERE p.id <= {n}) ORDER BY u.id;"),
        ('it', f'SELECT u.id, u.name FROM users u WHERE u.id IN (SELECT o.user_id FROM orders o GROUP BY o.user_id HAVING COUNT(*) >= {n}) ORDER BY u.id;'),
        ('b', f"SELECT '{city}' IN (SELECT city FROM users WHERE age >= 18);"),
        ('i', f'SELECT id FROM flags WHERE enabled IN (SELECT age >= 18 FROM users WHERE id = {n}) ORDER BY id;'),
        ('i', f'SELECT id FROM users WHERE id IN (SELECT user_id FROM orders WHERE id IN (SELECT id FROM orders WHERE amount >= {n * 30})) ORDER BY id;'),
        ('i', f'SELECT id FROM users WHERE id NOT IN (SELECT user_id FROM orders WHERE FALSE AND amount = {n}) ORDER BY id;'),
    ]: add('in_subqueries', types, sql)
    for types, sql in [
        ('i', f'SELECT u.id FROM users u WHERE EXISTS (SELECT o.id FROM orders o WHERE o.user_id = u.id AND o.amount >= {n * 25}) ORDER BY u.id;'),
        ('it', f'SELECT u.id, u.name FROM users u WHERE NOT EXISTS (SELECT o.id FROM orders o WHERE o.user_id = u.id AND o.amount < {n * 20}) ORDER BY u.id;'),
        ('b', f'SELECT EXISTS (SELECT id FROM users WHERE age > {n * 15});'),
        ('ib', f'SELECT u.id, EXISTS (SELECT o.id FROM orders o WHERE o.user_id = u.id AND o.id > {100 + n}) FROM users u ORDER BY u.id;'),
        ('b', f"SELECT NOT EXISTS (SELECT id FROM users WHERE city = '{city}');"),
        ('i', f'SELECT d.id FROM departments d WHERE EXISTS (SELECT e.id FROM employees e WHERE e.department_id = d.id AND e.salary > {n * 20}) ORDER BY d.id;'),
        ('i', f'SELECT u.id FROM users u WHERE EXISTS (SELECT o.id FROM orders o WHERE o.user_id = u.id AND EXISTS (SELECT f.id FROM flags f WHERE f.id = u.id AND f.id <= {n})) ORDER BY u.id;'),
        ('b', f'SELECT EXISTS (SELECT COUNT(*) FROM orders WHERE amount > {n * 100});'),
        ('b', f'SELECT EXISTS (SELECT id FROM orders WHERE FALSE AND id = {n});'),
        ('i', f'SELECT u.id FROM users u WHERE EXISTS (SELECT o.user_id FROM orders o WHERE o.user_id = u.id GROUP BY o.user_id HAVING COUNT(*) >= {n}) ORDER BY u.id;'),
    ]: add('exists', types, sql)
    for types, sql in [
        ('ii', f'SELECT u.id, q.amount FROM users u CROSS JOIN LATERAL (SELECT o.amount, o.id FROM orders o WHERE o.user_id = u.id AND o.amount >= {n * 20}) q ORDER BY u.id, q.id;'),
        ('iI', f'SELECT u.id, q.amount FROM users u LEFT JOIN LATERAL (SELECT o.amount, o.id FROM orders o WHERE o.user_id = u.id AND o.amount >= {n * 20}) q ON TRUE ORDER BY u.id, q.id;'),
        ('ii', f'SELECT u.id, q.next_age FROM users u CROSS JOIN LATERAL (SELECT u.age + {n} AS next_age) q ORDER BY u.id;'),
        ('ii', f'SELECT u.id, q.total FROM users u JOIN LATERAL (SELECT COUNT(*) AS total FROM orders o WHERE o.user_id = u.id AND o.amount > {n * 10}) q ON TRUE ORDER BY u.id;'),
        ('iI', f'SELECT u.id, q.total FROM users u CROSS JOIN LATERAL (SELECT SUM(o.amount) AS total FROM orders o WHERE o.user_id = u.id AND o.amount > {n * 10}) q ORDER BY u.id;'),
        ('iI', f'SELECT u.id, q.amount FROM users u LEFT JOIN LATERAL (SELECT o.amount FROM orders o WHERE o.user_id = u.id ORDER BY o.amount DESC, o.id LIMIT {n}) q ON TRUE ORDER BY u.id, q.amount;'),
        ('iit', f"SELECT u.id, q.id, q.status FROM users u CROSS JOIN LATERAL (SELECT o.id, o.status FROM orders o WHERE o.user_id = u.id AND u.city <> '{city}') q ORDER BY u.id, q.id;"),
        ('ii', f'SELECT d.id, q.id FROM departments d JOIN LATERAL (SELECT e.id FROM employees e WHERE e.department_id = d.id AND e.salary >= {n * 15}) q ON q.id > 0 ORDER BY d.id, q.id;'),
        ('ii', f'SELECT u.id, q.id FROM users u CROSS JOIN LATERAL (SELECT f.id FROM flags f WHERE f.id <= {n}) q ORDER BY u.id, q.id;'),
        ('iii', f'SELECT u.id, a.x, b.y FROM users u CROSS JOIN LATERAL (SELECT u.age + {n} AS x) a CROSS JOIN LATERAL (SELECT a.x * 2 AS y) b ORDER BY u.id;'),
    ]: add('lateral', types, sql)
    for types, sql in [
        ('itR', f'SELECT id, city, rating FROM users JOIN profiles USING (id, city) WHERE id <= {n} ORDER BY id;'),
        ('it', f'SELECT id, label FROM users JOIN tags USING (id) WHERE age > {n * 10} ORDER BY id;'),
        ('iT', f'SELECT id, label FROM users LEFT JOIN tags USING (id) WHERE age >= {n * 10} ORDER BY id;'),
        ('iT', f'SELECT id, users.name FROM users RIGHT JOIN tags USING (id) WHERE id <= {n + 5} ORDER BY id;'),
        ('iTT', f'SELECT id, users.name, tags.label FROM users FULL JOIN tags USING (id) WHERE id >= {n} ORDER BY id;'),
        ('ii', f'SELECT u.id, t.id FROM users u JOIN tags t USING (id) WHERE u.age > {n * 5} ORDER BY u.id;'),
        ('iittT', f'SELECT * FROM users LEFT JOIN tags USING (id) WHERE id <= {n} ORDER BY id;'),
        ('IITt', f'SELECT u.id, u.age, u.name, t.label FROM users u RIGHT JOIN tags t USING (id) WHERE t.id >= {n} ORDER BY t.id;'),
        ('i', f'SELECT id FROM users JOIN tags USING (id) JOIN profiles USING (id) WHERE rating > {n}.0 ORDER BY id;'),
        ('ititR', f'SELECT * FROM users JOIN profiles USING (id, city) WHERE age > {n * 10} ORDER BY id;'),
    ]: add('using_joins', types, sql)
    for types, sql in [
        ('it', f'SELECT id, label FROM users NATURAL JOIN tags WHERE age > {n * 10} ORDER BY id;'),
        ('iT', f'SELECT id, label FROM users NATURAL LEFT JOIN tags WHERE age > {n * 10} ORDER BY id;'),
        ('iT', f'SELECT id, users.name FROM users NATURAL RIGHT JOIN tags WHERE id <= {n + 5} ORDER BY id;'),
        ('iTT', f'SELECT id, users.name, tags.label FROM users NATURAL FULL JOIN tags WHERE id >= {n} ORDER BY id;'),
        ('itR', f'SELECT id, city, rating FROM users NATURAL JOIN profiles WHERE age > {n * 10} ORDER BY id;'),
        ('itR', f'SELECT id, city, rating FROM users NATURAL LEFT JOIN profiles WHERE id <= {n} ORDER BY id;'),
        ('iittT', f'SELECT * FROM users NATURAL LEFT JOIN tags WHERE id <= {n} ORDER BY id;'),
        ('ititR', f'SELECT * FROM users NATURAL JOIN profiles WHERE age >= {n * 10} ORDER BY id;'),
        ('ii', f'SELECT u.id, t.id FROM users u NATURAL JOIN tags t WHERE u.age > {n * 10} ORDER BY u.id;'),
        ('i', f'SELECT id FROM users NATURAL JOIN tags NATURAL JOIN profiles WHERE rating > {n}.0 ORDER BY id;'),
    ]: add('natural_joins', types, sql)
    for category, op in [('intersect', 'INTERSECT'), ('except', 'EXCEPT')]:
        for types, sql in [
            ('i', f'SELECT id FROM users WHERE age > {n * 10} {op} SELECT user_id FROM orders ORDER BY 1;'),
            ('i', f'SELECT user_id FROM orders {op} ALL SELECT id FROM users WHERE id <= {n} ORDER BY 1;'),
            ('t', f"SELECT city FROM users {op} SELECT city FROM profiles WHERE city <> '{city}' ORDER BY 1;"),
            ('it', f'SELECT id, name FROM users WHERE id <= {n} {op} SELECT id, name FROM employees ORDER BY 1, 2;'),
            ('i', f'SELECT {n} {op} SELECT id FROM users ORDER BY 1;'),
            ('i', f'SELECT id FROM users WHERE FALSE {op} SELECT id FROM flags WHERE id <= {n} ORDER BY 1;'),
            ('i', f'SELECT id FROM users {op} SELECT id FROM flags WHERE FALSE AND id = {n} ORDER BY 1;'),
            ('i', f'SELECT id FROM users {op} SELECT user_id FROM orders {op} SELECT id FROM flags WHERE id <= {n} ORDER BY 1;'),
            ('t', f"SELECT city FROM users {op} ALL SELECT city FROM profiles WHERE id < {n + 3} ORDER BY 1;"),
            ('i', f'SELECT id FROM users {op} SELECT user_id FROM orders ORDER BY 1 LIMIT {n};'),
        ]: add(category, types, sql)
    for types, sql in [
        ('it', f"INSERT INTO departments (id, name) VALUES ({n}, 'Updated {n}') ON CONFLICT (id) DO NOTHING RETURNING id, name;"),
        ('it', f"INSERT INTO departments VALUES ({n}, 'Updated {n}') ON CONFLICT (id) DO UPDATE SET name = EXCLUDED.name RETURNING id, name;"),
        ('ii', f"INSERT INTO users VALUES ({n}, {20 + n}, 'New {n}', 'Oslo') ON CONFLICT (id) DO UPDATE SET age = EXCLUDED.age RETURNING id, age;"),
        ('it', f"INSERT INTO users VALUES ({n}, {20 + n}, 'New {n}', 'Oslo') ON CONFLICT (id) DO UPDATE SET name = EXCLUDED.name, city = EXCLUDED.city RETURNING id, city;"),
        ('i', f"INSERT INTO departments VALUES ({20 + n}, 'Inserted {n}') ON CONFLICT DO NOTHING RETURNING id;"),
        ('i', f"INSERT INTO orders VALUES ({100 + n}, {n}, {n * 10}, 'paid') ON CONFLICT (id) DO UPDATE SET amount = orders.amount + EXCLUDED.amount RETURNING amount;"),
        ('ib', f"INSERT INTO flags VALUES ({n}, TRUE, 'Flag {n}') ON CONFLICT (id) DO UPDATE SET enabled = NOT flags.enabled RETURNING id, enabled;"),
        ('it', f"INSERT INTO tags VALUES ({n}, 'Tag {n}') ON CONFLICT (id) DO UPDATE SET label = EXCLUDED.label WHERE tags.id > 1 RETURNING id, label;"),
        ('i', f"INSERT INTO departments VALUES ({n}, 'Existing {n}'), ({30 + n}, 'New {n}') ON CONFLICT (id) DO NOTHING RETURNING id;"),
        ('', f"INSERT INTO departments VALUES ({n}, 'No output {n}') ON CONFLICT (id) DO UPDATE SET name = EXCLUDED.name;"),
    ]: add('upsert', types, sql)
    for types, sql in [
        ('iitt', f'INSERT INTO archive SELECT id, age, name, city FROM users WHERE age >= {n * 10} RETURNING *;'),
        ('it', f'INSERT INTO archive (id, age, name, city) SELECT id, age, name, city FROM users WHERE id <= {n} RETURNING id, name;'),
        ('', f'INSERT INTO archive (id, age, name, city) SELECT id, age + {n}, name, city FROM users;'),
        ('it', f'INSERT INTO tags (id, label) SELECT id + {100 + n}, name FROM users WHERE age >= 18 RETURNING id, label;'),
        ('it', f'INSERT INTO departments (id, name) SELECT id + {100 + n}, city FROM users WHERE id <= {n} RETURNING id, name;'),
        ('ii', f'INSERT INTO archive SELECT id, age * {n}, name, city FROM users WHERE id IN (SELECT user_id FROM orders) RETURNING id, age;'),
        ('it', f"INSERT INTO archive SELECT id, age, name, city FROM users WHERE city = '{city}' RETURNING id, city;"),
        ('i', f'INSERT INTO archive SELECT id, age, name, city FROM users WHERE FALSE AND id = {n} RETURNING id;'),
        ('ii', f'INSERT INTO archive (age, id, city, name) SELECT age + {n}, id, city, name FROM users RETURNING id, age;'),
        ('it', f'INSERT INTO tags SELECT id + {200 + n}, name FROM departments ORDER BY id LIMIT {n} RETURNING id, label;'),
    ]: add('insert_select', types, sql)

# Fifty NULL cases deliberately cover contextual typing, three-valued logic,
# casts, null-preserving arithmetic, predicates, aggregates, and DML storage.
NULL_CASES = '''
T | SELECT NULL;
I | SELECT NULL::INTEGER;
T | SELECT CAST(NULL AS TEXT);
B | SELECT NULL::BOOLEAN;
R | SELECT NULL::DOUBLE PRECISION;
I | SELECT NULL + 1;
I | SELECT 2 - NULL;
R | SELECT NULL * 2.5;
I | SELECT 10 / NULL;
B | SELECT NULL = 1;
B | SELECT 1 <> NULL;
B | SELECT NULL < 4;
B | SELECT NULL >= 4.5;
B | SELECT NULL = 'hello';
B | SELECT TRUE AND NULL;
B | SELECT FALSE OR NULL;
B | SELECT NOT NULL;
b | SELECT NULL IS NULL;
b | SELECT NULL IS NOT NULL;
b | SELECT (NULL + 1) IS NULL;
B | SELECT 1 IN (NULL, 2);
B | SELECT 2 IN (NULL, 2);
B | SELECT 1 NOT IN (NULL, 2);
B | SELECT NULL IN (1, 2);
B | SELECT NULL LIKE 'a%';
B | SELECT 'Alice' ILIKE NULL;
B | SELECT NULL BETWEEN 1 AND 3;
iT | SELECT id, NULL FROM users ORDER BY id;
iR | SELECT id, score FROM scratch ORDER BY id;
iT | SELECT id, name FROM scratch ORDER BY id;
iB | SELECT id, enabled FROM scratch ORDER BY id;
i | SELECT id FROM scratch WHERE name IS NULL ORDER BY id;
i | SELECT id FROM scratch WHERE score IS NOT NULL ORDER BY id;
i | SELECT id FROM scratch WHERE enabled IS NULL ORDER BY id;
i | SELECT id FROM scratch WHERE enabled = NULL ORDER BY id;
iR | SELECT id, score + 1.25 FROM scratch ORDER BY id;
iB | SELECT id, name LIKE 'a%' FROM scratch ORDER BY id;
i | SELECT COUNT(name) FROM scratch;
R | SELECT SUM(score) FROM scratch;
T | SELECT MIN(name) FROM scratch;
i | SELECT id FROM users WHERE id IN (SELECT NULL::INTEGER) ORDER BY id;
i | SELECT id FROM users WHERE id NOT IN (SELECT NULL::INTEGER) ORDER BY id;
B | SELECT NULL IN (SELECT id FROM users);
iTRB | INSERT INTO scratch VALUES (20, NULL, NULL, NULL) RETURNING *;
iT | INSERT INTO scratch (id, name) VALUES (21, NULL) RETURNING id, name;
iR | UPDATE scratch SET score = NULL WHERE id = 1 RETURNING id, score;
iB | UPDATE scratch SET enabled = NULL WHERE id = 2 RETURNING id, enabled;
i | DELETE FROM scratch WHERE name IS NULL RETURNING id;
i | SELECT id FROM scratch WHERE score IS NULL OR score > 2.0 ORDER BY id;
bb | SELECT (NULL = NULL) IS NULL, (NULL IS NULL) IS NOT NULL;
'''
for line in NULL_CASES.strip().splitlines():
    types, sql = line.split(' | ', 1)
    add('nulls', types, sql)

for literal in ('0.125', '.5', '2.', '1.25e2', '3E-2'):
    for types, sql in [
        ('r', f'SELECT {literal};'), ('r', f'SELECT -{literal};'),
        ('r', f'SELECT +{literal};'), ('r', f'SELECT {literal} + 2;'),
        ('r', f'SELECT 5 * {literal};'), ('r', f'SELECT {literal} / 2.0;'),
        ('b', f'SELECT {literal} > 0.25;'),
        ('ir', f'SELECT id, age + {literal} FROM users ORDER BY id;'),
        ('i', f'SELECT id FROM orders WHERE amount >= {literal} ORDER BY id;'),
        ('iR', f'SELECT id, score + {literal} FROM scratch ORDER BY id;'),
    ]: add('floating', types, sql)

PARAMETER_TEMPLATES = [
    ('i', 'i', [3], 'SELECT {p1} AS integer_parameter;'),
    ('tt', 't', ['Paris'], "SELECT {p1} AS text_parameter, '?' AS question_text;"),
    ('b', 'b', [True], 'SELECT {p1} AS boolean_parameter;'),
    ('r', 'r', [1.25], 'SELECT {p1} AS real_parameter;'),
    ('i', 'i', [2], 'SELECT id FROM users WHERE id >= {p1} ORDER BY id;'),
    ('it', 't', ['Paris'], 'SELECT id, name FROM users WHERE city = {p1} ORDER BY id;'),
    ('i', 'b', [True], 'SELECT id FROM flags WHERE enabled = {p1} ORDER BY id;'),
    ('i', 'r', [50.5], 'SELECT id FROM orders WHERE amount > {p1} ORDER BY id;'),
    ('ir', 'r', [0.5], 'SELECT id, age + {p1} FROM users ORDER BY id;'),
    ('b', 'i', [3], 'SELECT {p1} IN (SELECT user_id FROM orders);'),
    ('b', 'i', [2], 'SELECT EXISTS (SELECT id FROM users WHERE id = {p1});'),
    ('i', 'ii', [18, 40], 'SELECT id FROM users WHERE age BETWEEN {p1} AND {p2} ORDER BY id;'),
    ('it', 'ti', ['Paris', 1], 'SELECT id, name FROM users WHERE city = {p1} AND id > {p2} ORDER BY id;'),
    ('i', 'iii', [1, 3, 5], 'SELECT id FROM users WHERE id IN ({p1}, {p2}, {p3}) ORDER BY id;'),
    ('b', 'tt', ['Alice', 'a%'], 'SELECT {p1} ILIKE {p2};'),
    ('r', 'rr', [1.25, 2.5], 'SELECT {p1} + {p2};'),
    ('ii', 'ii', [1, 2], 'SELECT {p1}, {p2};'),
    ('t', 'i', [42], 'SELECT {p1}::TEXT;'),
    ('i', 't', ['42'], 'SELECT CAST({p1} AS INTEGER);'),
    ('i', 'i', [20], 'SELECT COUNT(*) FILTER (WHERE age >= {p1}) FROM users;'),
    ('i', 't', ['Paris'], 'SELECT u.id FROM users u CROSS JOIN LATERAL (SELECT u.city AS city) q WHERE q.city = {p1} ORDER BY u.id;'),
    ('it', 'it', [40, 'Inserted'], 'INSERT INTO departments VALUES ({p1}, {p2}) RETURNING id, name;'),
    ('ii', 'ii', [50, 1], 'UPDATE users SET age = {p1} WHERE id = {p2} RETURNING id, age;'),
    ('i', 'i', [2], 'DELETE FROM users WHERE id = {p1} RETURNING id;'),
    ('it', 'it', [1, 'Updated'], 'INSERT INTO departments VALUES ({p1}, {p2}) ON CONFLICT (id) DO UPDATE SET name = EXCLUDED.name RETURNING id, name;'),
]
for positional in (True, False):
    for parameter_index, (types, params, values, template) in enumerate(PARAMETER_TEMPLATES, 1):
        if parameter_index == 17 and positional:
            add('placeholders', 'iii', 'SELECT $2, $1, $2;', 'ii', [1, 2])
            continue
        mapping = {f'p{i}': f'${i}' if positional else '?' for i in range(1, 4)}
        add('placeholders', types, template.format(**mapping), params, values)

for n, (type_name, default) in enumerate((('INTEGER', '0'), ('TEXT', "'ready'"),
                                        ('BOOLEAN', 'FALSE'), ('REAL', '1.5'),
                                        ('DOUBLE PRECISION', '2.5e1')), 1):
    for suffix, body in [
        ('plain', f'value {type_name}'),
        ('required', f'value {type_name} NOT NULL'),
        ('default', f'value {type_name} DEFAULT {default}'),
        ('primary', f'id INTEGER PRIMARY KEY, value {type_name}'),
        ('unique', f'id INTEGER UNIQUE, value {type_name}'),
        ('table_primary', f'id INTEGER NOT NULL, value {type_name}, PRIMARY KEY (id)'),
        ('table_unique', f'id INTEGER NOT NULL, value {type_name}, UNIQUE (id)'),
        ('composite', f'id INTEGER NOT NULL, revision INTEGER NOT NULL, value {type_name}, PRIMARY KEY (id, revision)'),
        ('null', f'id INTEGER PRIMARY KEY, value {type_name} NULL DEFAULT NULL'),
        ('quoted', f'"record id" INTEGER PRIMARY KEY, "stored value" {type_name}'),
    ]:
        add('create_table', '', f'CREATE TABLE made_{n}_{suffix} ({body});')
    for sql in [
        f'ALTER TABLE scratch ADD COLUMN added_{n} {type_name};',
        f'ALTER TABLE scratch ADD added_default_{n} {type_name} DEFAULT {default};',
        f'ALTER TABLE scratch ADD COLUMN added_required_{n} {type_name} NOT NULL DEFAULT {default};',
        f'ALTER TABLE scratch ADD COLUMN IF NOT EXISTS added_optional_{n} {type_name};',
        f'ALTER TABLE scratch RENAME COLUMN name TO renamed_name_{n};',
        f'ALTER TABLE scratch RENAME COLUMN score TO renamed_score_{n};',
        f'ALTER TABLE scratch RENAME TO renamed_scratch_{n};',
        f'ALTER TABLE scratch ALTER COLUMN name SET DEFAULT \'default {n}\';',
        f'ALTER TABLE scratch ADD COLUMN added_key_{n} INTEGER UNIQUE;',
        f'ALTER TABLE scratch DROP COLUMN IF EXISTS missing_{n};',
    ]: add('alter_table', '', sql)
    for suffix in ('a', 'b', 'c', 'd', 'e'):
        add('drop_table', '', f'DROP TABLE IF EXISTS absent_{n}_{suffix};')
    for table in ('scratch', 'archive', 'profiles', 'tags', 'flags'):
        # Comments carry a scenario label; SQL structure varies through optional
        # IF EXISTS and behavior clauses without manufacturing unknown tables.
        clause = ('', ' IF EXISTS', '', ' IF EXISTS', '')[n - 1]
        behavior = ('', '', ' RESTRICT', ' RESTRICT', ' CASCADE')[n - 1]
        add('drop_table', '', f'DROP TABLE{clause} {table}{behavior};')

# Compound precedence and parenthesized operands complement the single-operator
# cases and catch renderers that accidentally reassociate set expressions.
for category, index, sql in [
    ('intersect', 44, 'SELECT 1 UNION SELECT 2 INTERSECT SELECT 2 ORDER BY 1;'),
    ('intersect', 45, 'SELECT 1 INTERSECT SELECT 1 UNION SELECT 2 ORDER BY 1;'),
    ('intersect', 46, '(SELECT 1 UNION SELECT 2) INTERSECT SELECT 2 ORDER BY 1;'),
    ('except', 44, 'SELECT 1 UNION SELECT 2 EXCEPT SELECT 1 ORDER BY 1;'),
    ('except', 45, 'SELECT 1 EXCEPT SELECT 1 UNION SELECT 2 ORDER BY 1;'),
    ('except', 46, 'SELECT 1 EXCEPT (SELECT 1 EXCEPT SELECT 1);'),
]:
    EXAMPLES[category][index - 1].update(sql=sql, types='i')
EXAMPLES['create_table'][10]['sql'] = EXAMPLES['create_table'][10]['sql'].replace('CREATE TABLE ', 'CREATE TABLE IF NOT EXISTS ')
EXAMPLES['create_table'][40]['sql'] = 'CREATE TABLE IF NOT EXISTS users (id INTEGER);'

# Expand ALTER beyond ADD/RENAME with real drops, casts, nullability/default
# transitions, multiple actions, and an existing-column IF NOT EXISTS no-op.
for index, sql in {
    14: 'ALTER TABLE scratch DROP COLUMN score;',
    16: 'ALTER TABLE scratch DROP COLUMN enabled RESTRICT;',
    19: 'ALTER TABLE scratch ALTER COLUMN score TYPE DOUBLE PRECISION;',
    20: 'ALTER TABLE scratch ALTER COLUMN name DROP DEFAULT;',
    24: 'ALTER TABLE scratch ALTER COLUMN id SET NOT NULL;',
    26: 'ALTER TABLE scratch ALTER COLUMN name DROP NOT NULL;',
    29: 'ALTER TABLE scratch ALTER COLUMN name TYPE TEXT;',
    30: 'ALTER TABLE scratch DROP COLUMN name;',
    34: 'ALTER TABLE scratch DROP COLUMN score CASCADE;',
    36: 'ALTER TABLE scratch ALTER COLUMN score DROP DEFAULT;',
    39: 'ALTER TABLE scratch ADD COLUMN extra_flag BOOLEAN DEFAULT FALSE, ADD COLUMN extra_count INTEGER DEFAULT 0;',
    40: 'ALTER TABLE scratch ALTER COLUMN score TYPE NUMERIC(10, 2);',
    44: 'ALTER TABLE scratch ALTER COLUMN enabled DROP DEFAULT;',
    46: 'ALTER TABLE scratch ALTER COLUMN enabled SET DEFAULT TRUE;',
    49: 'ALTER TABLE scratch ALTER COLUMN score SET DEFAULT 1.25;',
    50: 'ALTER TABLE scratch ADD COLUMN IF NOT EXISTS name TEXT;',
}.items():
    EXAMPLES['alter_table'][index - 1]['sql'] = sql


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--check', action='store_true')
    args = parser.parse_args()
    for category, cases in EXAMPLES.items():
        assert len(cases) == 50, (category, len(cases))
        assert len({case['sql'] for case in cases}) == 50, category
        assert all(len(case['parameters']) == len(case['values']) for case in cases)
    outputs = {f'{category}.sql': '\n'.join(case['sql'] for case in cases) + '\n'
               for category, cases in EXAMPLES.items()}
    outputs['schema.json'] = json.dumps(SCHEMA, indent=2) + '\n'
    outputs['cases.json'] = json.dumps(EXAMPLES, indent=2) + '\n'
    stale = []
    for filename, content in outputs.items():
        path = FIXTURES / filename
        if args.check:
            if not path.exists() or path.read_text() != content:
                stale.append(str(path.relative_to(ROOT)))
        else:
            FIXTURES.mkdir(parents=True, exist_ok=True)
            path.write_text(content)
    if stale:
        parser.exit(1, 'Stale advanced fixtures: ' + ', '.join(stale) + '\n')
    print(f"{'Checked' if args.check else 'Generated'} 50 examples per advanced class (750 total).")


if __name__ == '__main__':
    main()
