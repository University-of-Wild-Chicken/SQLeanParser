#!/usr/bin/env python3
"""Generate 50 examples for each of six PostgreSQL syntax classes.

Type expectations are specified with the examples, independently of the parser.
Lowercase i/t/b/r denote primitive types; uppercase letters denote nullable types.
Use --check to verify reproducible checked-in fixtures without writing files.
"""
from __future__ import annotations

import argparse
import json
from pathlib import Path

from generate_relational_examples import SCHEMA

ROOT = Path(__file__).resolve().parents[1]
FIXTURE_DIR = ROOT / 'fixtures/postgresql'


def examples(source: str) -> list[tuple[str, str]]:
    rows = [tuple(line.strip().split(' | ', 1)) for line in source.strip().splitlines() if line.strip()]
    assert len(rows) == 50, len(rows)
    assert len({sql for _, sql in rows}) == 50
    assert all(set(types) <= set('itbrITBR') for types, _ in rows)
    return rows


EXAMPLES = {
'distinct_on': examples("""
tt | SELECT DISTINCT ON (city) city, name FROM users ORDER BY city, age DESC, id;
tt | SELECT DISTINCT ON (city) city, name FROM users ORDER BY city, age, id;
ti | SELECT DISTINCT ON (city) city, age FROM users ORDER BY city, age DESC, id;
i | SELECT DISTINCT ON (age) age FROM users ORDER BY age;
iit | SELECT DISTINCT ON (city) id, age, name FROM users ORDER BY city, age DESC, id;
ii | SELECT DISTINCT ON (user_id) user_id, amount FROM orders ORDER BY user_id, amount DESC, id;
iit | SELECT DISTINCT ON (status) id, amount, status FROM orders ORDER BY status, amount DESC, id;
tt | SELECT DISTINCT ON (city, age) city, name FROM users ORDER BY city, age, id;
ii | SELECT DISTINCT ON (user_id, status) user_id, amount FROM orders ORDER BY user_id, status, amount DESC, id;
iit | SELECT DISTINCT ON (department_id) id, salary, name FROM employees ORDER BY department_id, salary DESC, id;
tb | SELECT DISTINCT ON (enabled) label, enabled FROM flags ORDER BY enabled, id;
t | SELECT DISTINCT ON (name) name FROM departments ORDER BY name;
ti | SELECT DISTINCT ON (u.city) u.city, u.id FROM users u ORDER BY u.city, u.id;
ii | SELECT DISTINCT ON (o.user_id) o.user_id, o.id FROM orders AS o ORDER BY o.user_id, o.id DESC;
ii | SELECT DISTINCT ON (age + 1) id, age FROM users ORDER BY age + 1, id;
t | SELECT DISTINCT ON (city) city AS location FROM users ORDER BY city;
ti | SELECT DISTINCT ON (city) city AS location, age AS years FROM users ORDER BY location, years DESC, id;
ii | SELECT DISTINCT ON (user_id) user_id AS customer, amount AS total FROM orders ORDER BY customer, total DESC, id;
ti | SELECT DISTINCT ON (city) city, id FROM users WHERE age >= 18 ORDER BY city, id;
ii | SELECT DISTINCT ON (user_id) user_id, amount FROM orders WHERE status = 'paid' ORDER BY user_id, amount DESC, id;
tt | SELECT DISTINCT ON (city) city, name FROM users ORDER BY city DESC, age DESC, id;
tt | SELECT DISTINCT ON (city) city, name FROM users ORDER BY city, id LIMIT 2;
tt | SELECT DISTINCT ON (city) city, name FROM users ORDER BY city, id LIMIT 2 OFFSET 1;
iitt | SELECT DISTINCT ON (city) * FROM users ORDER BY city, id;
iitt | SELECT DISTINCT ON (u.city) u.* FROM users u ORDER BY u.city, u.id;
tI | SELECT DISTINCT ON (u.city) u.city, o.amount FROM users u LEFT JOIN orders o ON u.id = o.user_id ORDER BY u.city, o.amount DESC, u.id, o.id;
ii | SELECT DISTINCT ON (u.id) u.id, o.amount FROM users u JOIN orders o ON u.id = o.user_id ORDER BY u.id, o.amount DESC, o.id;
iti | SELECT DISTINCT ON (d.id) d.id, e.name, e.salary FROM departments d JOIN employees e ON d.id = e.department_id ORDER BY d.id, e.salary DESC, e.id;
ti | SELECT DISTINCT ON (city) city, COUNT(*) AS people FROM users GROUP BY city ORDER BY city;
iI | SELECT DISTINCT ON (user_id) user_id, SUM(amount) AS total FROM orders GROUP BY user_id ORDER BY user_id;
tR | SELECT DISTINCT ON (city) city, AVG(age) AS average_age FROM users GROUP BY city ORDER BY city;
t | WITH places AS (SELECT city FROM users) SELECT DISTINCT ON (city) city FROM places ORDER BY city;
ii | WITH amounts AS (SELECT user_id, amount FROM orders) SELECT DISTINCT ON (user_id) user_id, amount FROM amounts ORDER BY user_id, amount DESC;
tt | SELECT DISTINCT ON (q.city) q.city, q.name FROM (SELECT city, name, id FROM users) q ORDER BY q.city, q.id;
i | SELECT DISTINCT ON (q.user_id) q.user_id FROM (SELECT user_id FROM orders) q ORDER BY q.user_id;
i | SELECT DISTINCT ON (1) 1;
it | SELECT DISTINCT ON (1) 1 AS id, 'constant' AS label ORDER BY 1;
b | SELECT DISTINCT ON (NOT FALSE) TRUE AS enabled;
tt | SELECT DISTINCT ON (city, name) city, name FROM users ORDER BY city, name;
ii | SELECT DISTINCT ON (department_id, salary) department_id, salary FROM employees ORDER BY department_id, salary;
it | SELECT DISTINCT ON (id) id, name FROM users ORDER BY id DESC;
bi | SELECT DISTINCT ON (enabled) enabled, id FROM flags WHERE id > 1 ORDER BY enabled, id;
t | SELECT DISTINCT ON (city) city FROM users WHERE FALSE ORDER BY city;
tt | SELECT DISTINCT ON (city) city AS "home city", name FROM users ORDER BY "home city", id;
ii | SELECT DISTINCT ON (user_id) user_id, amount FROM orders ORDER BY user_id DESC, amount DESC, id;
tt | SELECT DISTINCT ON (city) city, name FROM users ORDER BY city NULLS FIRST, id;
ti | SELECT DISTINCT ON (u.city) u.city, u.id FROM users AS u ORDER BY u.city DESC NULLS LAST, u.id;
ii | SELECT DISTINCT ON (age * 2) age, id FROM users ORDER BY age * 2, id;
tt | SELECT DISTINCT ON (city, age) city, name FROM users ORDER BY age, city, id;
iti | SELECT DISTINCT ON (user_id, status) user_id, status, amount FROM orders ORDER BY status, user_id, amount DESC, id;
"""),
'aggregate_filter': examples("""
i | SELECT COUNT(*) FILTER (WHERE age >= 18) FROM users;
i | SELECT COUNT(*) FILTER (WHERE age < 18) AS minors FROM users;
i | SELECT COUNT(id) FILTER (WHERE city = 'Paris') FROM users;
i | SELECT COUNT(DISTINCT city) FILTER (WHERE age > 20) FROM users;
I | SELECT SUM(amount) FILTER (WHERE status = 'paid') FROM orders;
R | SELECT AVG(age) FILTER (WHERE age >= 18) FROM users;
I | SELECT MIN(age) FILTER (WHERE city = 'Paris') FROM users;
I | SELECT MAX(salary) FILTER (WHERE department_id = 1) FROM employees;
T | SELECT MIN(name) FILTER (WHERE age >= 18) FROM users;
T | SELECT MAX(name) FILTER (WHERE city = 'Rome') FROM users;
ii | SELECT COUNT(*) FILTER (WHERE enabled), COUNT(*) FILTER (WHERE NOT enabled) FROM flags;
II | SELECT SUM(amount) FILTER (WHERE status = 'paid'), SUM(amount) FILTER (WHERE status = 'pending') FROM orders;
iI | SELECT COUNT(*) FILTER (WHERE TRUE), SUM(age) FILTER (WHERE FALSE) FROM users;
i | SELECT COUNT(*) FILTER (WHERE FALSE) FROM users;
i | SELECT COUNT(*) FILTER (WHERE TRUE);
I | SELECT SUM(5) FILTER (WHERE TRUE);
R | SELECT AVG(8) FILTER (WHERE FALSE);
ti | SELECT city, COUNT(*) FILTER (WHERE age >= 18) FROM users GROUP BY city ORDER BY city;
iI | SELECT user_id, SUM(amount) FILTER (WHERE status = 'paid') FROM orders GROUP BY user_id ORDER BY user_id;
iR | SELECT department_id, AVG(salary) FILTER (WHERE salary >= 80) FROM employees GROUP BY department_id ORDER BY department_id;
bi | SELECT enabled, COUNT(*) FILTER (WHERE id > 1) FROM flags GROUP BY enabled ORDER BY enabled;
ti | SELECT city, COUNT(DISTINCT age) FILTER (WHERE age > 20) FROM users GROUP BY city ORDER BY city;
ti | SELECT city, COUNT(*) FILTER (WHERE age > 20) AS adults FROM users GROUP BY city HAVING COUNT(*) FILTER (WHERE age > 20) > 1 ORDER BY city;
ti | SELECT city, COUNT(*) FILTER (WHERE age >= 18) AS adults FROM users GROUP BY city ORDER BY adults DESC, city;
i | SELECT COUNT(*) FILTER (WHERE age >= 18) + 1 FROM users;
I | SELECT SUM(amount) FILTER (WHERE status = 'paid') * 2 FROM orders;
i | SELECT COUNT(*) FILTER (WHERE age > 20 AND city = 'Paris') FROM users;
i | SELECT COUNT(*) FILTER (WHERE city = 'Paris' OR city = 'Rome') FROM users;
i | SELECT COUNT(*) FILTER (WHERE NOT (age < 18)) FROM users;
i | SELECT COUNT(*) FILTER (WHERE u.age > 20) FROM users u;
iI | SELECT u.id, SUM(o.amount) FILTER (WHERE o.status = 'paid') FROM users u LEFT JOIN orders o ON o.user_id = u.id GROUP BY u.id ORDER BY u.id;
ii | SELECT u.id, COUNT(*) FILTER (WHERE o.id IS NULL) FROM users u LEFT JOIN orders o ON o.user_id = u.id GROUP BY u.id ORDER BY u.id;
ii | SELECT u.id, COUNT(o.id) FILTER (WHERE o.amount > 50) FROM users u LEFT JOIN orders o ON o.user_id = u.id GROUP BY u.id ORDER BY u.id;
I | SELECT SUM(o.amount) FILTER (WHERE u.age >= 18) FROM users u JOIN orders o ON u.id = o.user_id;
i | SELECT COUNT(DISTINCT o.user_id) FILTER (WHERE o.status = 'paid') FROM orders o;
I | SELECT SUM(DISTINCT amount) FILTER (WHERE status = 'paid') FROM orders;
R | SELECT AVG(DISTINCT age) FILTER (WHERE city = 'Paris') FROM users;
i | WITH adults AS (SELECT age FROM users) SELECT COUNT(*) FILTER (WHERE age >= 18) FROM adults;
I | SELECT SUM(q.amount) FILTER (WHERE q.amount > 50) FROM (SELECT amount FROM orders) q;
i | SELECT COUNT(*) FILTER (WHERE age >= 18) FROM users WHERE city = 'Paris';
i | SELECT COUNT(*) FILTER (WHERE age >= 18) FROM users HAVING COUNT(*) > 0;
ti | SELECT city, COUNT(*) FILTER (WHERE age >= 18) FROM users GROUP BY city HAVING COUNT(*) FILTER (WHERE age >= 18) >= 0 ORDER BY city;
II | SELECT MIN(salary) FILTER (WHERE department_id = 1), MAX(salary) FILTER (WHERE department_id = 2) FROM employees;
TT | SELECT MIN(label) FILTER (WHERE enabled), MAX(label) FILTER (WHERE NOT enabled) FROM flags;
i | SELECT COUNT(*) FILTER (WHERE name = 'O''Brien') FROM users;
i | SELECT COUNT(*) FILTER (WHERE id + 1 > 3) FROM users;
i | SELECT COUNT(*) FILTER (WHERE age = 17) FROM users;
i | SELECT COUNT(*) FILTER (WHERE id IS NOT NULL) FROM users;
i | SELECT COUNT(*) FILTER (WHERE enabled = TRUE) FROM flags;
i | SELECT COUNT(*) FILTER (WHERE FALSE) AS empty_count WHERE FALSE;
"""),
'casts': examples("""
i | SELECT CAST('42' AS INTEGER);
i | SELECT '42'::INT;
t | SELECT CAST(42 AS TEXT);
t | SELECT 42::TEXT;
b | SELECT CAST('true' AS BOOLEAN);
b | SELECT 'false'::BOOL;
r | SELECT CAST(7 AS REAL);
r | SELECT 7::DOUBLE PRECISION;
i | SELECT CAST(TRUE AS INTEGER);
b | SELECT 1::BOOLEAN;
i | SELECT FALSE::INT;
b | SELECT CAST(0 AS BOOL);
t | SELECT TRUE::TEXT;
t | SELECT CAST(FALSE AS TEXT);
r | SELECT CAST('3.5' AS REAL);
r | SELECT '2.25'::DOUBLE PRECISION;
i | SELECT CAST(CAST('2.5' AS REAL) AS INTEGER);
t | SELECT CAST(CAST('12' AS INTEGER) AS TEXT);
t | SELECT '1.23456789012345'::DOUBLE PRECISION::TEXT;
t | SELECT '1.23456789012345'::REAL::TEXT;
t | SELECT id::TEXT FROM users ORDER BY id;
r | SELECT CAST(age AS DOUBLE PRECISION) FROM users ORDER BY id;
iit | SELECT id, CAST(age AS INTEGER), name FROM users ORDER BY id;
t | SELECT enabled::TEXT FROM flags ORDER BY id;
i | SELECT CAST(enabled AS INT) FROM flags ORDER BY id;
b | SELECT CAST(id AS BOOL) FROM flags ORDER BY id;
t | SELECT CAST(amount AS TEXT) FROM orders ORDER BY id;
r | SELECT amount::REAL FROM orders ORDER BY id;
tt | SELECT name, CAST(salary AS TEXT) FROM employees ORDER BY id;
tr | SELECT city, age::DOUBLE PRECISION FROM users ORDER BY id;
i | SELECT CAST('2' AS INT) + 3;
b | SELECT CAST('5' AS INT) > 4;
r | SELECT CAST(2 AS REAL) + CAST(3 AS REAL);
r | SELECT 2::REAL / 4::REAL;
i | SELECT -(CAST('9' AS INT));
b | SELECT NOT CAST('false' AS BOOLEAN);
b | SELECT CAST('1' AS INT) = CAST('1' AS INTEGER);
t | SELECT (1 + 2)::TEXT;
i | SELECT CAST((-5) AS INTEGER);
t | SELECT CAST('O''Brien' AS TEXT);
T | SELECT CAST(SUM(amount) AS TEXT) FROM orders;
R | SELECT CAST(SUM(amount) AS DOUBLE PRECISION) FROM orders;
I | SELECT AVG(age)::INTEGER FROM users;
t | SELECT CAST(COUNT(*) AS TEXT) FROM users;
T | SELECT CAST(o.amount AS TEXT) FROM users u LEFT JOIN orders o ON o.user_id = u.id ORDER BY u.id, o.id;
B | SELECT CAST(o.id AS BOOLEAN) FROM users u LEFT JOIN orders o ON o.user_id = u.id ORDER BY u.id, o.id;
t | WITH labels AS (SELECT id::TEXT AS id FROM users) SELECT id FROM labels ORDER BY id;
i | SELECT q.n::INT FROM (SELECT '42'::TEXT AS n) q;
rt | SELECT 3::REAL AS number, TRUE::TEXT AS label;
b | SELECT CAST('true' AS BOOL) AND CAST('false' AS BOOLEAN);
"""),
'predicates': examples("""
i | SELECT id FROM users WHERE name LIKE 'A%' ORDER BY id;
i | SELECT id FROM users WHERE name ILIKE 'a%' ORDER BY id;
i | SELECT id FROM users WHERE name NOT LIKE 'A%' ORDER BY id;
i | SELECT id FROM users WHERE name NOT ILIKE 'a%' ORDER BY id;
i | SELECT id FROM users WHERE name LIKE '_o%' ORDER BY id;
i | SELECT id FROM users WHERE name ILIKE '%R%' ORDER BY id;
i | SELECT id FROM users WHERE city LIKE 'P_ris' ORDER BY id;
i | SELECT id FROM users WHERE city NOT LIKE '' ORDER BY id;
i | SELECT id FROM users WHERE name LIKE 'O''B%' ORDER BY id;
i | SELECT id FROM flags WHERE label ILIKE '%abled' ORDER BY id;
b | SELECT 'Alice' LIKE 'A%';
b | SELECT 'Alice' ILIKE 'a%';
b | SELECT 'Alice' NOT LIKE 'a%';
b | SELECT 'Alice' NOT ILIKE 'a%';
b | SELECT '' LIKE '%';
b | SELECT 'abc' LIKE 'a_c';
i | SELECT id FROM users WHERE id IN (1, 3, 5) ORDER BY id;
i | SELECT id FROM users WHERE id NOT IN (1, 3, 5) ORDER BY id;
i | SELECT id FROM users WHERE city IN ('Paris', 'Rome') ORDER BY id;
i | SELECT id FROM users WHERE city NOT IN ('Paris', 'Rome') ORDER BY id;
i | SELECT id FROM flags WHERE enabled IN (TRUE) ORDER BY id;
i | SELECT id FROM flags WHERE enabled NOT IN (FALSE) ORDER BY id;
i | SELECT id FROM orders WHERE status IN ('paid', 'pending') ORDER BY id;
i | SELECT id FROM users WHERE id IN (1 + 1, 2 * 2) ORDER BY id;
b | SELECT 2 IN (1, 2, 3);
b | SELECT 2 NOT IN (1, 3);
b | SELECT 'ready' IN ('waiting', 'ready');
b | SELECT 16777216 IN (0::REAL, 16777217);
i | SELECT id FROM users WHERE age BETWEEN 18 AND 40 ORDER BY id;
i | SELECT id FROM users WHERE age NOT BETWEEN 18 AND 40 ORDER BY id;
i | SELECT id FROM orders WHERE amount BETWEEN 50 AND 120 ORDER BY id;
i | SELECT id FROM employees WHERE salary NOT BETWEEN 80 AND 100 ORDER BY id;
b | SELECT 3 BETWEEN 1 AND 3;
b | SELECT 3 NOT BETWEEN 1 AND 2;
b | SELECT 'b' BETWEEN 'a' AND 'c';
b | SELECT 3 BETWEEN 4 AND 2;
i | SELECT id FROM users WHERE age BETWEEN 10 + 8 AND 20 * 2 ORDER BY id;
i | SELECT id FROM users WHERE age BETWEEN 18 AND 40 AND city = 'Paris' ORDER BY id;
i | SELECT id FROM users WHERE age NOT BETWEEN 18 AND 40 OR city = 'Rome' ORDER BY id;
i | SELECT id FROM users WHERE NOT (id IN (1, 2)) ORDER BY id;
i | SELECT id FROM users WHERE name ILIKE 'a%' OR name ILIKE 'b%' ORDER BY id;
i | SELECT id FROM users WHERE city IN ('Paris') AND age BETWEEN 18 AND 50 ORDER BY id;
i | SELECT id FROM orders WHERE status NOT IN ('cancelled') AND amount NOT BETWEEN 0 AND 49 ORDER BY id;
bbb | SELECT 'ABC' ILIKE 'abc', 4 IN (2, 4), 5 BETWEEN 1 AND 5;
B | SELECT o.status LIKE 'p%' FROM users u LEFT JOIN orders o ON u.id = o.user_id ORDER BY u.id, o.id;
B | SELECT o.id IN (101, 104) FROM users u LEFT JOIN orders o ON u.id = o.user_id ORDER BY u.id, o.id;
B | SELECT o.amount BETWEEN 0 AND 100 FROM users u LEFT JOIN orders o ON u.id = o.user_id ORDER BY u.id, o.id;
i | WITH people AS (SELECT id, name FROM users) SELECT id FROM people WHERE name ILIKE '%a%' ORDER BY id;
i | SELECT q.id FROM (SELECT id, age FROM users) q WHERE q.age BETWEEN 18 AND 40 ORDER BY q.id;
i | SELECT COUNT(*) FILTER (WHERE age BETWEEN 18 AND 40) FROM users;
"""),
'null_ordering': examples("""
iI | SELECT u.id, o.amount FROM users u LEFT JOIN orders o ON o.user_id = u.id ORDER BY o.amount NULLS FIRST, u.id, o.id;
iI | SELECT u.id, o.amount FROM users u LEFT JOIN orders o ON o.user_id = u.id ORDER BY o.amount NULLS LAST, u.id, o.id;
iI | SELECT u.id, o.amount FROM users u LEFT JOIN orders o ON o.user_id = u.id ORDER BY o.amount DESC NULLS FIRST, u.id, o.id;
iI | SELECT u.id, o.amount FROM users u LEFT JOIN orders o ON o.user_id = u.id ORDER BY o.amount DESC NULLS LAST, u.id, o.id;
iT | SELECT e.id, d.name FROM employees e LEFT JOIN departments d ON d.id = e.department_id ORDER BY d.name NULLS FIRST, e.id;
iT | SELECT e.id, d.name FROM employees e LEFT JOIN departments d ON d.id = e.department_id ORDER BY d.name NULLS LAST, e.id;
iT | SELECT e.id, d.name FROM employees e LEFT JOIN departments d ON d.id = e.department_id ORDER BY d.name DESC NULLS FIRST, e.id;
iT | SELECT e.id, d.name FROM employees e LEFT JOIN departments d ON d.id = e.department_id ORDER BY d.name DESC NULLS LAST, e.id;
Ii | SELECT u.id, o.id FROM users u RIGHT JOIN orders o ON o.user_id = u.id ORDER BY u.id NULLS FIRST, o.id;
Ii | SELECT u.id, o.id FROM users u RIGHT JOIN orders o ON o.user_id = u.id ORDER BY u.id NULLS LAST, o.id;
II | SELECT u.id, o.id FROM users u FULL JOIN orders o ON o.user_id = u.id ORDER BY u.id NULLS FIRST, o.id NULLS LAST;
II | SELECT u.id, o.id FROM users u FULL JOIN orders o ON o.user_id = u.id ORDER BY u.id NULLS LAST, o.id NULLS FIRST;
iI | SELECT u.id, SUM(o.amount) AS total FROM users u LEFT JOIN orders o ON o.user_id = u.id GROUP BY u.id ORDER BY total NULLS FIRST, u.id;
iI | SELECT u.id, SUM(o.amount) AS total FROM users u LEFT JOIN orders o ON o.user_id = u.id GROUP BY u.id ORDER BY total NULLS LAST, u.id;
iI | SELECT u.id, SUM(o.amount) AS total FROM users u LEFT JOIN orders o ON o.user_id = u.id GROUP BY u.id ORDER BY total DESC NULLS FIRST, u.id;
iI | SELECT u.id, SUM(o.amount) AS total FROM users u LEFT JOIN orders o ON o.user_id = u.id GROUP BY u.id ORDER BY total DESC NULLS LAST, u.id;
iR | SELECT u.id, AVG(o.amount) AS average FROM users u LEFT JOIN orders o ON o.user_id = u.id GROUP BY u.id ORDER BY average NULLS FIRST, u.id;
iR | SELECT u.id, AVG(o.amount) AS average FROM users u LEFT JOIN orders o ON o.user_id = u.id GROUP BY u.id ORDER BY average DESC NULLS LAST, u.id;
iT | SELECT d.id, MIN(e.name) AS first_name FROM departments d LEFT JOIN employees e ON e.department_id = d.id GROUP BY d.id ORDER BY first_name NULLS FIRST, d.id;
iT | SELECT d.id, MIN(e.name) AS first_name FROM departments d LEFT JOIN employees e ON e.department_id = d.id GROUP BY d.id ORDER BY first_name NULLS LAST, d.id;
iI | SELECT u.id, o.amount AS total FROM users u LEFT JOIN orders o ON o.user_id = u.id ORDER BY total NULLS FIRST, u.id, o.id;
iI | SELECT u.id, o.amount AS total FROM users u LEFT JOIN orders o ON o.user_id = u.id ORDER BY total DESC NULLS LAST, u.id, o.id;
iI | SELECT u.id, o.amount FROM users u LEFT JOIN orders o ON o.user_id = u.id ORDER BY 2 NULLS FIRST, 1, o.id;
iI | SELECT u.id, o.amount FROM users u LEFT JOIN orders o ON o.user_id = u.id ORDER BY 2 DESC NULLS LAST, 1, o.id;
iI | SELECT u.id, o.amount + 1 FROM users u LEFT JOIN orders o ON o.user_id = u.id ORDER BY o.amount + 1 NULLS FIRST, u.id, o.id;
iI | SELECT u.id, o.amount * 2 FROM users u LEFT JOIN orders o ON o.user_id = u.id ORDER BY o.amount * 2 NULLS LAST, u.id, o.id;
iI | SELECT u.id, o.amount FROM users u LEFT JOIN orders o ON o.user_id = u.id WHERE u.age >= 18 ORDER BY o.amount NULLS FIRST, u.id, o.id;
iI | SELECT u.id, o.amount FROM users u LEFT JOIN orders o ON o.user_id = u.id WHERE u.age >= 18 ORDER BY o.amount NULLS LAST, u.id, o.id;
iI | SELECT u.id, o.amount FROM users u LEFT JOIN orders o ON o.user_id = u.id ORDER BY o.amount NULLS FIRST, u.id, o.id LIMIT 4;
iI | SELECT u.id, o.amount FROM users u LEFT JOIN orders o ON o.user_id = u.id ORDER BY o.amount NULLS LAST, u.id, o.id LIMIT 4 OFFSET 2;
iI | WITH purchases AS (SELECT u.id, o.amount FROM users u LEFT JOIN orders o ON o.user_id = u.id) SELECT id, amount FROM purchases ORDER BY amount NULLS FIRST, id;
iI | WITH purchases AS (SELECT u.id, o.amount FROM users u LEFT JOIN orders o ON o.user_id = u.id) SELECT id, amount FROM purchases ORDER BY amount NULLS LAST, id;
iI | SELECT q.id, q.amount FROM (SELECT u.id, o.amount FROM users u LEFT JOIN orders o ON o.user_id = u.id) q ORDER BY q.amount DESC NULLS FIRST, q.id;
iI | SELECT q.id, q.amount FROM (SELECT u.id, o.amount FROM users u LEFT JOIN orders o ON o.user_id = u.id) q ORDER BY q.amount DESC NULLS LAST, q.id;
i | SELECT id FROM users ORDER BY id NULLS FIRST;
i | SELECT id FROM users ORDER BY id NULLS LAST;
i | SELECT id FROM users ORDER BY id DESC NULLS FIRST;
i | SELECT id FROM users ORDER BY id DESC NULLS LAST;
t | SELECT name FROM users ORDER BY name NULLS FIRST;
t | SELECT name FROM users ORDER BY name DESC NULLS LAST;
b | SELECT enabled FROM flags ORDER BY enabled NULLS FIRST, id;
b | SELECT enabled FROM flags ORDER BY enabled DESC NULLS LAST, id;
i | SELECT 1 AS n ORDER BY n NULLS FIRST;
i | SELECT 1 AS n ORDER BY n DESC NULLS LAST;
I | SELECT SUM(amount) AS total FROM orders ORDER BY total NULLS FIRST;
I | SELECT SUM(amount) AS total FROM orders WHERE FALSE ORDER BY total NULLS LAST;
iI | SELECT DISTINCT u.id, o.amount FROM users u LEFT JOIN orders o ON o.user_id = u.id ORDER BY o.amount NULLS FIRST, u.id;
iI | SELECT DISTINCT u.id, o.amount FROM users u LEFT JOIN orders o ON o.user_id = u.id ORDER BY o.amount DESC NULLS LAST, u.id;
iI | SELECT DISTINCT ON (u.id) u.id, o.amount FROM users u LEFT JOIN orders o ON o.user_id = u.id ORDER BY u.id NULLS FIRST, o.amount DESC NULLS LAST, o.id;
i | SELECT id AS n FROM users UNION SELECT user_id FROM orders ORDER BY n NULLS FIRST;
"""),
'returning': examples("""
iitt | INSERT INTO users VALUES (20, 30, 'Zoe', 'Oslo') RETURNING *;
i | INSERT INTO users VALUES (21, 25, 'Amy', 'Paris') RETURNING id;
it | INSERT INTO users VALUES (22, 28, 'Ken', 'Rome') RETURNING id, name;
it | INSERT INTO users (name, id, city, age) VALUES ('Uma', 23, 'Lima', 31) RETURNING id, name;
i | INSERT INTO users VALUES (24, 35, 'Lee', 'Tokyo') RETURNING age + 1 AS next_age;
t | INSERT INTO users VALUES (25, 18, 'Sam', 'Oslo') RETURNING users.name;
iitt | INSERT INTO users VALUES (26, 40, 'Pat', 'Paris') RETURNING users.*;
b | INSERT INTO users VALUES (27, 16, 'Jay', 'Rome') RETURNING age >= 18 AS adult;
t | INSERT INTO users VALUES (28, 44, 'Max', 'Lima') RETURNING id::TEXT;
b | INSERT INTO users VALUES (29, 50, 'Ari', 'Tokyo') RETURNING name ILIKE 'a%';
it | INSERT INTO users VALUES (30, 22, 'Ava', 'Oslo'), (31, 23, 'Eli', 'Rome') RETURNING id, city;
ii | INSERT INTO orders VALUES (201, 1, 90, 'paid') RETURNING id, amount;
t | INSERT INTO orders VALUES (202, 2, 70, 'pending') RETURNING status AS state;
b | INSERT INTO orders VALUES (203, 3, 40, 'paid') RETURNING amount BETWEEN 20 AND 60;
ii | INSERT INTO employees VALUES (10, 1, 1, 'Nia', 95) RETURNING id, salary;
ibt | INSERT INTO flags VALUES (10, TRUE, 'Test') RETURNING *;
b | INSERT INTO flags VALUES (11, FALSE, 'Trial') RETURNING NOT enabled;
it | INSERT INTO departments VALUES (10, 'Support') RETURNING id AS department_id, name;
i | UPDATE users SET age = age + 1 WHERE id = 1 RETURNING age;
iitt | UPDATE users SET city = 'Milan' WHERE id = 2 RETURNING *;
it | UPDATE users SET name = 'Bobby' WHERE id = 2 RETURNING id, name;
iit | UPDATE users SET age = age + 2, city = 'Berlin' WHERE id = 3 RETURNING id, age, city;
i | UPDATE users SET age = age - 1 WHERE age >= 18 RETURNING id;
iitt | UPDATE users SET age = age WHERE FALSE RETURNING users.*;
t | UPDATE users SET city = 'Oslo' WHERE id = 4 RETURNING city AS destination;
b | UPDATE users SET age = 18 WHERE id = 2 RETURNING age >= 18;
t | UPDATE users SET age = age + 1 WHERE id = 1 RETURNING age::TEXT;
b | UPDATE users SET name = 'ALICE' WHERE id = 1 RETURNING name ILIKE 'alice';
ib | UPDATE users SET age = age + 1 WHERE id = 5 RETURNING id, age IN (33, 34);
i | UPDATE orders SET amount = amount + 10 WHERE status = 'paid' RETURNING amount;
ii | UPDATE orders SET status = 'paid' WHERE id = 103 RETURNING id, amount;
it | UPDATE orders SET amount = 0, status = 'cancelled' WHERE id = 101 RETURNING id, status;
ii | UPDATE employees SET salary = salary + 5 WHERE department_id = 1 RETURNING id, salary;
ib | UPDATE flags SET enabled = NOT enabled WHERE id = 2 RETURNING id, enabled;
t | UPDATE departments SET name = 'Product' WHERE id = 1 RETURNING name;
i | DELETE FROM users WHERE id = 1 RETURNING id;
iitt | DELETE FROM users WHERE age < 18 RETURNING *;
it | DELETE FROM users WHERE city = 'Rome' RETURNING id, name;
iitt | DELETE FROM users WHERE FALSE RETURNING users.*;
t | DELETE FROM users WHERE id = 5 RETURNING name AS removed_name;
i | DELETE FROM users WHERE id = 3 RETURNING age + 1;
b | DELETE FROM users WHERE id = 4 RETURNING age >= 65;
t | DELETE FROM users WHERE id = 6 RETURNING id::TEXT;
b | DELETE FROM users WHERE id = 1 RETURNING name LIKE 'A%';
b | DELETE FROM users WHERE id = 2 RETURNING age NOT BETWEEN 18 AND 65;
ii | DELETE FROM orders WHERE status = 'cancelled' RETURNING id, amount;
it | DELETE FROM orders WHERE amount = 50 RETURNING id, status;
it | DELETE FROM employees WHERE salary < 80 RETURNING id, name;
ibt | DELETE FROM flags WHERE NOT enabled RETURNING *;
it | DELETE FROM departments WHERE id = 3 RETURNING id, name;
"""),
}


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--check', action='store_true')
    args = parser.parse_args()
    outputs = {f'{category}.sql': '\n'.join(sql for _, sql in rows) + '\n'
               for category, rows in EXAMPLES.items()}
    outputs['expected_types.json'] = json.dumps(
        {category: [types for types, _ in rows] for category, rows in EXAMPLES.items()}, indent=2) + '\n'
    outputs['schema.json'] = json.dumps(SCHEMA, indent=2) + '\n'
    stale = []
    for filename, content in outputs.items():
        path = FIXTURE_DIR / filename
        if args.check:
            if not path.exists() or path.read_text(encoding='utf-8') != content:
                stale.append(str(path.relative_to(ROOT)))
        else:
            FIXTURE_DIR.mkdir(parents=True, exist_ok=True)
            path.write_text(content, encoding='utf-8')
    if stale:
        parser.exit(1, 'Stale PostgreSQL fixtures: ' + ', '.join(stale) + '\n')
    print(f"{'Checked' if args.check else 'Generated'} 50 examples for each of six PostgreSQL classes (300 total).")


if __name__ == '__main__':
    main()
