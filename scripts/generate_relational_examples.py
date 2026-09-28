#!/usr/bin/env python3
"""Generate 50 examples each for joins, grouping, subqueries, and CTEs.

Each line is a distinct, independently usable SELECT statement. These examples
cover aliases, qualified/mixed wildcards, all supported join kinds, chained and
self joins, NULL predicates, aggregates, grouped expressions, HAVING, ordering,
and pagination. Run --check to detect missing or stale checked-in fixtures.
"""

from __future__ import annotations

import argparse
import json
from pathlib import Path


ROOT = Path(__file__).resolve().parents[1]
FIXTURE_DIR = ROOT / "fixtures" / "relational"


def statements(source: str) -> list[str]:
    result = [line.strip() for line in source.strip().splitlines() if line.strip()]
    if len(result) != 50 or len(set(result)) != 50:
        raise ValueError(f"Expected 50 distinct statements, found {len(result)}")
    return result


EXAMPLES = {
    "joins": statements("""
SELECT users.name, orders.amount FROM users JOIN orders ON users.id = orders.user_id;
SELECT u.id, o.id AS order_id FROM users AS u INNER JOIN orders AS o ON u.id = o.user_id;
SELECT u.name customer, o.amount total FROM users u JOIN orders o ON u.id = o.user_id;
SELECT u.name, o.amount FROM users u LEFT JOIN orders o ON u.id = o.user_id;
SELECT u.id, o.status FROM users AS u LEFT OUTER JOIN orders AS o ON u.id = o.user_id;
SELECT u.name, o.id FROM users u RIGHT JOIN orders o ON u.id = o.user_id;
SELECT u.id, o.amount FROM users u RIGHT OUTER JOIN orders o ON u.id = o.user_id;
SELECT u.id, o.id FROM users u FULL JOIN orders o ON u.id = o.user_id;
SELECT u.name, o.status FROM users AS u FULL OUTER JOIN orders AS o ON u.id = o.user_id;
SELECT u.name, f.label FROM users u CROSS JOIN flags f;
SELECT * FROM users u JOIN orders o ON u.id = o.user_id;
SELECT u.*, o.amount FROM users u JOIN orders o ON u.id = o.user_id;
SELECT u.id, o.* FROM users u LEFT JOIN orders o ON u.id = o.user_id;
SELECT u.*, o.* FROM users u FULL OUTER JOIN orders o ON u.id = o.user_id;
SELECT *, o.amount + 1 AS adjusted FROM users u JOIN orders o ON u.id = o.user_id;
SELECT e.name, m.name AS manager FROM employees e LEFT JOIN employees m ON e.manager_id = m.id;
SELECT e.name, m.name FROM employees e INNER JOIN employees m ON e.manager_id = m.id;
SELECT e.name, d.name AS department FROM employees e JOIN departments d ON e.department_id = d.id;
SELECT d.name, e.name FROM departments d LEFT JOIN employees e ON d.id = e.department_id;
SELECT e.name, d.name, m.name AS manager FROM employees e JOIN departments d ON e.department_id = d.id LEFT JOIN employees m ON e.manager_id = m.id;
SELECT u.name, o.amount, f.enabled FROM users u JOIN orders o ON u.id = o.user_id CROSS JOIN flags f;
SELECT u.id FROM users u LEFT JOIN orders o ON u.id = o.user_id WHERE o.id IS NULL;
SELECT u.id, o.id FROM users u LEFT JOIN orders o ON u.id = o.user_id WHERE o.id IS NOT NULL;
SELECT o.id FROM users u RIGHT JOIN orders o ON u.id = o.user_id WHERE u.id IS NULL;
SELECT u.id, o.id FROM users u FULL JOIN orders o ON u.id = o.user_id WHERE u.id IS NULL OR o.id IS NULL;
SELECT e.name, m.name IS NULL AS has_no_manager FROM employees e LEFT JOIN employees m ON e.manager_id = m.id;
SELECT u.name, o.amount FROM users u JOIN orders o ON u.id = o.user_id AND o.amount > 100;
SELECT u.name, o.amount FROM users u LEFT JOIN orders o ON u.id = o.user_id AND o.status = 'paid';
SELECT u.name, o.amount FROM users u JOIN orders o ON u.id = o.user_id WHERE u.age >= 18 AND o.status <> 'cancelled';
SELECT u.id, o.amount + u.age AS score FROM users u JOIN orders o ON u.id = o.user_id ORDER BY score DESC;
SELECT u.name AS customer_name, o.amount AS order_total FROM users u JOIN orders o ON u.id = o.user_id ORDER BY customer_name, order_total DESC;
SELECT u.name, o.amount FROM users u JOIN orders o ON u.id = o.user_id ORDER BY 2 DESC, 1;
SELECT DISTINCT u.city, o.status FROM users u JOIN orders o ON u.id = o.user_id ORDER BY u.city, o.status;
SELECT DISTINCT u.id AS customer_id FROM users u JOIN orders o ON u.id = o.user_id ORDER BY customer_id;
SELECT u.id, o.id FROM users u JOIN orders o ON u.id = o.user_id ORDER BY o.id LIMIT 10 OFFSET 20;
SELECT u.name, f.label FROM users u CROSS JOIN flags f WHERE f.enabled ORDER BY u.name LIMIT 5;
SELECT a.name, b.name FROM users a JOIN users b ON a.city = b.city AND a.id < b.id;
SELECT e.name, m.name FROM employees e LEFT JOIN employees m ON e.manager_id = m.id WHERE NOT (m.id IS NULL);
SELECT u.id, o.amount * 2 - u.age AS adjusted FROM users u JOIN orders o ON u.id = o.user_id WHERE o.amount / 2 >= 10;
SELECT u.id, -o.amount AS credit FROM users u LEFT JOIN orders o ON u.id = o.user_id;
SELECT u.name, f.enabled, NOT f.enabled AS disabled FROM users u CROSS JOIN flags f WHERE f.enabled OR u.age > 65;
SELECT "customer alias"."name", "order alias"."amount" FROM "users" AS "customer alias" JOIN "orders" AS "order alias" ON "customer alias"."id" = "order alias"."user_id";
SELECT users.*, orders.status AS order_status FROM users JOIN orders ON users.id = orders.user_id;
SELECT e.name, d.name, m.name FROM employees e LEFT JOIN departments d ON e.department_id = d.id LEFT JOIN employees m ON e.manager_id = m.id;
SELECT d.name, e.name, m.name FROM departments d RIGHT JOIN employees e ON d.id = e.department_id LEFT JOIN employees m ON e.manager_id = m.id;
SELECT u.name, o.amount, f.label FROM users u FULL JOIN orders o ON u.id = o.user_id CROSS JOIN flags f;
SELECT u.name, o.amount FROM users u JOIN orders o ON u.id = o.user_id OR (u.id = 0 AND o.user_id = 0);
SELECT u.name, 'It''s paid' AS note FROM users u JOIN orders o ON u.id = o.user_id WHERE o.status = 'paid';
SELECT u.id, o.id FROM users u CROSS JOIN orders o WHERE u.id = o.user_id;
SELECT e.*, d.name AS department_name FROM employees e LEFT JOIN departments d ON e.department_id = d.id ORDER BY e.salary DESC LIMIT 3 OFFSET 1;
"""),
    "grouping": statements("""
SELECT COUNT(*) FROM users;
SELECT COUNT(id) AS user_count FROM users;
SELECT COUNT(DISTINCT city) AS city_count FROM users;
SELECT SUM(amount) AS revenue FROM orders;
SELECT AVG(amount) AS average_amount FROM orders;
SELECT MIN(amount), MAX(amount) FROM orders;
SELECT MIN(name), MAX(name) FROM users;
SELECT COUNT(*), SUM(amount), AVG(amount), MIN(amount), MAX(amount) FROM orders;
SELECT SUM(DISTINCT amount), AVG(DISTINCT amount) FROM orders;
SELECT MIN(DISTINCT city), MAX(DISTINCT city) FROM users;
SELECT city, COUNT(*) FROM users GROUP BY city;
SELECT city, AVG(age) AS average_age FROM users GROUP BY city ORDER BY average_age DESC;
SELECT status, COUNT(*), SUM(amount) FROM orders GROUP BY status;
SELECT user_id, status, SUM(amount) FROM orders GROUP BY user_id, status ORDER BY user_id, status;
SELECT city FROM users GROUP BY city ORDER BY city;
SELECT age / 10 AS decade, COUNT(*) FROM users GROUP BY age / 10 ORDER BY decade;
SELECT city, age / 10, COUNT(*) FROM users GROUP BY city, age / 10;
SELECT city, COUNT(*) AS population FROM users GROUP BY city HAVING COUNT(*) > 1;
SELECT status, SUM(amount) AS total FROM orders GROUP BY status HAVING SUM(amount) >= 100;
SELECT user_id, AVG(amount) FROM orders GROUP BY user_id HAVING AVG(amount) > 10;
SELECT user_id, MIN(amount), MAX(amount) FROM orders GROUP BY user_id HAVING MAX(amount) - MIN(amount) > 20;
SELECT COUNT(*) FROM orders HAVING COUNT(*) > 0;
SELECT SUM(amount) FROM orders HAVING SUM(amount) IS NOT NULL;
SELECT city, COUNT(*) FROM users WHERE age >= 18 GROUP BY city HAVING COUNT(*) >= 2 ORDER BY city LIMIT 10;
SELECT status, COUNT(DISTINCT user_id) FROM orders WHERE amount > 0 GROUP BY status;
SELECT u.city, COUNT(*) FROM users u JOIN orders o ON u.id = o.user_id GROUP BY u.city;
SELECT u.id, u.name, SUM(o.amount) AS total FROM users u JOIN orders o ON u.id = o.user_id GROUP BY u.id, u.name;
SELECT u.id, COUNT(o.id) AS order_count FROM users u LEFT JOIN orders o ON u.id = o.user_id GROUP BY u.id;
SELECT u.id, SUM(o.amount), AVG(o.amount) FROM users u LEFT JOIN orders o ON u.id = o.user_id GROUP BY u.id;
SELECT d.name, COUNT(e.id), AVG(e.salary) FROM departments d LEFT JOIN employees e ON d.id = e.department_id GROUP BY d.name;
SELECT e.department_id, m.name, COUNT(*) FROM employees e LEFT JOIN employees m ON e.manager_id = m.id GROUP BY e.department_id, m.name;
SELECT o.status, COUNT(DISTINCT u.city) FROM users u RIGHT JOIN orders o ON u.id = o.user_id GROUP BY o.status;
SELECT u.city, o.status, COUNT(*) FROM users u FULL JOIN orders o ON u.id = o.user_id GROUP BY u.city, o.status;
SELECT f.enabled, COUNT(*) FROM users u CROSS JOIN flags f GROUP BY f.enabled;
SELECT city AS hometown, COUNT(*) FROM users GROUP BY hometown;
SELECT city, COUNT(*) FROM users GROUP BY 1;
SELECT age / 10 AS decade, COUNT(*) AS population FROM users GROUP BY decade HAVING COUNT(*) > 0 ORDER BY 2 DESC, 1;
SELECT city, COUNT(*) AS population FROM users GROUP BY city ORDER BY population DESC LIMIT 5 OFFSET 5;
SELECT DISTINCT city, COUNT(*) FROM users GROUP BY city ORDER BY city;
SELECT user_id, SUM(amount + 1), AVG(amount * 2) FROM orders GROUP BY user_id;
SELECT user_id, SUM(-amount) AS credits FROM orders GROUP BY user_id HAVING SUM(-amount) < 0;
SELECT COUNT(*), TRUE AS present FROM users HAVING COUNT(*) > 0;
SELECT city, COUNT(*) + 1 AS next_population FROM users GROUP BY city;
SELECT city, SUM(age) / COUNT(*) AS mean_age FROM users GROUP BY city HAVING COUNT(*) > 0;
SELECT city, MIN(age) >= 18 AS all_adults FROM users GROUP BY city;
SELECT status, SUM(amount) IS NULL AS missing_total FROM orders GROUP BY status;
SELECT enabled, COUNT(*) FROM flags GROUP BY enabled HAVING enabled = TRUE;
SELECT city, COUNT(*) FROM users GROUP BY city HAVING city <> '' AND COUNT(*) > 0;
SELECT u.city, SUM(o.amount) AS revenue FROM users u JOIN orders o ON u.id = o.user_id WHERE o.status = 'paid' GROUP BY u.city HAVING SUM(o.amount) > 100 ORDER BY revenue DESC LIMIT 20;
SELECT "u"."city" AS "home city", COUNT(DISTINCT "u"."name") AS "people count" FROM "users" AS "u" GROUP BY "u"."city" ORDER BY "people count" DESC;
"""),
    "subqueries": statements("""
SELECT u.id FROM (SELECT id FROM users) AS u;
SELECT u.name, u.city FROM (SELECT name, city FROM users) u;
SELECT u.* FROM (SELECT id, name FROM users WHERE age >= 18) AS u;
SELECT * FROM (SELECT id, age, name, city FROM users) AS u;
SELECT u.customer_id FROM (SELECT id AS customer_id FROM users) AS u;
SELECT u.next_age FROM (SELECT age + 1 AS next_age FROM users) AS u;
SELECT u.name FROM (SELECT name, age FROM users) AS u WHERE u.age > 21;
SELECT u.name FROM (SELECT name FROM users ORDER BY name LIMIT 10) AS u;
SELECT u.name FROM (SELECT name FROM users ORDER BY id LIMIT 5 OFFSET 2) AS u ORDER BY u.name;
SELECT DISTINCT u.city FROM (SELECT city FROM users) AS u ORDER BY u.city;
SELECT o.amount FROM (SELECT amount FROM orders WHERE status = 'paid') AS o;
SELECT o.amount * 2 AS doubled FROM (SELECT amount FROM orders) AS o;
SELECT o.id, o.total FROM (SELECT id, amount + 1 AS total FROM orders) AS o ORDER BY o.total DESC;
SELECT o.status FROM (SELECT DISTINCT status FROM orders) AS o;
SELECT u.id, o.amount FROM (SELECT id FROM users WHERE age >= 18) AS u JOIN orders o ON u.id = o.user_id;
SELECT u.name, o.amount FROM users u JOIN (SELECT user_id, amount FROM orders WHERE amount > 0) AS o ON u.id = o.user_id;
SELECT u.id, o.amount FROM users u LEFT JOIN (SELECT user_id, amount FROM orders) AS o ON u.id = o.user_id;
SELECT u.id FROM users u LEFT JOIN (SELECT user_id, id FROM orders) AS o ON u.id = o.user_id WHERE o.id IS NULL;
SELECT u.name, o.amount FROM (SELECT id, name FROM users) AS u JOIN (SELECT user_id, amount FROM orders) AS o ON u.id = o.user_id;
SELECT u.id, o.id FROM (SELECT id FROM users) AS u FULL JOIN (SELECT id, user_id FROM orders) AS o ON u.id = o.user_id;
SELECT x.total FROM (SELECT COUNT(*) AS total FROM users) AS x;
SELECT x.revenue FROM (SELECT SUM(amount) AS revenue FROM orders) AS x;
SELECT x.mean FROM (SELECT AVG(amount) AS mean FROM orders) AS x;
SELECT x.city, x.population FROM (SELECT city, COUNT(*) AS population FROM users GROUP BY city) AS x;
SELECT x.city FROM (SELECT city, COUNT(*) AS population FROM users GROUP BY city) AS x WHERE x.population > 2;
SELECT x.status, x.revenue FROM (SELECT status, SUM(amount) AS revenue FROM orders GROUP BY status) AS x ORDER BY x.revenue DESC;
SELECT x.user_id FROM (SELECT user_id, SUM(amount) AS revenue FROM orders GROUP BY user_id HAVING SUM(amount) > 100) AS x;
SELECT u.name, x.total FROM users u JOIN (SELECT user_id, COUNT(*) AS total FROM orders GROUP BY user_id) AS x ON u.id = x.user_id;
SELECT u.name, x.total FROM users u LEFT JOIN (SELECT user_id, COUNT(*) AS total FROM orders GROUP BY user_id) AS x ON u.id = x.user_id;
SELECT x.city, COUNT(*) FROM (SELECT city FROM users) AS x GROUP BY x.city;
SELECT SUM(x.total) FROM (SELECT user_id, SUM(amount) AS total FROM orders GROUP BY user_id) AS x;
SELECT MAX(x.population) FROM (SELECT city, COUNT(*) AS population FROM users GROUP BY city) AS x;
SELECT x.city, COUNT(*) FROM (SELECT city, age FROM users) AS x WHERE x.age >= 18 GROUP BY x.city HAVING COUNT(*) > 0;
SELECT x.id FROM (SELECT y.id FROM (SELECT id FROM users) AS y) AS x;
SELECT x.customer FROM (SELECT y.name AS customer FROM (SELECT name FROM users) AS y) AS x;
SELECT x.amount FROM (SELECT y.amount FROM (SELECT amount FROM orders WHERE status = 'paid') AS y WHERE y.amount > 10) AS x;
SELECT x.total FROM (SELECT COUNT(*) AS total FROM (SELECT id FROM users WHERE age > 30) AS y) AS x;
SELECT x.* FROM (SELECT y.* FROM (SELECT id, name FROM users) AS y) AS x;
SELECT x.name, x.amount FROM (SELECT u.name, o.amount FROM users u JOIN orders o ON u.id = o.user_id) AS x;
SELECT x.name FROM (SELECT u.name, o.id AS order_id FROM users u LEFT JOIN orders o ON u.id = o.user_id) AS x WHERE x.order_id IS NULL;
SELECT e.name, d.name FROM (SELECT name, department_id FROM employees) AS e JOIN departments d ON e.department_id = d.id;
SELECT d.name, e.mean_salary FROM departments d LEFT JOIN (SELECT department_id, AVG(salary) AS mean_salary FROM employees GROUP BY department_id) AS e ON d.id = e.department_id;
SELECT f.label, f.disabled FROM (SELECT label, NOT enabled AS disabled FROM flags) AS f WHERE f.disabled;
SELECT f.enabled, COUNT(*) FROM (SELECT enabled FROM flags WHERE id > 0) AS f GROUP BY f.enabled;
SELECT u.name, f.label FROM (SELECT name FROM users) AS u CROSS JOIN (SELECT label FROM flags WHERE enabled) AS f;
SELECT u.id, o.amount FROM (SELECT id FROM users) AS u RIGHT JOIN orders o ON u.id = o.user_id;
SELECT x.name AS customer FROM (SELECT name FROM users) AS x ORDER BY customer LIMIT 3;
SELECT x.city, x.population FROM (SELECT city, COUNT(*) AS population FROM users GROUP BY city ORDER BY population DESC LIMIT 5) AS x ORDER BY x.city;
SELECT x."customer name" FROM (SELECT name AS "customer name" FROM users) AS x;
SELECT "derived table"."total amount" FROM (SELECT SUM(amount) AS "total amount" FROM orders) AS "derived table";
"""),
    "ctes": statements("""
WITH adults AS (SELECT id FROM users WHERE age >= 18) SELECT id FROM adults;
WITH customers AS (SELECT id, name, city FROM users) SELECT * FROM customers;
WITH customers AS (SELECT id, name FROM users) SELECT c.* FROM customers c;
WITH customers(customer_id) AS (SELECT id FROM users) SELECT customer_id FROM customers;
WITH ages AS (SELECT age + 1 AS next_age FROM users) SELECT next_age FROM ages;
WITH cities AS (SELECT DISTINCT city FROM users) SELECT city FROM cities ORDER BY city;
WITH recent AS (SELECT id, name FROM users ORDER BY id DESC LIMIT 10) SELECT name FROM recent;
WITH page AS (SELECT id FROM users ORDER BY id LIMIT 5 OFFSET 10) SELECT id FROM page;
WITH paid AS (SELECT user_id, amount FROM orders WHERE status = 'paid') SELECT amount FROM paid;
WITH discounted AS (SELECT id, amount / 2 AS amount FROM orders) SELECT id, amount FROM discounted WHERE amount > 10;
WITH totals(population) AS (SELECT COUNT(*) FROM users) SELECT population FROM totals;
WITH totals AS (SELECT SUM(amount) AS revenue FROM orders) SELECT revenue FROM totals;
WITH totals AS (SELECT AVG(amount) AS average_amount FROM orders) SELECT average_amount FROM totals;
WITH bounds(low, high) AS (SELECT MIN(amount), MAX(amount) FROM orders) SELECT low, high FROM bounds;
WITH populations AS (SELECT city, COUNT(*) AS population FROM users GROUP BY city) SELECT city, population FROM populations;
WITH populations AS (SELECT city, COUNT(*) AS population FROM users GROUP BY city) SELECT city FROM populations WHERE population >= 10;
WITH revenue AS (SELECT status, SUM(amount) AS total FROM orders GROUP BY status) SELECT status, total FROM revenue ORDER BY total DESC;
WITH active AS (SELECT user_id FROM orders GROUP BY user_id HAVING COUNT(*) > 1) SELECT user_id FROM active;
WITH city_counts AS (SELECT city, COUNT(*) AS total FROM users GROUP BY city) SELECT SUM(total) FROM city_counts;
WITH city_counts AS (SELECT city, COUNT(*) AS total FROM users GROUP BY city) SELECT MAX(total) FROM city_counts;
WITH paid AS (SELECT user_id, amount FROM orders WHERE status = 'paid') SELECT u.name, p.amount FROM users u JOIN paid p ON u.id = p.user_id;
WITH paid AS (SELECT id, user_id FROM orders WHERE status = 'paid') SELECT u.name FROM users u LEFT JOIN paid p ON u.id = p.user_id WHERE p.id IS NULL;
WITH totals AS (SELECT user_id, SUM(amount) AS total FROM orders GROUP BY user_id) SELECT u.name, t.total FROM users u LEFT JOIN totals t ON u.id = t.user_id;
WITH names AS (SELECT id, name FROM users) SELECT n.name, o.amount FROM names n JOIN orders o ON n.id = o.user_id;
WITH names AS (SELECT id, name FROM users) SELECT n.name, o.id FROM names n FULL JOIN orders o ON n.id = o.user_id;
WITH labels AS (SELECT label FROM flags WHERE enabled) SELECT u.name, f.label FROM users u CROSS JOIN labels f;
WITH workers AS (SELECT id, department_id, name FROM employees) SELECT w.name, d.name FROM workers w JOIN departments d ON w.department_id = d.id;
WITH salaries AS (SELECT department_id, AVG(salary) AS average_salary FROM employees GROUP BY department_id) SELECT d.name, s.average_salary FROM departments d LEFT JOIN salaries s ON d.id = s.department_id;
WITH toggles AS (SELECT id, NOT enabled AS disabled FROM flags) SELECT id FROM toggles WHERE disabled;
WITH customers AS (SELECT city, age FROM users) SELECT city, COUNT(*) FROM customers WHERE age >= 18 GROUP BY city;
WITH customers AS (SELECT id, name FROM users), paid AS (SELECT user_id, amount FROM orders WHERE status = 'paid') SELECT c.name, p.amount FROM customers c JOIN paid p ON c.id = p.user_id;
WITH customers AS (SELECT id FROM users WHERE age > 30), paid AS (SELECT user_id FROM orders WHERE amount > 100) SELECT c.id FROM customers c JOIN paid p ON c.id = p.user_id;
WITH adults AS (SELECT id, name FROM users WHERE age >= 18), names AS (SELECT name FROM adults) SELECT name FROM names;
WITH paid AS (SELECT user_id, amount FROM orders WHERE status = 'paid'), totals AS (SELECT user_id, SUM(amount) AS total FROM paid GROUP BY user_id) SELECT user_id, total FROM totals;
WITH first_stage AS (SELECT id FROM users), second_stage AS (SELECT id FROM first_stage), third_stage AS (SELECT id FROM second_stage) SELECT id FROM third_stage;
WITH adults AS (SELECT city FROM users WHERE age >= 18), populations AS (SELECT city, COUNT(*) AS total FROM adults GROUP BY city) SELECT city FROM populations WHERE total > 5;
WITH paid AS (SELECT user_id, amount FROM orders WHERE status = 'paid'), totals AS (SELECT user_id, SUM(amount) AS total FROM paid GROUP BY user_id) SELECT u.name, t.total FROM users u JOIN totals t ON u.id = t.user_id;
WITH selected AS (SELECT id, name FROM users) SELECT a.name, b.name FROM selected a JOIN selected b ON a.id < b.id;
WITH totals AS (SELECT user_id, COUNT(*) AS total FROM orders GROUP BY user_id) SELECT a.user_id, b.user_id FROM totals a JOIN totals b ON a.total = b.total AND a.user_id < b.user_id;
WITH adults AS (SELECT id, name FROM users WHERE age >= 18) SELECT x.name FROM (SELECT name FROM adults) AS x;
WITH derived AS (SELECT x.id FROM (SELECT id FROM users) AS x) SELECT id FROM derived;
WITH populations AS (SELECT x.city, COUNT(*) AS total FROM (SELECT city FROM users) AS x GROUP BY x.city) SELECT city, total FROM populations;
WITH outer_names AS (WITH inner_names AS (SELECT name FROM users) SELECT name FROM inner_names) SELECT name FROM outer_names;
WITH outer_ids AS (WITH inner_ids AS (SELECT id FROM users WHERE age >= 18) SELECT id FROM inner_ids) SELECT id FROM outer_ids;
WITH base AS (SELECT id FROM users), nested AS (WITH local_ids AS (SELECT id FROM base) SELECT id FROM local_ids) SELECT id FROM nested;
WITH report AS (SELECT u.city, SUM(o.amount) AS revenue FROM users u JOIN orders o ON u.id = o.user_id GROUP BY u.city) SELECT city, revenue FROM report ORDER BY revenue DESC LIMIT 10;
WITH missing AS (SELECT u.id FROM users u LEFT JOIN orders o ON u.id = o.user_id WHERE o.id IS NULL) SELECT COUNT(*) FROM missing;
WITH departments_report AS (SELECT d.name, COUNT(e.id) AS employees FROM departments d LEFT JOIN employees e ON d.id = e.department_id GROUP BY d.name) SELECT name FROM departments_report WHERE employees = 0;
WITH "customer names"("display name") AS (SELECT name FROM users) SELECT "display name" FROM "customer names";
WITH "totals report" AS (SELECT COUNT(*) AS "user count" FROM users) SELECT r."user count" FROM "totals report" AS r;
"""),
}

SCHEMA = {
    "tables": [
        {"name": table_name, "columns": [{"name": name, "type": kind} for name, kind in columns]}
        for table_name, columns in [
            ("users", [("id", "int"), ("age", "int"), ("name", "text"), ("city", "text")]),
            ("orders", [("id", "int"), ("user_id", "int"), ("amount", "int"), ("status", "text")]),
            ("departments", [("id", "int"), ("name", "text")]),
            ("employees", [("id", "int"), ("department_id", "int"), ("manager_id", "int"), ("name", "text"), ("salary", "int")]),
            ("flags", [("id", "int"), ("enabled", "bool"), ("label", "text")]),
        ]
    ]
}


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--check", action="store_true", help="Fail if any fixture is missing or stale")
    args = parser.parse_args()
    outputs = {f"{category}.sql": "\n".join(queries) + "\n" for category, queries in EXAMPLES.items()}
    outputs["schema.json"] = json.dumps(SCHEMA, ensure_ascii=False, indent=2) + "\n"
    stale = []
    for filename, content in outputs.items():
        path = FIXTURE_DIR / filename
        if args.check:
            if not path.exists() or path.read_text(encoding="utf-8") != content:
                stale.append(str(path.relative_to(ROOT)))
        else:
            FIXTURE_DIR.mkdir(parents=True, exist_ok=True)
            path.write_text(content, encoding="utf-8")
    if stale:
        parser.exit(1, "Stale relational fixtures: " + ", ".join(stale) + "\n")
    print(f"{'Checked' if args.check else 'Generated'} 50 examples each for joins, grouping, subqueries, and CTEs (200 total).")


if __name__ == "__main__":
    main()
