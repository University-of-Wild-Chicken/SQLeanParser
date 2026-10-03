#!/usr/bin/env python3
"""Generate 50 typed examples per industrial query class (150 total).

The examples exercise recursive CTEs, compound UNION queries, and SELECT without
FROM. Output type expectations are authored with the examples, independently of
the parser/checker. Run --check to verify the checked-in fixtures are current.
"""

from __future__ import annotations

import argparse
import json
from pathlib import Path

from generate_relational_examples import SCHEMA as RELATIONAL_SCHEMA

ROOT = Path(__file__).resolve().parents[1]
FIXTURE_DIR = ROOT / "fixtures" / "industrial"


def examples(source: str) -> list[tuple[str, str]]:
    result = [tuple(line.strip().split(" | ", 1)) for line in source.strip().splitlines() if line.strip()]
    assert len(result) == 50, len(result)
    assert len({sql for _, sql in result}) == 50
    assert all(set(types) <= set("itbrITBR") for types, _ in result)
    return result


# Lowercase type codes are non-null; uppercase codes are nullable.
EXAMPLES = {
    "recursive_ctes": examples("""
i | WITH RECURSIVE seq(n) AS (SELECT 1 UNION ALL SELECT n + 1 FROM seq WHERE n < 10) SELECT n FROM seq;
i | WITH RECURSIVE evens(n) AS (SELECT 0 UNION ALL SELECT n + 2 FROM evens WHERE n < 8) SELECT n FROM evens ORDER BY n;
i | WITH RECURSIVE countdown(n) AS (SELECT 10 UNION ALL SELECT n - 1 FROM countdown WHERE n > 0) SELECT n FROM countdown;
i | WITH RECURSIVE signed(n) AS (SELECT -3 UNION ALL SELECT n + 1 FROM signed WHERE n < 3) SELECT n FROM signed;
i | WITH RECURSIVE powers(n) AS (SELECT 1 UNION ALL SELECT n * 2 FROM powers WHERE n < 64) SELECT n FROM powers;
iii | WITH RECURSIVE fib(step, a, b) AS (SELECT 0, 0, 1 UNION ALL SELECT step + 1, b, a + b FROM fib WHERE step < 10) SELECT step, a, b FROM fib;
ii | WITH RECURSIVE factorial(n, product) AS (SELECT 1, 1 UNION ALL SELECT n + 1, product * (n + 1) FROM factorial WHERE n < 6) SELECT n, product FROM factorial;
ii | WITH RECURSIVE squares(n, total) AS (SELECT 0, 0 UNION ALL SELECT n + 1, total + (n + 1) * (n + 1) FROM squares WHERE n < 5) SELECT n, total FROM squares;
it | WITH RECURSIVE labels(n, label) AS (SELECT 1, 'batch' UNION ALL SELECT n + 1, label FROM labels WHERE n < 4) SELECT n, label FROM labels;
ib | WITH RECURSIVE toggles(n, enabled) AS (SELECT 0, TRUE UNION ALL SELECT n + 1, NOT enabled FROM toggles WHERE n < 5) SELECT n, enabled FROM toggles;
i | WITH RECURSIVE bounded(n, stop) AS (SELECT 2, 7 UNION ALL SELECT n + 1, stop FROM bounded WHERE n < stop) SELECT n FROM bounded;
i | WITH RECURSIVE ages(n) AS (SELECT age FROM users WHERE id = 1 UNION ALL SELECT n + 1 FROM ages WHERE n < 27) SELECT n FROM ages;
ii | WITH RECURSIVE retries(user_id, attempt) AS (SELECT id, 1 FROM users UNION ALL SELECT user_id, attempt + 1 FROM retries WHERE attempt < 3) SELECT user_id, attempt FROM retries ORDER BY user_id, attempt;
ii | WITH RECURSIVE installments(order_id, balance) AS (SELECT id, amount FROM orders UNION ALL SELECT order_id, balance - 50 FROM installments WHERE balance > 50) SELECT order_id, balance FROM installments;
i | WITH RECURSIVE once(n) AS (SELECT 42 UNION ALL SELECT n + 1 FROM once WHERE FALSE) SELECT n FROM once;
i | WITH RECURSIVE unique_steps(n) AS (SELECT 1 UNION SELECT n + 1 FROM unique_steps WHERE n < 5) SELECT n FROM unique_steps;
b | WITH RECURSIVE bits(enabled) AS (SELECT TRUE UNION SELECT NOT enabled FROM bits) SELECT enabled FROM bits;
i | WITH RECURSIVE signs(n) AS (SELECT 1 UNION SELECT -n FROM signs) SELECT n FROM signs;
i | WITH RECURSIVE page(n) AS (SELECT 1 UNION ALL SELECT n + 1 FROM page WHERE n < 20) SELECT n AS sequence_number FROM page ORDER BY sequence_number DESC LIMIT 4 OFFSET 2;
i | WITH RECURSIVE "number series"("current value") AS (SELECT 0 UNION ALL SELECT "current value" + 1 FROM "number series" WHERE "current value" < 3) SELECT "current value" FROM "number series";
iii | WITH RECURSIVE hierarchy(id, manager_id, depth) AS (SELECT id, manager_id, 0 FROM employees WHERE manager_id = 99 UNION ALL SELECT e.id, e.manager_id, h.depth + 1 FROM hierarchy h JOIN employees e ON e.manager_id = h.id) SELECT id, manager_id, depth FROM hierarchy;
iii | WITH RECURSIVE ancestors(id, manager_id, level) AS (SELECT id, manager_id, 0 FROM employees WHERE id = 2 UNION ALL SELECT e.id, e.manager_id, a.level + 1 FROM ancestors a JOIN employees e ON e.id = a.manager_id) SELECT id, manager_id, level FROM ancestors;
ti | WITH RECURSIVE team(id, name, depth) AS (SELECT id, name, 0 FROM employees WHERE id = 1 UNION ALL SELECT e.id, e.name, t.depth + 1 FROM team t JOIN employees e ON e.manager_id = t.id) SELECT name, depth FROM team ORDER BY depth, name;
i | WITH RECURSIVE high_paid(id) AS (SELECT id FROM employees WHERE id = 1 UNION ALL SELECT e.id FROM high_paid h JOIN employees e ON e.manager_id = h.id WHERE e.salary >= 85) SELECT id FROM high_paid;
ii | WITH RECURSIVE same_department(id, department_id) AS (SELECT id, department_id FROM employees WHERE id = 1 UNION ALL SELECT e.id, e.department_id FROM same_department s JOIN employees e ON e.manager_id = s.id AND e.department_id = s.department_id) SELECT id, department_id FROM same_department;
i | WITH RECURSIVE department_tree(id) AS (SELECT id FROM employees WHERE department_id = 1 UNION ALL SELECT e.id FROM department_tree t JOIN employees e ON e.manager_id = t.id) SELECT DISTINCT id FROM department_tree;
ii | WITH RECURSIVE descendants(root_id, id) AS (SELECT id, id FROM employees UNION ALL SELECT d.root_id, e.id FROM descendants d JOIN employees e ON e.manager_id = d.id) SELECT root_id, id FROM descendants ORDER BY root_id, id;
ii | WITH RECURSIVE salary_paths(id, total) AS (SELECT id, salary FROM employees WHERE id = 1 UNION ALL SELECT e.id, p.total + e.salary FROM salary_paths p JOIN employees e ON e.manager_id = p.id) SELECT id, total FROM salary_paths;
ii | WITH RECURSIVE chain(id, manager_id, depth) AS (SELECT id, manager_id, 0 FROM employees WHERE id = 3 UNION ALL SELECT e.id, e.manager_id, c.depth + 1 FROM chain c JOIN employees e ON e.id = c.manager_id WHERE c.depth < 4) SELECT id, depth FROM chain;
ii | WITH RECURSIVE levels(id, depth) AS (SELECT id, 0 FROM employees WHERE manager_id = 99 UNION ALL SELECT e.id, l.depth + 1 FROM levels l JOIN employees e ON e.manager_id = l.id) SELECT depth, COUNT(*) AS people FROM levels GROUP BY depth ORDER BY depth;
I | WITH RECURSIVE depth_scan(id, depth) AS (SELECT id, 0 FROM employees WHERE id = 1 UNION ALL SELECT e.id, d.depth + 1 FROM depth_scan d JOIN employees e ON e.manager_id = d.id) SELECT MAX(depth) AS maximum_depth FROM depth_scan;
tt | WITH RECURSIVE staff(id, department_id, name) AS (SELECT id, department_id, name FROM employees WHERE id = 1 UNION ALL SELECT e.id, e.department_id, e.name FROM staff s JOIN employees e ON e.manager_id = s.id) SELECT s.name, d.name FROM staff s JOIN departments d ON d.id = s.department_id;
tT | WITH RECURSIVE all_staff(id, department_id, name) AS (SELECT id, department_id, name FROM employees WHERE manager_id = 99 UNION ALL SELECT e.id, e.department_id, e.name FROM all_staff s JOIN employees e ON e.manager_id = s.id) SELECT s.name, d.name FROM all_staff s LEFT JOIN departments d ON d.id = s.department_id;
i | WITH RECURSIVE reports(id) AS (SELECT id FROM employees WHERE id = 1 UNION ALL SELECT e.id FROM employees e JOIN reports r ON e.manager_id = r.id) SELECT id FROM reports;
i | WITH RECURSIVE cross_reports(id) AS (SELECT id FROM employees WHERE id = 1 UNION ALL SELECT e.id FROM cross_reports r CROSS JOIN employees e WHERE e.manager_id = r.id) SELECT id FROM cross_reports;
i | WITH RECURSIVE reachable(node) AS (SELECT target FROM edges WHERE source = 1 UNION SELECT e.target FROM reachable r JOIN edges e ON e.source = r.node) SELECT node FROM reachable ORDER BY node;
i | WITH RECURSIVE closure(node) AS (SELECT 1 UNION SELECT e.target FROM closure c JOIN edges e ON e.source = c.node) SELECT node FROM closure ORDER BY node;
ii | WITH RECURSIVE paths(root, node) AS (SELECT source, target FROM edges UNION SELECT p.root, e.target FROM paths p JOIN edges e ON e.source = p.node) SELECT root, node FROM paths ORDER BY root, node;
i | WITH RECURSIVE reverse_reachable(node) AS (SELECT 4 UNION SELECT e.source FROM reverse_reachable r JOIN edges e ON e.target = r.node) SELECT node FROM reverse_reachable;
i | WITH RECURSIVE isolated(node) AS (SELECT 404 UNION SELECT e.target FROM isolated i JOIN edges e ON e.source = i.node) SELECT node FROM isolated;
ii | WITH RECURSIVE components(part_id, quantity) AS (SELECT child_id, quantity FROM parts WHERE parent_id = 1 UNION ALL SELECT p.child_id, c.quantity * p.quantity FROM components c JOIN parts p ON p.parent_id = c.part_id) SELECT part_id, quantity FROM components;
iii | WITH RECURSIVE assembly(part_id, quantity, depth) AS (SELECT child_id, quantity, 1 FROM parts WHERE parent_id = 1 UNION ALL SELECT p.child_id, a.quantity * p.quantity, a.depth + 1 FROM assembly a JOIN parts p ON p.parent_id = a.part_id) SELECT part_id, quantity, depth FROM assembly ORDER BY depth, part_id;
iI | WITH RECURSIVE requirements(part_id, quantity) AS (SELECT child_id, quantity FROM parts WHERE parent_id = 1 UNION ALL SELECT p.child_id, r.quantity * p.quantity FROM requirements r JOIN parts p ON p.parent_id = r.part_id) SELECT part_id, SUM(quantity) AS total_quantity FROM requirements GROUP BY part_id ORDER BY part_id;
i | WITH RECURSIVE component_rows(part_id) AS (SELECT child_id FROM parts WHERE parent_id = 1 UNION ALL SELECT p.child_id FROM component_rows c JOIN parts p ON p.parent_id = c.part_id) SELECT COUNT(*) AS component_count FROM component_rows;
ii | WITH RECURSIVE leaf_parts(part_id, quantity) AS (SELECT child_id, quantity FROM parts WHERE parent_id = 1 UNION ALL SELECT p.child_id, l.quantity * p.quantity FROM leaf_parts l JOIN parts p ON p.parent_id = l.part_id) SELECT l.part_id, l.quantity FROM leaf_parts l LEFT JOIN parts p ON p.parent_id = l.part_id WHERE p.child_id IS NULL;
i | WITH RECURSIVE roots(id) AS (SELECT id FROM employees WHERE id = 1), traversal(id) AS (SELECT id FROM roots UNION ALL SELECT e.id FROM traversal t JOIN employees e ON e.manager_id = t.id) SELECT id FROM traversal;
i | WITH RECURSIVE numbers(n) AS (SELECT 1 UNION ALL SELECT n + 1 FROM numbers WHERE n < 5), doubled(value) AS (SELECT n * 2 FROM numbers) SELECT value FROM doubled;
ii | WITH RECURSIVE left_seq(n) AS (SELECT 1 UNION ALL SELECT n + 1 FROM left_seq WHERE n < 3), right_seq(n) AS (SELECT 4 UNION ALL SELECT n + 1 FROM right_seq WHERE n < 6) SELECT l.n, r.n FROM left_seq l CROSS JOIN right_seq r;
i | SELECT q.n FROM (WITH RECURSIVE nested(n) AS (SELECT 1 UNION ALL SELECT n + 1 FROM nested WHERE n < 4) SELECT n FROM nested) AS q;
i | WITH RECURSIVE inferred AS (SELECT 1 AS n UNION ALL SELECT n + 1 FROM inferred WHERE n < 5) SELECT n FROM inferred;
"""),
    "unions": examples("""
i | SELECT id FROM users UNION SELECT user_id FROM orders;
i | SELECT id FROM users UNION ALL SELECT user_id FROM orders;
t | SELECT name FROM users UNION SELECT name FROM employees;
t | SELECT city AS location FROM users UNION ALL SELECT name FROM departments;
b | SELECT enabled FROM flags UNION SELECT TRUE;
ii | SELECT id, age FROM users UNION SELECT id, salary FROM employees;
it | SELECT id, name FROM users UNION ALL SELECT id, name FROM employees;
tt | SELECT name, city FROM users UNION SELECT name, 'employee' FROM employees;
i | SELECT 1 UNION SELECT 2;
i | SELECT 1 UNION ALL SELECT 1;
i | SELECT 1 AS n UNION ALL SELECT 2 UNION ALL SELECT 3;
i | SELECT 1 AS n UNION SELECT 1 UNION ALL SELECT 2;
i | SELECT 1 AS n UNION ALL SELECT 1 UNION SELECT 2;
i | SELECT id FROM users UNION ALL SELECT id FROM orders UNION ALL SELECT id FROM employees;
t | SELECT name FROM users UNION SELECT name FROM departments UNION SELECT label FROM flags;
i | SELECT id FROM users UNION SELECT user_id FROM orders ORDER BY id;
i | SELECT id AS result_id FROM users UNION ALL SELECT user_id FROM orders ORDER BY result_id DESC;
ii | SELECT id, age FROM users UNION ALL SELECT id, salary FROM employees ORDER BY 2 DESC, 1;
i | SELECT id FROM users UNION ALL SELECT id FROM employees LIMIT 4;
i | SELECT id AS item FROM users UNION SELECT id FROM employees ORDER BY item LIMIT 3 OFFSET 1;
i | SELECT id FROM users WHERE age >= 18 UNION SELECT user_id FROM orders WHERE status = 'paid';
t | SELECT DISTINCT city FROM users UNION ALL SELECT DISTINCT status FROM orders;
i | SELECT age + 1 AS number FROM users UNION ALL SELECT amount / 2 FROM orders;
i | SELECT -id AS number FROM users UNION SELECT id * 2 FROM orders;
b | SELECT age >= 18 AS eligible FROM users UNION SELECT enabled FROM flags;
i | SELECT u.id FROM users u JOIN orders o ON u.id = o.user_id UNION SELECT id FROM employees;
I | SELECT o.amount FROM users u LEFT JOIN orders o ON u.id = o.user_id UNION ALL SELECT SUM(salary) FROM employees;
T | SELECT d.name FROM employees e LEFT JOIN departments d ON d.id = e.department_id UNION SELECT MIN(city) FROM users;
ii | SELECT id, COUNT(*) AS tally FROM users GROUP BY id UNION ALL SELECT user_id, COUNT(*) FROM orders GROUP BY user_id;
i | SELECT COUNT(*) AS tally FROM users UNION ALL SELECT COUNT(*) FROM orders;
I | SELECT SUM(amount) AS total FROM orders UNION ALL SELECT SUM(salary) FROM employees;
R | SELECT AVG(age) AS mean FROM users UNION SELECT AVG(salary) FROM employees;
R | SELECT AVG(age) AS measure FROM users UNION ALL SELECT AVG(amount) FROM orders;
I | SELECT SUM(amount) AS measure FROM orders UNION SELECT SUM(age) FROM users;
T | SELECT MIN(name) AS label FROM users UNION SELECT MAX(name) FROM departments;
i | SELECT id FROM (SELECT id FROM users) AS customer_ids UNION ALL SELECT id FROM employees;
i | SELECT q.id FROM (SELECT id FROM users UNION SELECT user_id FROM orders) AS q;
ii | SELECT u.id, o.amount FROM users u JOIN orders o ON o.user_id = u.id UNION ALL SELECT e.id, e.salary FROM employees e;
i | WITH ids AS (SELECT id FROM users) SELECT id FROM ids UNION SELECT user_id FROM orders;
i | WITH merged(id) AS (SELECT id FROM users UNION ALL SELECT user_id FROM orders) SELECT id FROM merged;
it | WITH named AS (SELECT id, name FROM users UNION ALL SELECT id, name FROM employees) SELECT id, name FROM named ORDER BY id;
i | SELECT id AS "result number" FROM users UNION SELECT user_id FROM orders ORDER BY "result number";
t | SELECT 'It''s ready' AS message UNION ALL SELECT 'Waiting';
b | SELECT TRUE AS enabled UNION ALL SELECT FALSE ORDER BY enabled;
i | SELECT 7 AS n WHERE FALSE UNION SELECT 8;
ii | SELECT 1 AS first, 2 AS second UNION ALL SELECT 3, 4 ORDER BY second DESC;
i | SELECT id FROM users WHERE FALSE UNION SELECT id FROM employees WHERE FALSE;
t | SELECT city FROM users GROUP BY city HAVING COUNT(*) > 1 UNION SELECT name FROM departments;
i | SELECT d.id FROM departments d CROSS JOIN flags f WHERE f.enabled UNION SELECT id FROM users;
itb | SELECT 1 AS id, 'alpha' AS label, TRUE AS enabled UNION ALL SELECT 2, 'beta', FALSE ORDER BY id;
"""),
    "source_free": examples("""
i | SELECT 1;
i | SELECT 0;
i | SELECT -1;
i | SELECT +2;
t | SELECT 'hello';
t | SELECT '';
t | SELECT 'It''s ready';
b | SELECT TRUE;
b | SELECT FALSE;
b | SELECT NOT TRUE;
i | SELECT 1 + 2;
i | SELECT 7 - 3;
i | SELECT 4 * 5;
i | SELECT 12 / 3;
i | SELECT 2 + 3 * 4;
i | SELECT (2 + 3) * 4;
i | SELECT -(-3);
b | SELECT 1 = 1;
b | SELECT 1 <> 2;
b | SELECT 1 < 2;
b | SELECT 2 <= 2;
b | SELECT 3 > 2;
b | SELECT 3 >= 3;
b | SELECT 'a' = 'a';
b | SELECT TRUE AND FALSE;
b | SELECT FALSE OR TRUE AND FALSE;
b | SELECT NOT (1 = 2);
b | SELECT 1 IS NULL;
b | SELECT 'text' IS NOT NULL;
ii | SELECT 1, 2;
itb | SELECT 1, 'label', TRUE;
i | SELECT 42 AS answer;
t | SELECT 'ready' AS "status text";
i | SELECT DISTINCT 1;
i | SELECT 1 WHERE TRUE;
i | SELECT 1 WHERE FALSE;
i | SELECT 1 WHERE 2 > 1 AND NOT FALSE;
i | SELECT 2 + 2 AS answer ORDER BY answer;
it | SELECT 1 AS id, 'a' AS label ORDER BY 2, 1 DESC;
i | SELECT 7 LIMIT 1;
i | SELECT 7 LIMIT 0;
i | SELECT 7 LIMIT 1 OFFSET 1;
i | SELECT COUNT(*) AS row_count;
i | SELECT COUNT(1) AS present_count;
i | SELECT COUNT(DISTINCT 1) AS unique_count;
I | SELECT SUM(5) AS total;
R | SELECT AVG(5) AS average;
TT | SELECT MIN('x') AS first, MAX('x') AS last;
i | SELECT COUNT(*) AS row_count WHERE FALSE;
i | SELECT COUNT(*) AS row_count HAVING COUNT(*) > 0;
"""),
}

SCHEMA = {"tables": RELATIONAL_SCHEMA["tables"] + [
    {"name": name, "columns": [{"name": column, "type": "int"} for column in columns]}
    for name, columns in [
        ("edges", ["source", "target"]),
        ("parts", ["parent_id", "child_id", "quantity"]),
    ]
]}


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--check", action="store_true", help="Fail if a fixture is missing or stale")
    args = parser.parse_args()
    outputs = {f"{category}.sql": "\n".join(sql for _, sql in rows) + "\n"
               for category, rows in EXAMPLES.items()}
    outputs["expected_types.json"] = json.dumps(
        {category: [types for types, _ in rows] for category, rows in EXAMPLES.items()}, indent=2) + "\n"
    outputs["schema.json"] = json.dumps(SCHEMA, indent=2) + "\n"
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
        parser.exit(1, "Stale industrial fixtures: " + ", ".join(stale) + "\n")
    print(f"{'Checked' if args.check else 'Generated'} 50 examples each for recursive CTEs, UNIONs, and source-free SELECTs (150 total).")


if __name__ == "__main__":
    main()
