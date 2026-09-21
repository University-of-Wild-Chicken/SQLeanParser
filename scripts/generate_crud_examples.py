#!/usr/bin/env python3
"""Generate the reproducible CRUD verification corpus; no third-party packages.

Each category contains 50 deliberately varied statements. Examples use the
complete, non-null schemas below and exercise all newly supported CRUD clauses.
Run with --check to verify that checked-in fixtures match this source exactly.
"""

from __future__ import annotations

import argparse
import json
from pathlib import Path


ROOT = Path(__file__).resolve().parents[1]
FIXTURE_DIR = ROOT / "fixtures" / "crud"


def statements(source: str) -> list[str]:
    result = [line.strip() for line in source.strip().splitlines() if line.strip()]
    if len(result) != 50 or len(set(result)) != 50:
        raise ValueError(f"Expected 50 distinct statements, found {len(result)}")
    return result


EXAMPLES = {
    "select": statements("""
SELECT * FROM users;
SELECT * FROM inventory WHERE quantity > 0;
SELECT * FROM flags WHERE enabled;
SELECT * FROM users WHERE age >= 18 ORDER BY 4, 1 DESC;
SELECT * FROM inventory ORDER BY price DESC, sku ASC;
SELECT * FROM flags WHERE NOT enabled ORDER BY id;
SELECT * FROM users LIMIT 10;
SELECT * FROM inventory ORDER BY sku LIMIT 20 OFFSET 40;
SELECT DISTINCT * FROM users;
SELECT DISTINCT * FROM flags WHERE enabled = TRUE LIMIT 5;
SELECT DISTINCT city FROM users;
SELECT DISTINCT name, city FROM users WHERE age > 30 ORDER BY 2 DESC, 1;
SELECT DISTINCT price, quantity FROM inventory ORDER BY price DESC;
SELECT DISTINCT enabled FROM flags;
SELECT DISTINCT age / 10 FROM users;
SELECT DISTINCT label FROM inventory WHERE quantity != 0;
SELECT DISTINCT city, age FROM users ORDER BY city ASC, age DESC;
SELECT DISTINCT NOT enabled FROM flags;
SELECT DISTINCT name FROM users WHERE name != '' LIMIT 25;
SELECT DISTINCT label, enabled FROM flags ORDER BY label LIMIT 3 OFFSET 1;
SELECT id, name FROM users ORDER BY name ASC, id DESC;
SELECT sku, price * quantity FROM inventory ORDER BY price * quantity DESC;
SELECT id FROM users ORDER BY age + 1, name DESC;
SELECT label FROM inventory ORDER BY -price ASC;
SELECT id, enabled FROM flags ORDER BY 2 DESC, 1;
SELECT name, city FROM users WHERE age >= 21 ORDER BY city, name, id;
SELECT sku FROM inventory WHERE price <= 100 ORDER BY quantity / 2 DESC;
SELECT id FROM users ORDER BY (age - 18) * 2 DESC;
SELECT label FROM flags ORDER BY NOT enabled, label DESC;
SELECT sku, label FROM inventory ORDER BY 1 ASC, sku DESC;
SELECT id FROM users LIMIT 0;
SELECT name FROM users LIMIT 1 OFFSET 0;
SELECT sku FROM inventory LIMIT 100 OFFSET 200;
SELECT id FROM flags WHERE enabled LIMIT 10 OFFSET 5;
SELECT age + 1, name FROM users WHERE city = 'Paris' LIMIT 7;
SELECT label, price FROM inventory WHERE quantity > 5 LIMIT 12 OFFSET 24;
SELECT id, label FROM flags ORDER BY id DESC LIMIT 2 OFFSET 2;
SELECT id FROM users WHERE NOT (age < 18) LIMIT 50;
SELECT sku FROM inventory WHERE price != 0 ORDER BY sku LIMIT 15 OFFSET 30;
SELECT name FROM users WHERE city = 'New York' ORDER BY name LIMIT 1000;
SELECT -age, +id FROM users;
SELECT -(price * quantity), +sku FROM inventory;
SELECT NOT enabled, TRUE, FALSE FROM flags;
SELECT NOT age = 18 FROM users;
SELECT id FROM users WHERE NOT (age < 18 OR city = 'Closed');
SELECT enabled = TRUE, enabled != FALSE FROM flags ORDER BY id;
SELECT -(-age), +(id + 1) FROM users;
SELECT sku FROM inventory WHERE -price < +quantity ORDER BY sku;
SELECT id, NOT NOT enabled FROM flags;
SELECT TRUE AND NOT FALSE, -5 + +3 * 2 FROM users;
"""),
    "insert": statements("""
INSERT INTO users VALUES (1, 18, 'Alice', 'Paris');
INSERT INTO users VALUES (2, 35, 'Bob', 'London'), (3, 29, 'Carol', 'Berlin');
INSERT INTO users (id, age, name, city) VALUES (4, 41, 'Dora', 'Rome');
INSERT INTO users (name, city, age, id) VALUES ('Eve', 'Oslo', 22, 5);
INSERT INTO users (city, id, name, age) VALUES ('Tokyo', 6, 'Faye', 31), ('Seoul', 7, 'Gus', 28);
INSERT INTO users VALUES (8, 20 + 2, 'Hana', 'Prague');
INSERT INTO users VALUES (9 + 1, 50 - 7, 'Ivan', 'Riga');
INSERT INTO users VALUES (11, 6 * 7, 'Jane', 'Vienna');
INSERT INTO users VALUES (12, 80 / 2, 'Kai', 'Lima');
INSERT INTO users VALUES (+13, +(18 + 3), 'Lea', 'Bern');
INSERT INTO users VALUES (14, -1, 'Unknown age', 'Unset');
INSERT INTO users VALUES (15, 44, 'O''Brien', 'D''Orsay');
INSERT INTO users VALUES (16, 26, '', '');
INSERT INTO users VALUES (17, 32, 'Zoë', 'München');
INSERT INTO users (age, city, id, name) VALUES (24, 'Austin', 18, 'Mia');
INSERT INTO users (id, name, age, city) VALUES (19, 'Noah', 30, 'Denver'), (20, 'Ora', 31, 'Boston'), (21, 'Pia', 32, 'Miami');
INSERT INTO users VALUES ((20 + 2), (4 * (5 + 1)), 'Quin', 'Portland');
INSERT INTO users (city, age, name, id) VALUES ('Québec', 27, 'Rémy', 23);
INSERT INTO users VALUES (24, -(-25), 'Sara', 'A;B');
INSERT INTO "users" ("id", "age", "name", "city") VALUES (25, 39, 'Tom', 'San Francisco');
INSERT INTO inventory VALUES (101, 25, 8, 'Widget');
INSERT INTO inventory VALUES (102, 40, 6, 'Gadget'), (103, 15, 20, 'Cable');
INSERT INTO inventory (sku, price, quantity, label) VALUES (104, 100, 1, 'Monitor');
INSERT INTO inventory (label, quantity, price, sku) VALUES ('Mouse', 30, 20, 105);
INSERT INTO inventory (price, sku, label, quantity) VALUES (75, 106, 'Keyboard', 12);
INSERT INTO inventory VALUES (107, 10 + 5, 3 * 4, 'Adapter');
INSERT INTO inventory VALUES (108, 90 - 10, 24 / 2, 'Dock');
INSERT INTO inventory VALUES (109, 3 * 7, 50 - 2, 'Battery');
INSERT INTO inventory VALUES (110, 100 / 4, 0, 'Empty shelf');
INSERT INTO inventory VALUES (+111, +9, +2, 'Positive');
INSERT INTO inventory VALUES (112, -5, 1, 'Credit');
INSERT INTO inventory VALUES (113, 0, 0, 'Free sample');
INSERT INTO inventory VALUES (114, 7, 2, 'Maker''s kit');
INSERT INTO inventory VALUES (115, 11, 3, '');
INSERT INTO inventory VALUES (116, 13, 4, 'Café supplies');
INSERT INTO inventory (quantity, label, sku, price) VALUES (7, 'Pen', 117, 2), (9, 'Paper', 118, 4);
INSERT INTO inventory VALUES (119, (5 + 5) * 2, 18 / (2 + 1), 'Bundle');
INSERT INTO inventory VALUES (120, 5, 2, 'Small'), (121, 10, 4, 'Medium'), (122, 20, 8, 'Large');
INSERT INTO inventory (sku, quantity, label, price) VALUES (123, -(-6), 'Restock', 3);
INSERT INTO "inventory" VALUES (124, 8, 1, 'Queue;ready');
INSERT INTO flags VALUES (201, TRUE, 'Enabled');
INSERT INTO flags VALUES (202, FALSE, 'Disabled');
INSERT INTO flags (label, enabled, id) VALUES ('Feature A', TRUE, 203);
INSERT INTO flags VALUES (204, NOT FALSE, 'Negated literal');
INSERT INTO flags VALUES (205, TRUE AND FALSE, 'Conjunction');
INSERT INTO flags VALUES (206, FALSE OR TRUE, 'Disjunction');
INSERT INTO flags VALUES (207, 1 < 2, 'Comparison');
INSERT INTO flags (enabled, id, label) VALUES ('a' != 'b', 208, 'Text comparison');
INSERT INTO flags VALUES (209, TRUE, 'First'), (210, FALSE, 'Second'), (211, NOT TRUE, 'Third');
INSERT INTO "flags" ("id", "enabled", "label") VALUES (212, NOT (2 >= 3 OR FALSE), 'Nested');
"""),
    "update": statements("""
UPDATE users SET age = 30 WHERE id = 1;
UPDATE users SET name = 'Alice' WHERE id = 2;
UPDATE users SET city = 'Paris' WHERE age >= 18;
UPDATE users SET age = age + 1;
UPDATE users SET name = 'Bob', city = 'London' WHERE id = 3;
UPDATE users SET age = age - 1 WHERE age > 0;
UPDATE users SET age = age * 2 WHERE id < 10;
UPDATE users SET age = age / 2 WHERE age >= 40;
UPDATE users SET age = +age WHERE age != 0;
UPDATE users SET age = -age WHERE age < 0;
UPDATE users SET id = id + 100, age = age + 1 WHERE city = 'Rome';
UPDATE users SET name = 'O''Brien' WHERE name = 'Obrien';
UPDATE users SET city = '' WHERE city = 'Unknown';
UPDATE users SET name = 'Zoë', city = 'München' WHERE id = 8;
UPDATE users SET age = (age + 2) * 3 WHERE age <= 20;
UPDATE users SET city = 'Adult' WHERE NOT age < 18;
UPDATE users SET name = name, city = city WHERE TRUE;
UPDATE users SET age = 21 WHERE age < 18 OR city = 'Campus';
UPDATE users SET city = 'Verified' WHERE age >= 18 AND name != '';
UPDATE "users" SET "age" = -(0 - age), "city" = 'Reviewed' WHERE NOT (id = 0 OR age < 0);
UPDATE inventory SET price = 20 WHERE sku = 101;
UPDATE inventory SET quantity = quantity + 10 WHERE sku = 102;
UPDATE inventory SET quantity = quantity - 1 WHERE quantity > 0;
UPDATE inventory SET price = price * 2 WHERE label = 'Premium';
UPDATE inventory SET price = price / 2 WHERE quantity >= 100;
UPDATE inventory SET label = 'Sale', price = price - 5 WHERE price > 10;
UPDATE inventory SET price = 0, quantity = 0 WHERE label = 'Discontinued';
UPDATE inventory SET label = 'Maker''s kit' WHERE sku = 103;
UPDATE inventory SET price = +price WHERE price != 0;
UPDATE inventory SET quantity = -quantity WHERE quantity < 0;
UPDATE inventory SET quantity = 1;
UPDATE inventory SET sku = sku + 1000, label = 'Migrated' WHERE sku < 100;
UPDATE inventory SET price = (price * 9) / 10 WHERE quantity > 5 AND price >= 10;
UPDATE inventory SET label = '' WHERE quantity = 0;
UPDATE inventory SET label = 'Café supplies' WHERE label = 'Cafe';
UPDATE inventory SET quantity = quantity + (2 * 3) WHERE NOT quantity > 10;
UPDATE inventory SET price = quantity + 1 WHERE sku >= 50 AND sku <= 60;
UPDATE inventory SET quantity = price - quantity WHERE price > quantity;
UPDATE inventory SET price = price, label = label WHERE FALSE OR sku = 104;
UPDATE "inventory" SET "label" = 'Checked;ready', "price" = -(-price) WHERE NOT (quantity < 0 OR price < 0);
UPDATE flags SET enabled = TRUE WHERE id = 201;
UPDATE flags SET enabled = FALSE WHERE enabled;
UPDATE flags SET enabled = NOT enabled WHERE id != 0;
UPDATE flags SET label = 'Active', enabled = TRUE WHERE NOT enabled;
UPDATE flags SET enabled = enabled AND TRUE;
UPDATE flags SET enabled = enabled OR FALSE WHERE label != '';
UPDATE flags SET enabled = id > 10 WHERE id >= 0;
UPDATE flags SET enabled = NOT (id = 0 OR enabled = FALSE), label = 'Reviewed' WHERE TRUE;
UPDATE flags SET id = id + 1, label = 'Next', enabled = TRUE != FALSE WHERE enabled = TRUE;
UPDATE "flags" SET "enabled" = NOT NOT enabled, "label" = 'It''s enabled' WHERE enabled AND NOT FALSE;
"""),
    "delete": statements("""
DELETE FROM users;
DELETE FROM users WHERE id = 1;
DELETE FROM users WHERE age < 18;
DELETE FROM users WHERE age <= 0;
DELETE FROM users WHERE age > 100;
DELETE FROM users WHERE age >= 120;
DELETE FROM users WHERE name = '';
DELETE FROM users WHERE city != 'Paris';
DELETE FROM users WHERE name <> 'Protected';
DELETE FROM users WHERE age < 18 AND city = 'Closed';
DELETE FROM users WHERE city = 'A' OR city = 'B';
DELETE FROM users WHERE NOT age >= 18;
DELETE FROM users WHERE NOT (age < 18 OR city = 'Open');
DELETE FROM users WHERE age + 1 = 21;
DELETE FROM users WHERE age - 10 < 0;
DELETE FROM users WHERE age * 2 > 200;
DELETE FROM users WHERE age / 10 = 0;
DELETE FROM users WHERE -age > +id;
DELETE FROM users WHERE name = 'O''Brien' AND city = 'Québec';
DELETE FROM "users" WHERE (id = 0 OR name = '') AND NOT FALSE;
DELETE FROM inventory;
DELETE FROM inventory WHERE sku = 101;
DELETE FROM inventory WHERE quantity = 0;
DELETE FROM inventory WHERE price < 0;
DELETE FROM inventory WHERE price <= 1;
DELETE FROM inventory WHERE quantity > 1000;
DELETE FROM inventory WHERE quantity >= 500;
DELETE FROM inventory WHERE label != 'Keep';
DELETE FROM inventory WHERE label <> '';
DELETE FROM inventory WHERE price = 0 AND quantity = 0;
DELETE FROM inventory WHERE sku < 10 OR sku > 999;
DELETE FROM inventory WHERE NOT quantity > 0;
DELETE FROM inventory WHERE NOT (price > 0 AND quantity > 0);
DELETE FROM inventory WHERE price * quantity < 10;
DELETE FROM inventory WHERE quantity - 5 <= 0;
DELETE FROM inventory WHERE price / 2 = 0;
DELETE FROM inventory WHERE +price = -quantity;
DELETE FROM inventory WHERE label = 'Maker''s kit';
DELETE FROM inventory WHERE (price + quantity) * 2 >= 100 AND label = 'Sale';
DELETE FROM "inventory" WHERE TRUE AND NOT (sku != 0);
DELETE FROM flags;
DELETE FROM flags WHERE enabled;
DELETE FROM flags WHERE NOT enabled;
DELETE FROM flags WHERE enabled = TRUE;
DELETE FROM flags WHERE enabled != FALSE;
DELETE FROM flags WHERE id > 10 AND enabled;
DELETE FROM flags WHERE label = '' OR NOT enabled;
DELETE FROM flags WHERE NOT (enabled OR id < 0);
DELETE FROM flags WHERE NOT NOT enabled AND TRUE;
DELETE FROM "flags" WHERE (enabled = FALSE OR label = 'Expired') AND id >= +1;
"""),
}

SCHEMA = {
    "tables": [
        {
            "name": table_name,
            "columns": [{"name": name, "type": kind} for name, kind in columns],
        }
        for table_name, columns in [
            ("users", [("id", "int"), ("age", "int"), ("name", "text"), ("city", "text")]),
            ("inventory", [("sku", "int"), ("price", "int"), ("quantity", "int"), ("label", "text")]),
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
        parser.exit(1, "Stale CRUD fixtures: " + ", ".join(stale) + "\n")
    print(f"{'Checked' if args.check else 'Generated'} 50 examples each for SELECT, INSERT, UPDATE, DELETE (200 total).")


if __name__ == "__main__":
    main()
