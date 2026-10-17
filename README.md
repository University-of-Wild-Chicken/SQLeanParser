# SQLean

A Lean 4 SQL parser with public AST interfaces, canonical SQL rendering, and proof-carrying static validation. It supports SELECT with joins, grouping, aggregates, derived tables, ordinary and recursive CTEs, UNION/UNION ALL, and queries without FROM, plus single-table INSERT, UPDATE, and DELETE. PostgreSQL extensions include DISTINCT ON, aggregate FILTER, casts, LIKE/ILIKE, IN/BETWEEN, NULLS ordering, and mutation RETURNING. The advanced statement interface also supports correlated IN/EXISTS and scalar subqueries, LATERAL, USING/NATURAL joins, INTERSECT/EXCEPT, ON CONFLICT, INSERT SELECT, NULL, exact decimal/exponent literals, typed parameters, and table DDL. The project uses Lean **4.34.0**, with no external Lean package dependencies.

Build and test from the repository root:

```sh
lake build
lake exe sqlean_tests
python3 scripts/generate_crud_examples.py --check
python3 scripts/check_crud_cli.py
python3 scripts/generate_relational_examples.py --check
python3 scripts/check_relational_cli.py
python3 scripts/generate_industrial_examples.py --check
python3 scripts/check_industrial_cli.py
python3 scripts/generate_postgresql_examples.py --check
python3 scripts/test_postgresql_results.py
python3 scripts/generate_advanced_examples.py --check
```

[GitHub Actions CI](.github/workflows/ci.yml) runs on pushes, pull requests, and
manual dispatch. A Python job runs all offline regression tests and checks all
five generated corpora. A second job builds the library, CLI, and test executable
from scratch using `lean-toolchain`, runs the Lean and SQLite suites, then runs
both PostgreSQL corpora and the actual parameter-execution check against
PostgreSQL 16. Both jobs use Ubuntu 24.04 and Python 3.12. PostgreSQL checks use
temporary private clusters; no database secrets are required. New runs cancel
superseded runs for the same branch or pull request.

To run the PostgreSQL oracle, supply a directory containing `initdb`, `pg_ctl`,
and `psql` (for example, the output of `pg_config --bindir`):

```sh
python3 scripts/check_postgresql_cli.py --local-bin /usr/lib/postgresql/16/bin
```

The checker starts a temporary PostgreSQL cluster with Unix sockets only, tests
original and rendered statements on empty and seeded tables, and removes the
cluster afterward. RETURNING checks compare both result rows and table contents
after each mutation, with savepoint rollbacks between runs. PostgreSQL 16 was
used for this corpus. Alternatively, `--dsn` uses a fresh random schema inside a
rolled-back transaction on a supplied test database; `--psql` selects its client.

The PostgreSQL transport uses `COPY ... CSV FORCE_QUOTE *`: quoted fields are
text (including the literal NULL marker), and only an unquoted marker is SQL
NULL. Offline decoder regressions require neither PostgreSQL nor Lean. Result
arity, row ordering, and RETURNING state comparisons retain their existing
representation. These finite database checks are not a proof of execution
equivalence for arbitrary database states. Run `--local-bin` as a non-root user
(as required by `initdb`).

The Lean test executable checks syntax, expression precedence, schema and type errors, certificates, and SQL round trips. The Python checks use only the standard library. The generators check that example files match their deterministic source; the CRUD, relational, and industrial CLI checks independently compile each example and its rendered SQL using SQLite `EXPLAIN`, without executing mutations. The relational and industrial checks also compare SELECT results on empty and seeded SQLite databases. Recursive examples use finite data or explicit bounds, and the industrial checker caps SQLite execution work. The PostgreSQL checker performs 600 source/canonical result comparisons, 100 RETURNING mutation-state comparisons, and 36 independently specified result checks.

The compatibility corpora contain **50 examples per added query category**, 50 per CRUD category, and the original 100 SELECT examples. The 750 advanced examples are listed later in this README:

| Category | Examples | New functionality |
| --- | --- | --- |
| DISTINCT ON | [50 examples](fixtures/postgresql/distinct_on.sql) | First row per key, expressions, aliases, ordinals, and grouping. |
| Aggregate FILTER | [50 examples](fixtures/postgresql/aggregate_filter.sql) | Conditional COUNT/SUM/AVG/MIN/MAX in projections, HAVING, and sorting. |
| Casts | [50 examples](fixtures/postgresql/casts.sql) | PostgreSQL `::` and standard CAST, with explicit scalar targets. |
| Predicates | [50 examples](fixtures/postgresql/predicates.sql) | LIKE/ILIKE, IN lists, BETWEEN, and their NOT forms. |
| NULLS ordering | [50 examples](fixtures/postgresql/null_ordering.sql) | FIRST/LAST with ascending/descending, outer joins, aggregates, and compounds. |
| RETURNING | [50 examples](fixtures/postgresql/returning.sql) | INSERT/UPDATE/DELETE result projections, wildcards, aliases, and scalar expressions. |
| Recursive CTEs | [50 examples](fixtures/industrial/recursive_ctes.sql) | Bounded sequences, employee hierarchies, graph reachability, and bills of materials. |
| Unions | [50 examples](fixtures/industrial/unions.sql) | UNION/UNION ALL, multiple arms, global ordering/pagination, unions inside CTEs and derived tables. |
| SELECT without FROM | [50 examples](fixtures/industrial/source_free.sql) | Constant projections, arithmetic, predicates, aggregate results, and constant seed relations. |
| Joins | [50 examples](fixtures/relational/joins.sql) | INNER, LEFT, RIGHT, FULL, CROSS, aliases, qualified columns, wildcards, null checks. |
| Grouping and aggregates | [50 examples](fixtures/relational/grouping.sql) | GROUP BY, HAVING, COUNT/SUM/AVG/MIN/MAX, DISTINCT aggregates, aliases and ordinals. |
| Derived-table subqueries | [50 examples](fixtures/relational/subqueries.sql) | SELECT in FROM or JOIN, nested queries, named outputs, aggregate results. |
| Nonrecursive CTEs | [50 examples](fixtures/relational/ctes.sql) | WITH, multiple bindings, column lists, nested WITH, references to earlier bindings. |
| Read / SELECT | [50 examples](fixtures/crud/select.sql) | `*`, `DISTINCT`, sorting, pagination, boolean literals and unary expressions. |
| Create / INSERT | [50 examples](fixtures/crud/insert.sql) | Implicit/explicit target columns, reordered columns, multiple rows, constant expressions. |
| Update / UPDATE | [50 examples](fixtures/crud/update.sql) | One or several assignments, column-based expressions, optional filters. |
| Delete / DELETE | [50 examples](fixtures/crud/delete.sql) | Optional filters, comparisons, boolean combinations. |
| Original SELECT MVP | [100 examples](fixtures/queries.sql) | Regression coverage for the original expression grammar and API. |

Every corpus statement is parsed, certified against its schema, rendered, and reparsed with equal ASTs using the corresponding API. The original PostgreSQL SELECT corpus uses the uniform `parseRelQuery` interface, since normalized BETWEEN expressions can also fit the legacy grammar. The advanced corpus uses `Advanced.parse` and `Advanced.render` to keep its AST interface stable. Each line is a separate input; passing an entire corpus file to the single-statement CLI is an error. Regenerate fixtures with the corresponding `scripts/generate_*_examples.py` script.

Use the CLI with one SQL argument, a file containing one statement, or standard input:

```sh
lake exe sqlean 'SELECT * FROM users ORDER BY age DESC LIMIT 10 OFFSET 20'
lake exe sqlean --ast 'UPDATE users SET age = age + 1 WHERE id = 7'
lake exe sqlean --schema fixtures/crud/schema.json \
  "INSERT INTO users (id, age, name, city) VALUES (1, 30, 'Ada', 'London'), (2, 25, 'Grace', 'Paris')"
lake exe sqlean --schema fixtures/crud/schema.json 'DELETE FROM users WHERE age < 18'
lake exe sqlean --schema fixtures/relational/schema.json \
  'SELECT u.name, o.amount FROM users u LEFT JOIN orders o ON u.id = o.user_id'
lake exe sqlean --file statement.sql
printf '%s\n' 'SELECT id FROM users' | lake exe sqlean
```

The CLI prints canonical SQL; `--ast` selects AST output. `--schema` additionally validates the statement and reports selected/RETURNING output types (or the mutation category when no rows are returned). Syntax/validation failures exit with status 1; invalid CLI arguments exit with status 2. Parsing or certifying SQL does not execute it. DDL validation reports an in-memory catalog transition without changing a database.

Schemas are supplied externally as JSON:

```json
{"tables":[{"name":"flags","columns":[{"name":"id","type":"int"},{"name":"enabled","type":"bool"},{"name":"label","type":"text"}]}]}
```

JSON schema input types are `int`, `text`, `bool`, and `real`; columns may specify `"nullable": true` and otherwise default to non-null. Table/column names must be nonempty and unique in their scope, and tables must have columns. Schema names are exact; ordinary unquoted SQL identifiers normalize to lowercase. [The CRUD schema](fixtures/crud/schema.json) contains `users`, `inventory`, and `flags`; [the relational schema](fixtures/relational/schema.json) contains users, orders, departments, employees, and flags. These compatibility fixtures contain only required, non-null columns without defaults, so their INSERT statements must supply every column. `parseSchemaJson` returns the original `Schema` interface; `Advanced.parseCatalogJson` additionally preserves defaults and key metadata, as described with the advanced catalog API below. The CLI uses that catalog decoder and selects advanced validation when the schema needs its richer metadata.

For example, join orders before grouping customers and filter by their number of matching orders:

```sql
SELECT u.id, u.name, COUNT(o.id) AS order_count, SUM(o.amount) AS total
FROM users AS u
LEFT JOIN orders AS o ON u.id = o.user_id
GROUP BY u.id, u.name
HAVING COUNT(o.id) >= 1
ORDER BY total DESC;
```

A derived table names the result of a nested SELECT. Its alias is required:

```sql
SELECT totals.user_id, totals.total
FROM (
  SELECT user_id, SUM(amount) AS total
  FROM orders
  GROUP BY user_id
) AS totals
WHERE totals.total > 100;
```

WITH gives a query result a name usable by later bindings and the main SELECT:

```sql
WITH totals (customer_id, total) AS (
  SELECT user_id, SUM(amount) FROM orders GROUP BY user_id
), large_orders AS (
  SELECT customer_id, total FROM totals WHERE total > 100
)
SELECT u.name, large_orders.total
FROM users u
JOIN large_orders ON u.id = large_orders.customer_id;
```

In the original relational API, CTEs are checked sequentially: each can use earlier bindings and the outer schema. A binding shadows an outer relation with the same name; duplicate names in one WITH list are rejected. Derived tables and CTEs may nest. They expose the natural names of selected columns and explicit result aliases. Computed outputs at these boundaries require `AS name` (or a bare alias); a CTE's explicit column list can instead supply all output names. The column list must match the result arity. Duplicate output names are rejected at a derived-table/CTE boundary, so alias columns when a joined projection would otherwise repeat a name. This original API does not allow references to enclosing FROM aliases; the advanced API adds correlated subqueries and LATERAL sources.

Recursive CTEs support an anchor followed by one recursive step. For example, a bounded integer sequence works with an empty schema:

```sql
WITH RECURSIVE sequence(n) AS (
  SELECT 1
  UNION ALL
  SELECT n + 1 FROM sequence WHERE n < 10
)
SELECT n FROM sequence ORDER BY n;
```

The same pattern follows a hierarchy using a join in the step:

```sql
WITH RECURSIVE team(id, manager_id, name, depth) AS (
  SELECT id, manager_id, name, 0 FROM employees WHERE id = 1
  UNION ALL
  SELECT e.id, e.manager_id, e.name, t.depth + 1
  FROM employees e JOIN team t ON e.manager_id = t.id
  WHERE t.depth < 20
)
SELECT name, depth FROM team ORDER BY depth, name;
```

The supported recursive shape is `anchor UNION [ALL] step`. The anchor cannot refer to its own CTE. The recursive body cannot carry a top-level WITH, ORDER BY, LIMIT, or OFFSET; place final sorting and pagination on the outer SELECT. The step must reference the CTE exactly once directly in FROM or JOIN; it may use INNER/CROSS joins and filters. Recursive steps cannot contain aggregates, GROUP BY, HAVING, DISTINCT, nested sources/CTEs, or further unions. Anchor and step outputs must have identical type vectors, including nullability, and the CTE's output names come from its explicit column list or the anchor. Earlier CTEs are visible; forward and mutual recursion are rejected. Under WITH RECURSIVE, names of current and later bindings are reserved rather than resolved to equally named physical tables. Ordinary CTEs are also allowed in a WITH RECURSIVE list.

`UNION` removes duplicate rows, while `UNION ALL` preserves them when executed by a database. Any number of nonrecursive arms can be combined. The original relational validator requires equal arity and identical output types, including nullability. The advanced validator also computes supported common numeric/nullable types for set operations; it does not model every PostgreSQL coercion. Output names come from the first SELECT. A compound query's final ORDER BY accepts an unambiguous output name or a positive integer literal denoting a one-based output position; arbitrary expressions and source-qualified names are rejected. Final ORDER BY, LIMIT, and OFFSET apply to the whole compound. The original API requires an aliased derived table to sort or limit an individual input. Advanced set operations also accept parenthesized operands with their own sorting and pagination.

SELECT without FROM uses an empty column scope. Constants, expressions, filters, and supported aggregate expressions can be checked; unbound columns and wildcards are rejected. This supplies constant anchors and seed relations without requiring a physical table.

This portable recursive shape follows the shared anchor/step structure documented by [PostgreSQL](https://www.postgresql.org/docs/current/queries-with.html) and [SQLite](https://www.sqlite.org/lang_with.html). Static certification does not establish termination or detect data cycles. A recursive query can be well typed and run indefinitely; callers must choose appropriate predicates or a suitable deduplicating UNION for their data.

PostgreSQL's DISTINCT ON keeps the first row for each key. For deterministic choices, provide enough ORDER BY keys to break ties:

```sql
SELECT DISTINCT ON (user_id) user_id, id, amount
FROM orders
ORDER BY user_id, amount DESC, id;
```

DISTINCT ON keys are resolved like ORDER BY keys, including aliases and output positions. The initial ORDER BY keys must come from DISTINCT ON; all DISTINCT ON keys must have appeared before an unrelated sort key. Permutations, repeated keys, and shorter all-matching initial orders are accepted. Omitting ORDER BY is permitted but does not select a predictable representative. DISTINCT ON keys also obey expression typing and grouping rules; ordinary DISTINCT and DISTINCT ON cannot coexist in a hand-built AST. See PostgreSQL's [SELECT documentation](https://www.postgresql.org/docs/current/sql-select.html).

FILTER selects the input rows for one aggregate:

```sql
SELECT user_id,
       COUNT(*) FILTER (WHERE status = 'paid') AS paid_orders,
       SUM(amount) FILTER (WHERE status = 'paid') AS paid_total
FROM orders
GROUP BY user_id
ORDER BY paid_total DESC NULLS LAST, user_id;
```

FILTER attaches directly to COUNT(*) or COUNT/SUM/AVG/MIN/MAX, including DISTINCT arguments. Its predicate must be boolean and cannot contain aggregates. It does not change the aggregate's output type or make a nullable aggregate non-null. NULLS FIRST/LAST is stored independently of ASC/DESC and works on ordinary and compound query ordering. FILTER follows PostgreSQL's [aggregate-expression syntax](https://www.postgresql.org/docs/current/sql-expressions.html#SYNTAX-AGGREGATES).

In the original relational API, `expr::type` and `CAST(expr AS type)` accept INT/INTEGER, TEXT, BOOL/BOOLEAN, REAL, and DOUBLE PRECISION. `CastType` preserves REAL versus DOUBLE PRECISION so rendering preserves the requested precision; both belong to the static `SqlType.real` family. Supported conversions are identity, conversions to/from text, integer/real conversions, and integer/boolean conversions. Casts preserve nullability. Certification checks that a conversion is supported, not that textual values parse or numeric values fit at execution time. The advanced API adds BIGINT, VARCHAR, NUMERIC, and supported length/precision/scale modifiers through `Advanced.DataType`. Arrays and user-defined cast targets remain unsupported.

Both expression APIs and RETURNING projections accept LIKE/ILIKE, nonempty IN expression lists, BETWEEN bounds, and their NOT variants. LIKE/ILIKE require text operands and propagate nullability. IN remains a dedicated AST node and renders as IN, preserving PostgreSQL's common-type coercion across its operands. The original `RelExpr` normalizes BETWEEN into two inclusive comparisons joined by AND. `Advanced.Expr` keeps a dedicated BETWEEN node, preserving parameter identity and nested expressions during rendering. Advanced expressions also support IN subqueries. BETWEEN SYMMETRIC, explicit ESCAPE clauses, and volatile functions remain unsupported. PostgreSQL documents LIKE/ILIKE in [pattern matching](https://www.postgresql.org/docs/current/functions-matching.html).

Mutation RETURNING exposes the affected row through the same rich projection syntax:

```sql
UPDATE users SET age = age + 1 WHERE id = 7
RETURNING id, age, name ILIKE 'a%' AS starts_with_a;

DELETE FROM orders WHERE status = 'cancelled'
RETURNING orders.*, CAST(amount AS TEXT) AS amount_text;
```

The statement certificate validates the complete mutation before checking RETURNING. Projection names resolve against the target table; wildcards, qualified columns, aliases, and scalar expressions are supported. Aggregates are forbidden, and the projection must be nonempty. Bare mutations still return an empty output-type list; RETURNING statements report their projection types. The legacy mutation constructors retain their existing expression grammar. The advanced statement constructors add target aliases, ON CONFLICT, rich mutation expressions, and RETURNING subqueries. UPDATE FROM, DELETE USING, and old/new row aliases remain unsupported. The library does not execute mutations or model trigger effects. See PostgreSQL's [RETURNING documentation](https://www.postgresql.org/docs/current/dml-returning.html).

The original relational and CRUD grammar remains available through the compatibility APIs. Its grammar is:

```ebnf
statement = (select | insert | update | delete) [";"] ;
select    = [WITH [RECURSIVE] cte {"," cte}]
            selectCore {UNION [ALL] selectCore}
            [ORDER BY orderItem {"," orderItem}]
            [LIMIT integer [OFFSET integer]] ;
selectCore = SELECT [DISTINCT [ON "(" exprList ")"]] selectItem {"," selectItem}
             [FROM source {join}]
             [WHERE expr] [GROUP BY exprList] [HAVING expr] ;
cte       = identifier ["(" identifier {"," identifier} ")"] AS "(" select ")" ;
source    = identifier [[AS] identifier] | "(" select ")" [AS] identifier ;
join      = [INNER] JOIN source ON expr
          | (LEFT | RIGHT | FULL) [OUTER] JOIN source ON expr
          | CROSS JOIN source ;
selectItem = "*" | identifier "." "*" | expr [[AS] identifier] ;
insert    = INSERT INTO identifier ["(" identifier {"," identifier} ")"]
            VALUES row {"," row} [returning] ;
row       = "(" exprList ")" ;
update    = UPDATE identifier SET assignment {"," assignment} [WHERE expr] [returning] ;
assignment = identifier "=" expr ;
delete    = DELETE FROM identifier [WHERE expr] [returning] ;
returning = RETURNING selectItem {"," selectItem} ;
orderItem = expr [ASC | DESC] [NULLS (FIRST | LAST)] ;
exprList  = expr {"," expr} ;
expr      = orExpr ;
orExpr    = andExpr {OR andExpr} ;
andExpr   = notExpr {AND notExpr} ;
notExpr   = {NOT} cmpExpr ;
cmpExpr   = addExpr [("=" | "<>" | "!=" | "<" | "<=" | ">" | ">=") addExpr
                    | IS [NOT] NULL | [NOT] (LIKE | ILIKE) addExpr
                    | [NOT] IN "(" exprList ")" | [NOT] BETWEEN addExpr AND addExpr] ;
addExpr   = mulExpr {("+" | "-") mulExpr} ;
mulExpr   = unaryExpr {("*" | "/") unaryExpr} ;
unaryExpr = {"+" | "-"} primary ;
primary   = atom {"::" castType} ;
atom      = identifier ["." identifier] | integer | string | TRUE | FALSE
          | "(" expr ")" | CAST "(" expr AS castType ")"
          | aggregate [FILTER "(" WHERE expr ")"] ;
aggregate = COUNT "(" "*" ")"
          | (COUNT | SUM | AVG | MIN | MAX) "(" [DISTINCT] expr ")" ;
castType  = INT | INTEGER | TEXT | BOOL | BOOLEAN | REAL | DOUBLE PRECISION ;
```

In this compatibility grammar, qualification, PostgreSQL scalar expressions, IS NULL, and aggregates extend SELECT; RETURNING supports the scalar subset. Legacy INSERT values and UPDATE/DELETE clauses retain their original unqualified expression grammar. Advanced mutations use `Advanced.Expr`, including NULL, decimals, parameters, and subqueries. Aggregates take one expression, except COUNT(*). COUNT(DISTINCT *) is rejected. Ordinary columns named `count`, `sum`, `avg`, `min`, or `max` remain usable without parentheses. Nested SELECTs cannot contain semicolons.

Postfix casts bind before unary signs, followed by multiplication/division, addition/subtraction, the predicate/comparison tier, NOT, AND, and OR. Binary chains associate left. This subset uses a single nonchainable tier for comparison operators, LIKE/ILIKE, IN, BETWEEN, and IS NULL; use parentheses for mixed forms such as `(name LIKE 'a%') = TRUE`. It does not implement PostgreSQL's complete operator precedence table. Comparison chains such as `a < b < c` are rejected. Integers are arbitrary-precision decimal numerals; a leading sign is a separate unary AST node. `LIMIT` and `OFFSET` take unsigned integer literals. The original grammar requires LIMIT before OFFSET; the advanced grammar also permits OFFSET alone.

GROUP BY and ORDER BY accept expressions, whole-key result aliases, or one-based selected-column positions. Zero, negative, and out-of-range positions are rejected by validation. GROUP BY prefers an input column when its name conflicts with a result alias; ORDER BY prefers the output name. Output-name lookup includes natural bare-column names and explicit aliases; repeated names must denote identical expressions after column resolution. Aliases inside larger expressions and aliases in HAVING are not substituted. With DISTINCT, sort expressions must occur in the selected projection after alias/ordinal expansion. Wildcards expand in FROM/JOIN column order.

An aggregate query's SELECT, HAVING, and ORDER BY expressions must use grouping keys, constants, aggregates, or expressions built from them. GROUP BY expressions are compared structurally after resolving column names, so an unqualified column and its uniquely resolved qualified form agree. Functional dependencies, such as assuming another column is determined by a grouped primary key, are not inferred. Aggregates are forbidden in WHERE, ON, GROUP BY, and arguments to other aggregates. HAVING also creates an aggregate query when GROUP BY is absent.

This is a documented SQL subset, not complete compatibility with PostgreSQL. Remaining unsupported forms include recursive SEARCH/CYCLE, window functions, general function calls, JSON/array operators, schema-qualified relation names, DML CTEs, UPDATE FROM, DELETE USING, row-valued IN, per-value DEFAULT, and transaction commands. DDL is limited to the table forms described below; foreign keys, CHECK constraints, views, indexes, sequences, permissions, and schema DDL are not modeled. Exactly one statement and at most one trailing semicolon are accepted.

Keywords are case-insensitive. Unquoted identifiers begin with ASCII letters or `_`, followed by ASCII letters, digits, or `_`; the advanced lexer also permits `$` after the first character. Double-quoted identifiers preserve spelling and allow reserved words. The original reserved-word policies are in `Parser.crudReservedWords` and `Parser.relationalReservedWords`; advanced syntax has its own reserved-word set. Escape quotes by doubling them: `'O''Brien'` and `"a""b"`. Empty quoted identifiers are rejected. Strings and quoted identifiers support Unicode. Both lexers accept `--` line comments and `/* ... */` comments; the advanced lexer additionally supports nested block comments. Parse errors carry a zero-based character offset and one-based line/column positions.

Import `SQLean` to use the library:

```lean
import SQLean
open SQLean

def users : Schema := [
  { name := "users", columns := [⟨"id", .int⟩, ⟨"age", .int⟩] }
]

#eval (parseStatement "SELECT * FROM users ORDER BY age DESC LIMIT 10").map toSql
#eval (parseAndValidateStatement users "UPDATE users SET age = age + 1 WHERE id = 7").map
  (fun checked => checked.certificate.outputTypes)  -- Except.ok []
#eval (parseAndValidateStatement users
  "SELECT age, COUNT(*) AS n FROM users GROUP BY age ORDER BY n DESC").map
  (fun checked => checked.certificate.outputTypes)  -- Except.ok [SqlType.int, SqlType.int]
#eval (parseAndValidateStatement users
  "UPDATE users SET age = age + 1 WHERE id = 7 RETURNING id, age::TEXT").map
  (fun checked => checked.certificate.outputTypes)  -- Except.ok [SqlType.int, SqlType.text]
#eval (parseAndValidateRelQuery users
  "SELECT COUNT(*) FILTER (WHERE age >= 18) AS adults FROM users").map
  (fun checked => checked.certificate.outputTypes)  -- Except.ok [SqlType.int]

-- Request the relational AST even for a simple SELECT.
#eval (parseRelQuery "SELECT id FROM users").map toSql
#eval do
  let query ← (parseRelQuery "SELECT AVG(age) AS mean_age FROM users").mapError toString
  (checkRelQuery users query).mapError toString  -- Except.ok [SqlType.nullable SqlType.real]

-- A uniform relational AST and its certificate, including recursive CTEs.
#eval (parseAndValidateRelQuery []
  "WITH RECURSIVE s(n) AS (SELECT 1 UNION ALL SELECT n + 1 FROM s WHERE n < 5) SELECT n FROM s").map
  (fun checked => checked.certificate.outputTypes)  -- Except.ok [SqlType.int]

-- The original API still accepts the original, strict SELECT MVP grammar.
#eval (parseQuery "SELECT id FROM users").map toSql
#eval (parseAndValidate users "SELECT id FROM users WHERE age >= 18").map
  (fun checked => checked.certificate.outputTypes)  -- Except.ok [SqlType.int]
```

| Interface | Purpose |
| --- | --- |
| `Statement`, `Mutation`, `SelectQuery`, `InsertQuery`, `UpdateQuery`, `DeleteQuery` | Public CRUD and RETURNING syntax constructors. |
| `Projection`, `OrderBy`, `Assignment`, `Expr`, `BinOp`, `UnOp`, `Value` | Public syntax components. |
| `RelQuery`, `RelExpr`, `CastType`, `TableRef`, `Join`, `JoinKind`, `SelectItem`, `RelOrderBy`, `AggregateFn`, `CTE`, `UnionBranch` | Public syntax for relational SELECTs, PostgreSQL expressions, nested sources, and compounds. |
| `Schema`, `TableDef`, `ColumnDef`, `SqlType` | External table and column definitions. |
| `parseStatement` | `String → Except ParseError Statement`; consumes the complete input. |
| `parseRelQuery` | `String → Except ParseError RelQuery`; always returns the relational AST. |
| `ToSql` / `toSql` | SQL rendering with escaped identifiers/strings and explicit parentheses. |
| `certifyStatement schema statement` | `CertifiedStatement schema statement`, containing `outputTypes` and a validity proof. |
| `checkStatement schema statement` | Output types or a validation error; mutations without RETURNING have no output columns. |
| `parseAndValidateStatement schema source` | A parsed AST and its certificate packaged as `CheckedStatement schema`. |
| `parseAndValidateRelQuery schema source` | A uniform relational AST and its certificate packaged as `CheckedRelQuery schema`. |
| `certifyRelQuery schema query` | `CertifiedRelQuery schema query`, with output types, names, and proofs for the query and its nested sources. |
| `checkRelQuery schema query` | Relational result types or a validation error. |
| `Query`, `parseQuery` / `parse`, `certifyQuery`, `checkQuery`, `parseAndValidate` | The original SELECT API, retained for compatibility. |

The original `parseQuery` source parser retains its strict MVP grammar and reserved-name policy, including mandatory FROM. `parseStatement` tries the legacy SELECT grammar first, returning `.select` there and `.relational` for richer SELECT syntax, then falls back to `.extended` for the advanced syntax. RETURNING is reserved in the statement grammar; quote existing identifiers with that name. INSERT/UPDATE/DELETE constructors remain available, and `Statement.returning` wraps a `Mutation` and its output items. Use `parseRelQuery` or `parseAndValidateRelQuery` for the original consistent relational AST, or `Advanced.parse` for the uniform advanced AST. The low-level legacy token APIs retain their original grammar and expect lexer-produced tokens with exactly one final EOF. Shared original syntax types now live in `SyntaxBase.lean`, re-exported by `AST.lean`. The compatibility `certifyStatement schema statement` API checks `.extended` statements with an empty parameter environment and a catalog converted from the original schema. Use `parseAndValidateAdvanced` when parameters, defaults, key metadata, or resulting catalog transitions are needed.

The advanced corpus adds **750 examples, 50 per class**: [IN subqueries](fixtures/advanced/in_subqueries.sql), [EXISTS](fixtures/advanced/exists.sql), [LATERAL](fixtures/advanced/lateral.sql), [USING](fixtures/advanced/using_joins.sql), [NATURAL](fixtures/advanced/natural_joins.sql), [INTERSECT](fixtures/advanced/intersect.sql), [EXCEPT](fixtures/advanced/except.sql), [UPSERT](fixtures/advanced/upsert.sql), [INSERT SELECT](fixtures/advanced/insert_select.sql), [NULL](fixtures/advanced/nulls.sql), [decimal/exponent numbers](fixtures/advanced/floating.sql), [parameters](fixtures/advanced/placeholders.sql), [CREATE TABLE](fixtures/advanced/create_table.sql), [ALTER TABLE](fixtures/advanced/alter_table.sql), and [DROP TABLE](fixtures/advanced/drop_table.sql). Each has independent output-type expectations; parameterized cases also declare parameter types and test values.

Run their database comparisons with PostgreSQL binaries available locally:

```sh
python3 scripts/check_advanced_cli.py --local-bin /usr/lib/postgresql/16/bin
```

The checker performs 1,500 source/canonical result/status comparisons (including 1,180 row-result comparisons), 526 mutation/DDL state comparisons, and 61 independent result/catalog oracles on empty and populated databases. DDL state checks include table/column names, types, defaults, nullability, constraints, and rows. Parameter cases use PostgreSQL PREPARE/EXECUTE as well as COPY result capture; question marks inside quoted text remain text. The script uses temporary databases and the NULL-preserving COPY decoder.

For parameterized statements, `check_advanced_cli.py` currently discards the
PREPARE/EXECUTE output and captures results from typed literal substitution.
Its parameter result oracles therefore directly cover the literal path only.
The separate bounded check below captures actual SQL EXECUTE rows through a
typed PL/pgSQL set-returning bridge and the same NULL-preserving COPY protocol:

```sh
python3 scripts/test_parameter_execution.py  # offline wiring/oracle tests only
python3 scripts/check_parameter_execution.py --local-bin /usr/lib/postgresql/16/bin
# Or: python3 scripts/check_parameter_execution.py --dsn "$TEST_DATABASE_URL"
```

It selects 12 historical placeholder fixtures (2, 17, 22–25, 27, 42, 47–50)
and adds one fixed NULL/marker-text/empty-string case without changing the
historical corpus. On empty and seeded tables, each execution path must match
handwritten expected rows and arity; RETURNING cases also compare database
snapshots after each path. Each path starts from the same savepoint state.
Repeated/out-of-order `$n`, quoted `?`, anonymous parameters, INSERT, UPDATE,
DELETE and UPSERT RETURNING are included. The bridge issues the actual SQL
`EXECUTE sqlean_parameters (...)`; it does not interpolate the prepared query.
Offline tests do not establish PostgreSQL execution success. A successful database
run would establish only these finite source-SQL checks, not CLI canonicalization,
wire-protocol binding, arbitrary SQL adapter correctness, or general semantic
equivalence. Use the local-cluster command as a non-root user.

Advanced queries support correlated IN, NOT IN, EXISTS, NOT EXISTS, and scalar subqueries. IN and scalar subqueries require one output column; scalar subquery results are conservatively nullable, and the checker does not prove at-most-one-row cardinality. Inner scopes shadow outer names. A LATERAL derived table can see preceding sources; ordinary derived tables cannot see sibling sources. LEFT LATERAL joins propagate nullability. USING and NATURAL joins merge unqualified shared columns and wildcard outputs while retaining both qualified original columns. INTERSECT binds more tightly than UNION/EXCEPT; UNION and EXCEPT associate left. ALL variants preserve bag-operation syntax. Parenthesized operands retain their own sorting and pagination.

```sql
SELECT u.id FROM users u
WHERE EXISTS (SELECT 1 FROM orders o WHERE o.user_id = u.id);

SELECT u.id, recent.amount FROM users u
LEFT JOIN LATERAL (
  SELECT amount FROM orders o WHERE o.user_id = u.id ORDER BY id DESC LIMIT 1
) recent ON TRUE;

SELECT id FROM users INTERSECT SELECT user_id FROM orders
EXCEPT SELECT id FROM users WHERE age < 18;

INSERT INTO users (id, age, name, city)
SELECT id + 100, age, name, city FROM users
ON CONFLICT (id) DO UPDATE SET name = excluded.name
RETURNING id, name;
```

NULL is represented independently of text and waits for expression context; a bare selected NULL resolves to nullable text. Decimal and exponent literals retain their exact lexemes, including `.5`, `1.`, and `1.2e-3`; parsing never rounds through a machine float. Decimal/exponent literals and noninteger numeric cast targets use the coarse `SqlType.real` family; integer literals and INT/BIGINT targets use `SqlType.int`. The advanced AST preserves distinctions between NUMERIC, REAL, and DOUBLE PRECISION and retains supported modifiers. Type-name synonyms normalize to canonical SQL names. Numeric range, rounding, overflow, and successful text conversion are runtime concerns.

Both PostgreSQL `$1` parameters and client-style `?` parameters are supported. Anonymous parameters are numbered in source order, starting at one; mixed styles are rejected. Default rendering preserves their style, and `Advanced.renderPostgres` / CLI `--postgres` converts `?` to the corresponding `$n`. A dedicated advanced BETWEEN node prevents parameter duplication during rendering. Validation requires an explicit parameter-type environment; it does not silently guess types for missing bindings.

```sh
lake exe sqlean --param-types int,int,int --postgres 'SELECT ? BETWEEN ? AND ?'
lake exe sqlean --schema fixtures/advanced/schema.json --param-types int \
  'SELECT id FROM users WHERE id = $1'
```

Parameter types are `int,text,bool,real`; a suffix `?` permits NULL values, for example `int,text?`. Schema JSON accepts these same base families with an optional `nullable` Boolean (default false), a `default` SQL-expression string, table `uniqueKeys` arrays, a `primaryKey` column array, and a `namedKeys` object mapping constraint names to column arrays. `Advanced.parseCatalogJson` validates this metadata. ON CONFLICT targets must match a declared unique key or named constraint. DO UPDATE requires a target; its expressions can qualify the target table or `excluded`. Unqualified names shared by both scopes are ambiguous. Omitted INSERT columns require a default or nullable type; INSERT SELECT checks arity and assignment compatibility.

Table DDL supports CREATE TABLE / IF NOT EXISTS, column NULL/NOT NULL and constant DEFAULT expressions, and column/table PRIMARY KEY and UNIQUE constraints. Types include INT/INTEGER, BIGINT, TEXT, VARCHAR with optional length, BOOLEAN, REAL, DOUBLE PRECISION, and NUMERIC with optional precision/scale. ALTER TABLE supports ADD/DROP COLUMN with existence guards, RENAME COLUMN/TO, compatible ALTER COLUMN TYPE, SET/DROP NOT NULL, and SET/DROP DEFAULT. Multiple actions must affect distinct columns; RENAME is standalone. This conservatively avoids PostgreSQL's phase-dependent combinations. DROP TABLE supports IF EXISTS and RESTRICT/CASCADE. The catalog models only tables and local unique/primary constraints, not external dependency graphs or row data.

Use the catalog API to check a DDL sequence and feed each resulting catalog into the next statement:

```lean
import SQLean
open SQLean

def exampleCatalog : Advanced.Catalog := [{
  name := "users"
  columns := [{ name := "id", type := ⟨.int, []⟩, nullable := some false }]
  uniqueKeys := [["id"]] }]

#eval (parseAndValidateAdvanced exampleCatalog [(1, .int)]
  "SELECT EXISTS (SELECT 1 FROM users WHERE id = $1)").map
  (fun checked => checked.result.outputTypes)

#eval do
  let statements ← (["CREATE TABLE items (id INT PRIMARY KEY, label TEXT)",
    "ALTER TABLE items ADD COLUMN price REAL DEFAULT 0.0"].mapM Advanced.parse).mapError toString
  (Advanced.checkStatements [] [] statements).mapError toString
```

Public advanced interfaces include `Advanced.Statement`, `Query`, `Expr`, `From`, `DataType`, `Column`, `Catalog`, `ParameterEnv`, `parse`, `parseQuery`, `parseExpression`, `render`, `renderPostgres`, `checkQuery`, `inferExpr`, `checkStatementDetailed`, `certifyStatement`, and `checkStatements`. `parseAndValidateAdvanced catalog params source` returns the AST, output types, resulting catalog, and a Lean proof that the bounded static checker accepted that result. The advanced certificates attest this algorithmic contract; they are not independent declarative SQL-semantics proofs. The existing declarative proofs remain available for the original constructors.

Advanced validation limits recursive CTEs to the documented portable anchor/step shape and rejects forward references, including physical-table homonyms under WITH RECURSIVE. It conservatively rejects aggregates whose arguments/FILTER refer to an outer query level and some PostgreSQL implicit coercions; explicit casts and local aggregate inputs avoid these cases. Query validation has a depth budget of 1,024 and reports exhaustion as an error. Additional modifiers directly around an already-modified parenthesized query require a derived table. DDL certificates describe schema transitions only: they do not establish that existing rows satisfy a new NOT NULL/unique constraint, that casts succeed, or that a database operation will execute successfully.

In the relational AST, `recursive` records the WITH RECURSIVE modifier, and `unions` holds the subsequent `UnionBranch` arms in order (`all = true` for UNION ALL). The root query owns global sorting and pagination. A source with an empty name, no alias, and no derived query denotes absent FROM. Validation rejects malformed hand-built AST combinations as well as invalid parsed queries.

`RelQuery.distinctOn` holds DISTINCT ON keys and is mutually exclusive with `distinct = true`. `RelOrderBy.nullsFirst` distinguishes the default (`none`), FIRST (`some true`), and LAST (`some false`). `RelExpr.cast`, `pattern`, `filteredAggregate`, and `inList` preserve the corresponding PostgreSQL syntax. `RelExpr.between` supplies the normalized comparison AST; `RelExpr.inValues` builds an IN node whose list must be nonempty for certification.

Static validity requires a well-formed schema, existing relations, and uniquely resolved, correctly typed expressions. A table alias hides that table's original qualifier. Unqualified column names must identify exactly one visible column; duplicate relation aliases are rejected. ON cannot reference a later JOIN. In the original relational API, ON sees preceding relations and the current JOIN source; CROSS JOIN forbids ON and the other join kinds require it. `Advanced.From` preserves join trees and separately represents ON, USING, and NATURAL joins.

Relational arithmetic accepts integer/real operands; ordered comparisons accept numeric pairs or two text operands. Equality accepts matching base types or a numeric pair. Logical operators and predicates require boolean base types. The original CRUD expression checker retains its integer arithmetic/comparison rules. The original INSERT checker requires complete target coverage and checks every row's arity/types in an empty column environment. Advanced INSERT additionally uses catalog defaults/nullability and validates SELECT sources and conflict actions. UPDATE checks unique assignment targets and matching value types against the original table environment, so swaps such as `SET id = age, age = id` typecheck. UPDATE and DELETE without WHERE are valid.

Outer joins make the unmatched side's result types nullable: right for LEFT, left for RIGHT, both for FULL. Arithmetic, comparisons, and logical operators propagate nullable inputs; IS NULL and IS NOT NULL return non-null booleans. Predicates accept nullable booleans. COUNT returns a non-null integer. SUM returns a nullable numeric type, AVG a nullable real, and MIN/MAX a nullable numeric or text type. These are static type annotations; the parser and checker do not evaluate SQL values or use WHERE clauses to narrow nullability.

For the original expression, CRUD, and relational constructors, the declarative typing and validity relations are separate from their executable checkers. Lean checks soundness and completeness equivalences for the original query checker, the relational core, and complete nested queries, including:

```text
inferType_iff:
  inferType columns expr = .ok type ↔ HasType columns expr type
checkQuery_iff:
  checkQuery schema query = .ok types ↔ ValidQuery schema query types
inferRelType_iff:
  inferRelType scope aggregates expr = .ok type ↔ RelHasType scope aggregates expr type
checkRelQueryCore_iff:
  checkRelQueryCore schema query = .ok types ↔ ValidRelQueryCore schema query types
checkRelQuery_iff:
  checkRelQuery schema query = .ok types ↔ ValidRelQuery schema query types
checkStatement_iff:
  checkStatement schema statement = .ok types ↔ ValidStatement schema statement types
```

The full relational certificate composes child query proofs, CTE scope extensions, recursive anchor/step checks, compound output compatibility, output naming checks, and the flat core derivation. `checkRelQuery_iff` establishes that the full checker accepts exactly the queries satisfying `ValidRelQuery` for the supplied schema and AST. The statement certificate API and its equivalence theorem also cover relational SELECTs. The `.extended` constructor embeds the explicitly algorithmic advanced static-check contract described above; it does not add an independent declarative typing derivation for the advanced syntax. These proofs use standard Lean axioms; there are no `sorry` placeholders or custom axioms.

These are static guarantees. The parser/renderer have regression and round-trip tests, not general grammar-correctness or round-trip proofs. The library does not execute queries or prove row-level constraints, division safety, recursive termination/cycle safety, write effects, transaction behavior, or ACID properties. For example, `1 / 0` remains well typed. SQLite and PostgreSQL checks provide additional test evidence, not a formal semantic equivalence claim.
