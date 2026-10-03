# SQLean

A Lean 4 SQL parser with public AST interfaces, canonical SQL rendering, and proof-carrying static validation. It supports SELECT with joins, grouping, aggregates, derived tables, ordinary and recursive CTEs, UNION/UNION ALL, and queries without FROM, plus single-table INSERT, UPDATE, and DELETE. The project uses Lean **4.34.0**, with no external Lean package dependencies.

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
```

The Lean test executable checks syntax, expression precedence, schema and type errors, certificates, and SQL round trips. The Python checks use only the standard library. The generators check that example files match their deterministic source; the CLI checks independently compile each example and its rendered SQL using SQLite `EXPLAIN`, without executing mutations. The relational and industrial checks also compare SELECT results on empty and seeded SQLite databases. Recursive examples use finite data or explicit bounds, and the industrial checker caps SQLite execution work.

There are **50 examples per new query category**, 50 per CRUD category, and the original 100 SELECT examples:

| Category | Examples | New functionality |
| --- | --- | --- |
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

Every corpus statement is parsed, certified against its schema, rendered, and reparsed with equal ASTs. Each line is a separate input; passing an entire corpus file to the single-statement CLI is an error. Regenerate fixtures with `python3 scripts/generate_crud_examples.py`, `python3 scripts/generate_relational_examples.py`, and `python3 scripts/generate_industrial_examples.py`.

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

The CLI prints canonical SQL; `--ast` selects AST output. `--schema` additionally validates the statement and reports selected output types (or the mutation category). Syntax/validation failures exit with status 1; invalid CLI arguments exit with status 2. Parsing or certifying an INSERT, UPDATE, or DELETE does not execute it.

Schemas are supplied externally as JSON:

```json
{"tables":[{"name":"flags","columns":[{"name":"id","type":"int"},{"name":"enabled","type":"bool"},{"name":"label","type":"text"}]}]}
```

JSON schema input types are `int`, `text`, and `bool`. Table/column names must be nonempty and unique in their scope, and tables must have columns. Schema names are exact; ordinary unquoted SQL identifiers normalize to lowercase. [The CRUD schema](fixtures/crud/schema.json) contains `users`, `inventory`, and `flags`; [the relational schema](fixtures/relational/schema.json) contains users, orders, departments, employees, and flags. JSON schema columns are required and non-null, with no default values. Consequently INSERT must supply every column, either in schema order or through a complete explicit column list. The Lean `SqlType` API also represents `real` and `nullable` result types, for example the output of AVG and outer joins.

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

CTEs are checked sequentially: each can use earlier bindings and the outer schema. A binding shadows an outer relation with the same name; duplicate names in one WITH list are rejected. Derived tables and CTEs may nest. They expose the natural names of selected columns and explicit result aliases. Computed outputs at these boundaries require `AS name` (or a bare alias); a CTE's explicit column list can instead supply all output names. The column list must match the result arity. Duplicate output names are rejected at a derived-table/CTE boundary, so alias columns when a joined projection would otherwise repeat a name. Nested queries cannot refer to enclosing FROM aliases.

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

`UNION` removes duplicate rows, while `UNION ALL` preserves them when executed by a database. Any number of nonrecursive arms can be combined. Validation requires equal arity and identical output types, including nullability; implicit database type coercions are outside this subset. Output names come from the first SELECT. A compound query's final ORDER BY accepts an unambiguous output name or a positive integer literal denoting a one-based output position; arbitrary expressions and source-qualified names are rejected. Final ORDER BY, LIMIT, and OFFSET apply to the whole compound. To sort or limit an individual input, wrap it in an aliased derived table.

SELECT without FROM uses an empty column scope. Constants, expressions, filters, and supported aggregate expressions can be checked; unbound columns and wildcards are rejected. This supplies constant anchors and seed relations without requiring a physical table.

This portable recursive shape follows the shared anchor/step structure documented by [PostgreSQL](https://www.postgresql.org/docs/current/queries-with.html) and [SQLite](https://www.sqlite.org/lang_with.html). Static certification does not establish termination or detect data cycles. A recursive query can be well typed and run indefinitely; callers must choose appropriate predicates or a suitable deduplicating UNION for their data.

The extended grammar accepted by `parseStatement` is:

```ebnf
statement = (select | insert | update | delete) [";"] ;
select    = [WITH [RECURSIVE] cte {"," cte}]
            selectCore {UNION [ALL] selectCore}
            [ORDER BY orderItem {"," orderItem}]
            [LIMIT integer [OFFSET integer]] ;
selectCore = SELECT [DISTINCT] selectItem {"," selectItem}
             [FROM source {join}]
             [WHERE expr] [GROUP BY exprList] [HAVING expr] ;
cte       = identifier ["(" identifier {"," identifier} ")"] AS "(" select ")" ;
source    = identifier [[AS] identifier] | "(" select ")" [AS] identifier ;
join      = [INNER] JOIN source ON expr
          | (LEFT | RIGHT | FULL) [OUTER] JOIN source ON expr
          | CROSS JOIN source ;
selectItem = "*" | identifier "." "*" | expr [[AS] identifier] ;
insert    = INSERT INTO identifier ["(" identifier {"," identifier} ")"]
            VALUES row {"," row} ;
row       = "(" exprList ")" ;
update    = UPDATE identifier SET assignment {"," assignment} [WHERE expr] ;
assignment = identifier "=" expr ;
delete    = DELETE FROM identifier [WHERE expr] ;
orderItem = expr [ASC | DESC] ;
exprList  = expr {"," expr} ;
expr      = orExpr ;
orExpr    = andExpr {OR andExpr} ;
andExpr   = notExpr {AND notExpr} ;
notExpr   = {NOT} cmpExpr ;
cmpExpr   = addExpr [("=" | "<>" | "!=" | "<" | "<=" | ">" | ">=") addExpr
                    | IS [NOT] NULL] ;
addExpr   = mulExpr {("+" | "-") mulExpr} ;
mulExpr   = unaryExpr {("*" | "/") unaryExpr} ;
unaryExpr = {"+" | "-"} primary ;
primary   = identifier ["." identifier] | integer | string | TRUE | FALSE
          | "(" expr ")" | COUNT "(" "*" ")"
          | (COUNT | SUM | AVG | MIN | MAX) "(" [DISTINCT] expr ")" ;
```

Qualification, IS NULL, and aggregate expressions extend SELECT only; INSERT, UPDATE, and DELETE retain their existing unqualified expression grammar. Aggregates take one expression, except COUNT(*). COUNT(DISTINCT *) is rejected. Ordinary columns named `count`, `sum`, `avg`, `min`, or `max` remain usable without parentheses. Nested SELECTs cannot contain semicolons.

Multiplication/division bind before addition/subtraction, then comparisons and IS NULL, `NOT`, `AND`, and `OR`. Unary signs bind most tightly. Binary chains associate left; comparison chains such as `a < b < c` are rejected. Integers are arbitrary-precision decimal numerals; a leading sign is a separate unary AST node. `LIMIT` and `OFFSET` take unsigned literals, and OFFSET requires LIMIT.

GROUP BY and ORDER BY accept expressions, whole-key result aliases, or one-based selected-column positions. Zero, negative, and out-of-range positions are rejected by validation. GROUP BY prefers an input column when its name conflicts with a result alias; ORDER BY prefers the result alias. Aliases inside larger expressions and aliases in HAVING are not substituted. With DISTINCT, sort expressions must occur in the selected projection after alias/ordinal expansion. Wildcards expand in FROM/JOIN column order.

An aggregate query's SELECT, HAVING, and ORDER BY expressions must use grouping keys, constants, aggregates, or expressions built from them. GROUP BY expressions are compared structurally after resolving column names, so an unqualified column and its uniquely resolved qualified form agree. Functional dependencies, such as assuming another column is determined by a grouped primary key, are not inferred. Aggregates are forbidden in WHERE, ON, GROUP BY, and arguments to other aggregates. HAVING also creates an aggregate query when GROUP BY is absent.

This is a documented SQL subset, not complete compatibility with any database dialect. Unsupported forms include scalar/IN/EXISTS subqueries, correlated or LATERAL subqueries, USING/NATURAL joins, INTERSECT/EXCEPT, recursive SEARCH/CYCLE clauses, window functions, general function calls, `RETURNING`, UPSERT, INSERT-SELECT, NULL/default literals, decimal literals, parameter placeholders, DDL, and transaction commands. IS NULL tests and nullable output types are supported despite NULL literals being outside the grammar. Exactly one statement and at most one trailing semicolon are accepted.

Keywords are case-insensitive. Unquoted identifiers use ASCII letters or `_`, followed by ASCII letters, digits, or `_`. Double-quoted identifiers preserve spelling and allow reserved words; see `Parser.crudReservedWords` and `Parser.relationalReservedWords`. Escape quotes by doubling them: `'O''Brien'` and `"a""b"`. Empty quoted identifiers are rejected. Strings and quoted identifiers support Unicode. `--` line comments and nonnested `/* ... */` comments are accepted. Parse errors carry a zero-based character offset and one-based line/column positions.

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
| `Statement`, `SelectQuery`, `InsertQuery`, `UpdateQuery`, `DeleteQuery` | Public CRUD syntax constructors. |
| `Projection`, `OrderBy`, `Assignment`, `Expr`, `BinOp`, `UnOp`, `Value` | Public syntax components. |
| `RelQuery`, `RelExpr`, `TableRef`, `Join`, `JoinKind`, `SelectItem`, `RelOrderBy`, `AggregateFn`, `CTE`, `UnionBranch` | Public syntax for relational SELECTs, nested sources, and compounds. |
| `Schema`, `TableDef`, `ColumnDef`, `SqlType` | External table and column definitions. |
| `parseStatement` | `String → Except ParseError Statement`; consumes the complete input. |
| `parseRelQuery` | `String → Except ParseError RelQuery`; always returns the relational AST. |
| `ToSql` / `toSql` | SQL rendering with escaped identifiers/strings and explicit parentheses. |
| `certifyStatement schema statement` | `CertifiedStatement schema statement`, containing `outputTypes` and a validity proof. |
| `checkStatement schema statement` | Output types or a validation error; mutations have no selected output columns. |
| `parseAndValidateStatement schema source` | A parsed AST and its certificate packaged as `CheckedStatement schema`. |
| `parseAndValidateRelQuery schema source` | A uniform relational AST and its certificate packaged as `CheckedRelQuery schema`. |
| `certifyRelQuery schema query` | `CertifiedRelQuery schema query`, with output types, names, and proofs for the query and its nested sources. |
| `checkRelQuery schema query` | Relational result types or a validation error. |
| `Query`, `parseQuery` / `parse`, `certifyQuery`, `checkQuery`, `parseAndValidate` | The original SELECT API, retained for compatibility. |

The original `parseQuery` source parser retains its strict MVP grammar and reserved-name policy, including mandatory FROM. `parseStatement` returns `.select` for every previously accepted SELECT and `.relational` for the new syntax; INSERT/UPDATE/DELETE constructors are unchanged. Use `parseRelQuery` or `parseAndValidateRelQuery` when callers need one consistent relational AST even for simple SELECTs. Low-level token APIs `Parser.parseTokens`, `Parser.parseStatementTokens`, and `Parser.parseRelQueryTokens` expect lexer-produced tokens with exactly one final EOF.

In the relational AST, `recursive` records the WITH RECURSIVE modifier, and `unions` holds the subsequent `UnionBranch` arms in order (`all = true` for UNION ALL). The root query owns global sorting and pagination. A source with an empty name, no alias, and no derived query denotes absent FROM. Validation rejects malformed hand-built AST combinations as well as invalid parsed queries.

Static validity requires a well-formed schema, existing relations, and uniquely resolved, correctly typed expressions. A table alias hides that table's original qualifier. Unqualified column names must identify exactly one visible column; duplicate relation aliases are rejected. ON sees the preceding relations and the current JOIN source, so it cannot reference a later JOIN. CROSS JOIN forbids ON; all other supported joins require it.

Relational arithmetic accepts integer/real operands; ordered comparisons accept numeric pairs or two text operands. Equality accepts matching base types or a numeric pair. Logical operators and predicates require boolean base types. The original CRUD expression checker retains its integer arithmetic/comparison rules. INSERT checks target uniqueness/coverage and every row's arity/types, evaluating expression types in an empty column environment. UPDATE checks unique assignment targets and matching value types against the original table environment, so swaps such as `SET id = age, age = id` typecheck. UPDATE and DELETE without WHERE are valid.

Outer joins make the unmatched side's result types nullable: right for LEFT, left for RIGHT, both for FULL. Arithmetic, comparisons, and logical operators propagate nullable inputs; IS NULL and IS NOT NULL return non-null booleans. Predicates accept nullable booleans. COUNT returns a non-null integer. SUM returns a nullable numeric type, AVG a nullable real, and MIN/MAX a nullable numeric or text type. These are static type annotations; the parser and checker do not evaluate SQL values or use WHERE clauses to narrow nullability.

The declarative typing and validity relations are separate from their executable checkers. Lean checks soundness and completeness equivalences for the original query checker, the relational core, and complete nested queries, including:

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

The full relational certificate composes child query proofs, CTE scope extensions, recursive anchor/step checks, compound output compatibility, output naming checks, and the flat core derivation. `checkRelQuery_iff` establishes that the full checker accepts exactly the queries satisfying `ValidRelQuery` for the supplied schema and AST. The statement certificate API and its equivalence theorem also cover relational SELECTs. These proofs use standard Lean axioms; there are no `sorry` placeholders or custom axioms.

These are static guarantees. The parser/renderer have regression and round-trip tests, not general grammar-correctness or round-trip proofs. The library does not execute queries or prove row-level constraints, division safety, recursive termination/cycle safety, write effects, transaction behavior, or ACID properties. For example, `1 / 0` remains well typed. SQLite compilation and result comparisons are additional test evidence, not a formal semantic equivalence claim.
