# SQLean

A Lean 4 SQL parser with public AST interfaces, canonical SQL rendering, and proof-carrying static validation. It supports common single-table SELECT, INSERT, UPDATE, and DELETE statements. The project uses Lean **4.34.0**, with no external Lean package dependencies.

Build and test from the repository root:

```sh
lake build
lake exe sqlean_tests
python3 scripts/generate_crud_examples.py --check
python3 scripts/check_crud_cli.py
```

The Lean test executable checks syntax, expression precedence, schema and type errors, certificates, and SQL round trips. The Python checks use only the standard library: one verifies that example files match the deterministic generator; the other exercises the CLI and independently compiles each new example and its rendered SQL using SQLite `EXPLAIN`, without executing mutations.

There are **50 new examples per CRUD category**, plus the original 100 SELECT examples:

| Category | Examples | New functionality |
| --- | --- | --- |
| Read / SELECT | [50 examples](fixtures/crud/select.sql) | `*`, `DISTINCT`, sorting, pagination, boolean literals and unary expressions. |
| Create / INSERT | [50 examples](fixtures/crud/insert.sql) | Implicit/explicit target columns, reordered columns, multiple rows, constant expressions. |
| Update / UPDATE | [50 examples](fixtures/crud/update.sql) | One or several assignments, column-based expressions, optional filters. |
| Delete / DELETE | [50 examples](fixtures/crud/delete.sql) | Optional filters, comparisons, boolean combinations. |
| Original SELECT MVP | [100 examples](fixtures/queries.sql) | Regression coverage for the original expression grammar and API. |

Every corpus statement is parsed, certified against its schema, rendered, and reparsed with equal ASTs. Each line is a separate input; passing an entire corpus file to the single-statement CLI is an error. Regenerate the new examples with `python3 scripts/generate_crud_examples.py`.

Use the CLI with one SQL argument, a file containing one statement, or standard input:

```sh
lake exe sqlean 'SELECT * FROM users ORDER BY age DESC LIMIT 10 OFFSET 20'
lake exe sqlean --ast 'UPDATE users SET age = age + 1 WHERE id = 7'
lake exe sqlean --schema fixtures/crud/schema.json \
  "INSERT INTO users (id, age, name, city) VALUES (1, 30, 'Ada', 'London'), (2, 25, 'Grace', 'Paris')"
lake exe sqlean --schema fixtures/crud/schema.json 'DELETE FROM users WHERE age < 18'
lake exe sqlean --file statement.sql
printf '%s\n' 'SELECT id FROM users' | lake exe sqlean
```

The CLI prints canonical SQL; `--ast` selects AST output. `--schema` additionally validates the statement and reports selected output types (or the mutation category). Syntax/validation failures exit with status 1; invalid CLI arguments exit with status 2. Parsing or certifying an INSERT, UPDATE, or DELETE does not execute it.

Schemas are supplied externally as JSON:

```json
{"tables":[{"name":"flags","columns":[{"name":"id","type":"int"},{"name":"enabled","type":"bool"},{"name":"label","type":"text"}]}]}
```

Types are `int`, `text`, and `bool`. Table/column names must be nonempty and unique in their scope, and tables must have columns. Schema names are exact; ordinary unquoted SQL identifiers normalize to lowercase. [The CRUD schema](fixtures/crud/schema.json) contains `users`, `inventory`, and `flags`. All columns are required and non-null, with no default values. Consequently INSERT must supply every column, either in schema order or through a complete explicit column list.

The extended grammar accepted by `parseStatement` is:

```ebnf
statement = (select | insert | update | delete) [";"] ;
select    = SELECT [DISTINCT] ("*" | exprList) FROM identifier
            [WHERE expr] [ORDER BY orderItem {"," orderItem}]
            [LIMIT integer [OFFSET integer]] ;
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
cmpExpr   = addExpr [("=" | "<>" | "!=" | "<" | "<=" | ">" | ">=") addExpr] ;
addExpr   = mulExpr {("+" | "-") mulExpr} ;
mulExpr   = unaryExpr {("*" | "/") unaryExpr} ;
unaryExpr = {"+" | "-"} primary ;
primary   = identifier | integer | string | TRUE | FALSE | "(" expr ")" ;
```

Multiplication/division bind before addition/subtraction, then comparisons, `NOT`, `AND`, and `OR`. Unary signs bind most tightly. Binary chains associate left; comparison chains such as `a < b < c` are rejected. Integers are arbitrary-precision decimal numerals; a leading sign is a separate unary AST node. `LIMIT` and `OFFSET` take unsigned literals, and OFFSET requires LIMIT. ORDER BY accepts source expressions or one-based selected-column positions; zero and out-of-range positions are rejected by validation. With DISTINCT, non-positional sort expressions must also occur in the selected expressions (wildcard selection expands to all columns).

This is a documented SQL subset, not complete compatibility with any database dialect. Unsupported forms include joins, aliases, subqueries, aggregates, grouping, `RETURNING`, UPSERT, INSERT-SELECT, NULL/default values, parameter placeholders, DDL, and transaction commands. Exactly one statement and at most one trailing semicolon are accepted.

Keywords are case-insensitive. Unquoted identifiers use ASCII letters or `_`, followed by ASCII letters, digits, or `_`. Double-quoted identifiers preserve spelling and allow reserved words; see `Parser.crudReservedWords`. Escape quotes by doubling them: `'O''Brien'` and `"a""b"`. Empty quoted identifiers are rejected. Strings and quoted identifiers support Unicode. `--` line comments and nonnested `/* ... */` comments are accepted. Parse errors carry a zero-based character offset and one-based line/column positions.

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

-- The original API still accepts the original, strict SELECT MVP grammar.
#eval (parseQuery "SELECT id FROM users").map toSql
#eval (parseAndValidate users "SELECT id FROM users WHERE age >= 18").map
  (fun checked => checked.certificate.outputTypes)  -- Except.ok [SqlType.int]
```

| Interface | Purpose |
| --- | --- |
| `Statement`, `SelectQuery`, `InsertQuery`, `UpdateQuery`, `DeleteQuery` | Public CRUD syntax constructors. |
| `Projection`, `OrderBy`, `Assignment`, `Expr`, `BinOp`, `UnOp`, `Value` | Public syntax components. |
| `Schema`, `TableDef`, `ColumnDef`, `SqlType` | External table and column definitions. |
| `parseStatement` | `String → Except ParseError Statement`; consumes the complete input. |
| `ToSql` / `toSql` | SQL rendering with escaped identifiers/strings and explicit parentheses. |
| `certifyStatement schema statement` | `CertifiedStatement schema statement`, containing `outputTypes` and a validity proof. |
| `checkStatement schema statement` | Output types or a validation error; mutations have no selected output columns. |
| `parseAndValidateStatement schema source` | A parsed AST and its certificate packaged as `CheckedStatement schema`. |
| `Query`, `parseQuery` / `parse`, `certifyQuery`, `checkQuery`, `parseAndValidate` | The original SELECT API, retained for compatibility. |

The original source parser continues to reject the new syntax: use `parseStatement` for all CRUD extensions. Its reserved-name policy is unchanged. Low-level token APIs `Parser.parseTokens` and `Parser.parseStatementTokens` expect lexer-produced tokens with exactly one final EOF.

Static validity requires a well-formed schema, an existing table, and correctly resolved and typed expressions. Arithmetic and ordering **comparisons** require integers; equality requires equal operand types. `AND`, `OR`, `NOT`, and WHERE require booleans. ORDER BY may sort typed integer, text, or boolean expressions. INSERT checks target uniqueness/coverage and every row's arity/types, evaluating expression types in an empty column environment. UPDATE checks unique assignment targets and matching value types against the original table environment, so swaps such as `SET id = age, age = id` typecheck. UPDATE and DELETE without WHERE are valid and denote all rows.

The declarative typing and validity relations are separate from their executable checkers. Lean checks soundness and completeness proofs:

```text
inferType_iff:
  inferType columns expr = .ok type ↔ HasType columns expr type
checkQuery_iff:
  checkQuery schema query = .ok types ↔ ValidQuery schema query types
checkStatement_iff:
  checkStatement schema statement = .ok types ↔ ValidStatement schema statement types
```

Certificates bind the exact schema and AST supplied to the checker. These are static guarantees. The parser/renderer have regression and round-trip tests, not general grammar-correctness or round-trip proofs. No database is executed, and the project does not prove row-level constraints, division safety, write effects, transaction behavior, or ACID properties. For example, `1 / 0` remains well typed. SQLite compilation of the examples is additional test evidence, not a formal semantic equivalence claim.
