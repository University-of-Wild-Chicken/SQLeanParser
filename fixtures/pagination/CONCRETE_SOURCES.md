# Concrete expression LIMIT/OFFSET statements

`concrete.jsonl` contains 50 distinct complete public SELECT statements whose
pagination uses PostgreSQL `$n` parameters. SQL text is preserved from the
upstream sources. These are 42 application constants and eight compiler
regression statements; the latter are explicitly labeled `compiler-regression`.
They are separate from the generated synthetic population.

The sources are pinned:

- 20 Temporal application constants, MIT, commit
  [`b7bc978d1040afe2dcbc68ecfe8b228ae198e0b6`](https://github.com/temporalio/temporal/tree/b7bc978d1040afe2dcbc68ecfe8b228ae198e0b6/common/persistence/sql/sqlplugin/postgresql).
- 21 Cadence application constants, Apache-2.0, commit
  [`b89482543407a82529d022ef81c2280794ab0c74`](https://github.com/cadence-workflow/cadence/tree/b89482543407a82529d022ef81c2280794ab0c74/common/persistence/sql/sqlplugin/postgres).
- One River application constant, MPL-2.0, commit
  [`1354a059d7cbe5790acc7a755a2ab7ac6d2f1ed8`](https://github.com/riverqueue/river/blob/1354a059d7cbe5790acc7a755a2ab7ac6d2f1ed8/riverdriver/riverpgxv5/internal/dbsqlc/river_queue.sql.go).
- Eight sqlc compiler regression statements, MIT, commit
  [`0f1602fe1a4b780336e3e878dde720892fd8578d`](https://github.com/sqlc-dev/sqlc/tree/0f1602fe1a4b780336e3e878dde720892fd8578d/internal/endtoend/testdata).

Each JSONL record identifies the source file, original line, commit, license,
source kind, extraction method, original SQL, and SQL SHA-256.
`concrete_sources.json` pins every selected constant or complete SQL statement
span, source-file hash, and license hash. Temporal and River inputs reuse the
existing `fixtures/external_postgresql` snapshots. Only the needed Cadence and
sqlc files are copied here, with their original headers and license texts.

Go string constants are decoded without executing Go. Constant concatenation
retains the original decoded query text. sqlc regression statements are exact
source substrings, including their terminating semicolon and internal comments;
leading query-name annotations are outside those statements. No statement is
renamed, parameter-substituted, repaired, or assembled from runtime fragments.
River's schema-template comment remains in its unexpanded source constant,
as in the original external corpus; this does not claim to capture every
runtime-expanded variant.

Selection deliberately avoids dependencies on later grammar increments:
Cadence's timer pagination with a row-value comparison is excluded, as are two
Cadence replication queries that duplicate Temporal after case/whitespace
folding. Temporal DELETE statements with nested LIMIT and SELECT statements
requiring row constructors are excluded. Additional Hatchet/Coder pagination
sources found during research require functions, extended types, arrays, JSON,
locking, or modifying CTEs and are not counted here. All 50 selected statements
are unique both as exact SQL text and after conservative case/whitespace
folding. The eight sqlc statements include a compound UNION with pagination.

Reproduce the extraction and verify every source hash without network access:

```sh
python3 scripts/extract_pagination_corpus.py --check
```

With the pinned corpus dependency installed, also verify that each original
statement is one PostgreSQL SELECT with a nonliteral pagination AST node:

```sh
python3 scripts/extract_pagination_corpus.py --check --oracle
```

The optional oracle is pglast 7.21 / PostgreSQL 17.7 raw grammar. This is syntax
evidence, not database execution, catalog/type validity, result equivalence, or
proof that arbitrary pagination expressions have PostgreSQL semantics. The
source application schemas and parameter bindings are not executed by this
extractor.
