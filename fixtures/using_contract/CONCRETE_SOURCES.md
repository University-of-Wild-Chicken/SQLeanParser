# USING join source corpus

`concrete.jsonl` contains 50 distinct, unchanged, whole SELECT statements:
16 PostgreSQL engine regressions, 3 sqlc compiler regressions, and 31 SQLite
engine regressions. They contain 23 INNER, 24 LEFT, 6 RIGHT, and 16 FULL join
nodes with USING conditions. Some statements contain several joins or mix
USING with NATURAL or ON conditions.

Every selected FROM expression is a tree of named relations, optional table
aliases, and joins. The selections have no derived-table, table-function,
subquery, aggregate, or CTE dependency. Explicit USING column lists retain
their original order, including multi-column and nested joins. Whether a
named relation resolves to a table, view, or foreign table requires its real
catalog.

Pinned sources and licenses:

- [PostgreSQL REL_16_STABLE](https://github.com/postgres/postgres/tree/f0595c3d839debdb140903621c1b44a4f4d86256):
  commit `f0595c3d839debdb140903621c1b44a4f4d86256`, PostgreSQL License.
- [sqlc](https://github.com/sqlc-dev/sqlc/tree/0f1602fe1a4b780336e3e878dde720892fd8578d):
  commit `0f1602fe1a4b780336e3e878dde720892fd8578d`, MIT.
- [SQLite](https://github.com/sqlite/sqlite/tree/5484850c7a2cd90f2a06b8d4f3453b259aefc1e1):
  commit `5484850c7a2cd90f2a06b8d4f3453b259aefc1e1`, public domain for its
  test files, as stated in the pinned
  [LICENSE.md](../factor_sources/licenses/sqlite-LICENSE.md).

`concrete_sources.json` pins 10 source files and all license files by SHA-256.
Existing source snapshots are reused. SQLite files are shared with the NATURAL
corpus under `fixtures/factor_sources/sources/sqlite`. Its upstream generated
`joinB.test` and `joinC.test` matrices are not part of these selections.

SQLite SQL is extracted from literal `execsql`, `catchsql`, `do_execsql_test`,
or `do_catchsql_test` blocks. The manifest records the command line, complete
balanced SQL argument, and one complete semicolon-terminated statement within
it, using character offsets in the UTF-8-decoded file. Blocks requiring Tcl
backslash-newline substitution are rejected. No Tcl is evaluated, and no SQL
is rewritten. Loop variables in test names are recorded as source text;
they never generate additional queries or change the selected SQL.

Each record retains the original SQL, source line/link, source kind,
parameter slots, and recursively ordered join tree. SQLite records also
declare `source_dialect: "sqlite"` and identify the original Tcl command.
Error-capturing commands remain labeled; successful analysis or execution
is not assumed. Conservative normalized duplicates cannot increase the count.

These sources receive syntax and checked-rendering checks only. **They are
never executed** by corpus verification. Catalogs and parameter types are
not invented. Parsing SQLite-origin text as PostgreSQL and checking its
rendering does not establish equivalent catalog resolution, column merging,
result types, or execution behavior across engines.

Reproduce from local pinned inputs:

```sh
python3 scripts/extract_factor_corpus.py --factor using_contract --check
python3 -m unittest discover -s scripts -p test_factor_extraction.py
python3 -m unittest discover -s scripts -p test_tcl_sql_extraction.py
```

Optional `--oracle` requires `pglast==7.21` and rechecks one whole SELECT,
parameter slots, dependency observations, USING column order, and the exact
join tree. Its raw parser uses PostgreSQL 17.7. The independent PostgreSQL 16
grammar replay also checks all 50 statements. Neither oracle executes SQL.
