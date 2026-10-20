# NATURAL join source corpus

`concrete.jsonl` contains 50 distinct, unchanged, whole SELECT statements:
6 PostgreSQL engine regressions and 44 SQLite engine regressions. They contain
30 INNER, 19 LEFT, 9 RIGHT, and 14 FULL join nodes with NATURAL conditions.
Some statements contain several joins or mix NATURAL with USING or ON.

Every selected FROM expression is a tree of named relations, optional table
aliases, and joins. There are no derived-table, table-function, subquery,
aggregate, or CTE dependencies. The source metadata retains NATURAL as an
explicit condition and preserves left/right nesting. Actual shared column
names, their order, merged output types, and nullability depend on a catalog;
the concrete source corpus does not invent one.

Pinned sources and licenses:

- [PostgreSQL REL_16_STABLE](https://github.com/postgres/postgres/tree/f0595c3d839debdb140903621c1b44a4f4d86256):
  commit `f0595c3d839debdb140903621c1b44a4f4d86256`, PostgreSQL License.
- [SQLite](https://github.com/sqlite/sqlite/tree/5484850c7a2cd90f2a06b8d4f3453b259aefc1e1):
  commit `5484850c7a2cd90f2a06b8d4f3453b259aefc1e1`, public domain for its
  test files, as stated in the pinned
  [LICENSE.md](../factor_sources/licenses/sqlite-LICENSE.md).

`concrete_sources.json` pins 10 source files and both license files by SHA-256.
Existing source snapshots are reused. SQLite files are shared with the USING
corpus under `fixtures/factor_sources/sources/sqlite`. The selections exclude
its upstream generated `joinB.test` and `joinC.test` matrices; no renamed or
synthetically varied queries were created to reach 50.

Each SQLite selection pins an explicit Tcl SQL command, its complete balanced
literal SQL argument, and one complete semicolon-terminated statement within
that argument. Offsets refer to characters in the UTF-8-decoded source.
Backslash-newline substitution is rejected. The extractor recognizes this
finite source format; it does not interpret Tcl or evaluate loop variables.
Every record keeps the original SQL bytes after UTF-8 decoding, source
line/link, source kind, and ordered join tree. SQLite records explicitly name
their source dialect and preserve the original SQL test command, including
error-capturing commands.

These sources receive syntax and checked-rendering checks only. **They are
never executed** by corpus verification. Application catalogs and parameter
types are not invented. PostgreSQL parsing/rendering acceptance of
SQLite-origin SQL establishes neither successful catalog-dependent analysis
nor equivalent NATURAL join behavior across engines.

Reproduce from local pinned inputs:

```sh
python3 scripts/extract_factor_corpus.py --factor natural_contract --check
python3 -m unittest discover -s scripts -p test_factor_extraction.py
python3 -m unittest discover -s scripts -p test_tcl_sql_extraction.py
```

Optional `--oracle` requires `pglast==7.21` and rechecks one whole SELECT,
parameter slots, dependency observations, and the exact join tree. Its raw
parser uses PostgreSQL 17.7. The separate PostgreSQL 16 grammar replay also
checks all 50 statements. Neither oracle executes SQL.
