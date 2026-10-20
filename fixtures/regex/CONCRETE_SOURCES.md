# Regular-expression operator source corpus

`concrete.jsonl` contains 50 distinct, unchanged, whole SELECT statements
from five PostgreSQL regression files. None occurs in the existing
`fixtures/statement_families/concrete.jsonl` population. These are engine
regressions, not application queries or captured production traffic.

Each statement contains one regular-expression operator: 42 `~`, six `~*`,
one `!~`, and one `!~*`. Twenty-seven statements are literal-expression tests
from `regex.sql`; 18 exercise text columns in the `pg_trgm` regression;
three query NAME columns; one contains a derived-table join and CASE
expression; and one uses a regex condition inside aggregate `FILTER`.
The negated case-insensitive example is the complete original multi-join
query, rather than an invented spelling variant of a simpler statement.

The literal patterns include anchors, repetition, captures, backreferences,
lookahead, and lookbehind. This is observed source syntax, not a proof that
every runtime pattern is valid or that matching is efficient. The selected
literal statements precede the regression's explicit error-condition
section. LTREE overloads of `~`, unary bitwise complement, custom operator
spellings, and schema-qualified operators were not selected.

The source is pinned to
[PostgreSQL REL_16_STABLE](https://github.com/postgres/postgres/tree/f0595c3d839debdb140903621c1b44a4f4d86256),
commit `f0595c3d839debdb140903621c1b44a4f4d86256`, under the PostgreSQL
License. `concrete_sources.json` pins all five source files and the license
input by SHA-256. Each selection is one complete original statement with
exact source bytes, source line and link, and unchanged string escapes.
The statements are parameter-free; dollar signs inside regex literals do
not become parameter bindings.

Metadata records operator spelling and the raw-parser node form on each
side. It does not infer the types of NAME or other column references,
assign function signatures, select an operator overload, or attach runtime
results. The finite screen excludes explicit array types, constructors and
access, rows, array/quantified subqueries, and other extended operators.
Existing joins, CASE, casts, and aggregation remain where present.

Discovery probes temporarily substituted an existing operator to identify
unrelated parser dependencies. Those probes are not corpus inputs or
coverage evidence. No committed query is rewritten, renamed, or shortened.
Exact and case/whitespace duplicates cannot increase the population.

All 50 concrete queries receive syntax and checked-rendering checks only.
They are never executed. PostgreSQL expected-output files are not imported
as native expectations. Application validity, catalog typing, collation
behavior, regex validity, and successful execution are not established by
this source screen or the raw parser. Separate authored fixtures provide
catalogs and finite native observations for the independent contracts.

Reproduce from local pinned inputs:

```sh
python3 scripts/extract_factor_corpus.py --factor regex --check
python3 -m unittest discover -s scripts -p test_pattern_extraction.py
```

Optional `--oracle` requires `pglast==7.21` and verifies one whole SELECT,
parameter slots, exact operator observations, and the stated syntax
exclusions. Its raw parser uses PostgreSQL 17.7. The separate PostgreSQL 16
grammar replay checks all 50 originals. Neither oracle executes SQL.
