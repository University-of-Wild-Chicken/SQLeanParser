# Whole unchanged VALUES query sources

This finite population contains **50 distinct complete query inputs**: nine
PostgreSQL and 41 DuckDB statements. Seven have a top-level VALUES query body
(including one with a local WITH clause); 43 are SELECT queries containing
VALUES. INSERT VALUES, DML CTEs, extracted expression fragments, view bodies,
expected-result text and generated loop expansions do not count.

`concrete_sources.json` pins immutable full commits, complete upstream source
files, licenses, exact whole-input selectors, SQL hashes and normalized token
hashes. `concrete.jsonl` reproduces the 50 input strings without modification.
SQLLogicTest `query` inputs have a separate expected-result delimiter. Four
standalone VALUES queries are genuine complete `statement ok` inputs from the
DuckDB decimal warning regression file; they are not INSERT statements.
Setup, warning controls, errors and expected results remain opaque and never
execute. The finite reader rejects unknown directives and malformed boundaries.
PostgreSQL inputs use complete semicolon-terminated statement boundaries.

All **50 queries / 65 ordered output columns** were preregistered in
`source_contracts.json`, independently of a SQLean VALUES checker. There are no
catalog files or fabricated tables. Inputs use closed expressions and derived
VALUES, with two simple local nonrecursive CTE cases. They contain no aggregate
or function calls, GROUP BY, DISTINCT ON, windows, LATERAL, correlation, external
tables or DML. The certified static surface includes existing scalar subqueries,
scalar/flat-row quantified comparisons, arithmetic and array set operations.
Each selection also records `values_body_columns`: fixed metadata for every
VALUES body, in raw-query preorder, with default `column1`, `column2`, ... names.
This exposes inner-column type, modifier, nullability and collation expectations
even when the final result is just a comparison boolean.

**Twelve inputs additionally require PostgreSQL 16 anonymous derived-table
syntax and scope.** Eleven are unchanged row comparisons whose child contains
`FROM (VALUES ...)` without an alias; the twelfth is the complete input
`SELECT * FROM (VALUES (42, 43))`. This is an independent implementation
requirement alongside VALUES bodies: the pre-v0.36 typed parser required a
derived-table alias. No visible qualifier may be invented to make these inputs
pass. Unqualified columns and star expansion must work with the anonymous
relation's actual visibility rules. The manifest records this requirement and
its 12-case count; it does not assert 50 independent anonymous-derived cases or
claim complete anonymous-derived coverage beyond the registered surface.

The fixed metadata uses PostgreSQL 16 semantics, not DuckDB result tables:

- A column resolves its common type across all rows simultaneously. All-unknown
  inputs resolve to text. Each expression must then support the selected implicit
  coercion. This must not be replaced by a left-associated UNION tree that
  prematurely resolves an initial pair of NULLs.
- Type modifiers are compared **after coercion**. They survive only when every
  coerced expression has the same resulting type and modifier. The four genuine
  decimal sources expect, respectively, `numeric`, `numeric(38,24)`, `numeric`,
  and `numeric`. An untyped NULL or an unmodified numeric NULL drops the sibling's
  modifier; a matching explicitly typed NULL retains it; unequal modifiers drop.
- Collation is resolved per column. Implicit conflicts can remain indeterminate;
  explicit conflicts still fail. The selected PostgreSQL collation case fixes
  its first text column to default collation and its second to C.
- Nullable flags follow the conservative contract, not execution of test
  data: a VALUES column is nullable if any source expression is nullable. Scalar
  subqueries are nullable. WHERE filters do not refine this flag. Existing flat
  row comparisons remain conservatively nullable.

The primary PostgreSQL implementation is retained under `primary_sources/`,
hashed and tied to the same immutable PostgreSQL revision and license:

- [`transformValuesClause`, analyze.c](https://github.com/postgres/postgres/blob/f0595c3d839debdb140903621c1b44a4f4d86256/src/backend/parser/analyze.c#L1474)
  transforms all row expressions, checks equal widths, chooses column types,
  coerces inputs, and then chooses typmods and collations (lines 1593–1604).
- [`select_common_typmod`, parse_coerce.c](https://github.com/postgres/postgres/blob/f0595c3d839debdb140903621c1b44a4f4d86256/src/backend/parser/parse_coerce.c#L1643)
  requires matching resulting types and modifiers. The same file's
  `select_common_type` defines the complete-input type-selection algorithm.
- [`addRangeTableEntryForValues`, parse_relation.c](https://github.com/postgres/postgres/blob/f0595c3d839debdb140903621c1b44a4f4d86256/src/backend/parser/parse_relation.c#L2137)
  supplies default column names. Outer projection or relation/CTE aliases are
  applied separately in the final preregistered descriptors.

Run `python3 scripts/extract_values_query_corpus.py --check` for offline
reproduction. Add `--oracle` in the pinned pglast 7.21 environment to replay raw
syntax, VALUES-body shape observations and token identity. The optional raw
parser is not a PostgreSQL 16 semantic analyzer; neither this oracle nor the
extractor executes SQL. Eleven extraction tests cover source/metadata mutations,
whole-input boundaries, opaque results, DML/multiple-input rejection, modifier
expectations, explicit anonymous-derived requirements and fail-closed
optional-oracle mismatches.

The manifest's lexical relation/CTE inventory is a conservative screen, not a
general correlation proof. The two selected local CTE contexts are reviewed and
preregistered explicitly. Output descriptors are fixed before checker replay;
passing or failing the new checker cannot rewrite them.

The v0.36 whole-source gate passes all 50 original queries and their identity
and PostgreSQL canonical forms under empty catalogs: 150 exact static reports,
195 ordered output-column positions, 200 renderer reports and 100 canonical
forms. These checks cover complete query outputs. The 54 internal VALUES-body
descriptors remain preregistered and are **not separately certified** by this
gate. No source SQL or DDL is executed.

The separate authored native gate passes fifty VALUES fixtures and thirteen
boundary fixtures, with 100 row captures, 100 metadata captures, 116 exact
descriptor positions and 24 stage controls. The quantified-subquery population
now activates all seventeen retained VALUES-dependent inputs unchanged: 101
active queries, fifty scalar and 51 row, with 97 complete certificates and 110
ordered output columns. Its original v0.35 deferred snapshot remains archived.

The final integration matrix, clean Python export and upstream CI are still
pending. These finite gates do not establish full PostgreSQL coverage or
permission to publish the held alpha release.
