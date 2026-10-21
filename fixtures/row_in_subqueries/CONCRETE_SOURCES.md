# Unchanged row-valued IN-subquery sources

This closed population contains **50 distinct complete positive typed-parser and
checked-renderer inputs** from six pinned projects: Hatchet 10, PostgreSQL 7,
DuckDB 1, Materialize 5, SQLite 25 and Calcite 2. SQL bytes are retained unchanged;
all 50 have distinct comment-free token sequences. They exercise row-valued IN
and NOT IN, two- and three-column comparisons, ordering, casts, joins, repeated
input columns, CTE inputs, set operations and NULLs.

`concrete_sources.json` pins every upstream repository, full commit, source file
hash, license/notice hash, exact input selector, SQL hash, token hash and syntax
observation. Complete source files and licenses are retained in `sources/` and
`licenses/`. `concrete.jsonl` is reproduced from those pinned inputs. The original
source SQL, declarations, fixture data, expected results, Tcl commands and test
runner directives are **never executed**.

The fifty inputs passed 100 identity/PostgreSQL rendering checks using the frozen
v0.33 CLI with SHA-256
`2c00c6692f3acf23d027849b18d8efc3036f033339e5a87dfd6e165a7d60824a`.
This observation establishes parser and checked-rendering coverage; it does not
establish database analysis, catalog completeness or execution equivalence.

## Complete input boundaries

Selectors retain whole semicolon-terminated SQL statements, complete generated
Go constants, SQLLogicTest query inputs, complete Quidem SELECT inputs and literal
positive SQLite Tcl SQL arguments. The whole-Tcl-argument reader admits the
source's complete SELECT even when it omits a terminating semicolon. It does not
append one, evaluate Tcl, substitute variables, combine statements, or manufacture
a SELECT from an expression fragment. It rejects argument assembly and Tcl
backslash-newline substitution. Quidem inputs remain complete terminated SELECTs
when an upstream result table is omitted. Expected outputs stay opaque.

The existing 64-candidate discovery inventory supplied 37 renderer successes.
Fifteen additional complete SQLite arguments were found in the retained pinned
`rowvalue3.test` and `rowvalue9.test` files; this closure selects all fifteen and
35 of the original successes. Two original aggregate-dependent PostgreSQL cases
were omitted. Repeated source queries differing only in comments, whitespace or
case do not contribute additional inputs. Unsupported examples are not counted
as passing rendering coverage.

## Preregistered conditional static subset

`source_contracts.json` fixes **12 candidate full certificates and 20 ordered
output columns**, before replay with the v0.34 checker. It is a plain list of
`id`, `catalogFile` and exact `output_columns` entries. Output names, types,
nullability and collations were specified from the unchanged SELECTs, written
field declarations and the v0.34 rules, independently of checker success.
Boolean row-IN outputs are conservatively nullable. The DuckDB projection is
literal `1` and therefore remains nonnullable INTEGER despite its row-IN filter.
The source alias `"Correlated Field"` is preserved; its selected query has no
outer reference and the alias itself does not establish correlation.

Two candidates are closed queries. Ten use five conditional catalogs, backed by
six complete declarations retained in the same source files:

- PostgreSQL `subselect_tbl`: INTEGER, INTEGER and unqualified FLOAT (DOUBLE
  PRECISION), with nullable fields.
- PostgreSQL temporary `outer_7597` and `inner_7597`: INTEGER and BIGINT fields.
- PostgreSQL `collate_test10`: INTEGER plus TEXT fields with distinct C and POSIX
  collation identities.
- Materialize's Cockroach test `t`: three nullable INTEGER fields.
- Materialize's Cockroach test `abc`: INTEGER primary key and two nullable INTEGER
  fields.

Catalog JSON transcribes those fields and explicit collation sidecars. The
conditional claim assumes successful declarations and matching, unshadowed
PostgreSQL type/name lookup. It imports neither source data nor native execution
observations. The manifest binds each candidate to its exact declaration and
column-name inventory; lexical dependency observations must show no correlation,
uncertain scope, unresolved names or parameters for this subset.

The other **38 records retain rendering-only assurance**. Their conservative
correlation and unresolved/uncertain-name observations remain visible in each
record. Missing application catalogs, set-returning functions, aggregates,
SQLite-specific fields and legacy query features are not promoted to static
certificates. A lexical screen with unknown fields does not certify uncorrelated
scope. All static eligibility is fixed by the explicit registry, never selected
by accepting whichever queries happen to pass a later checker replay.

## Reproduction

```sh
python3 scripts/extract_row_in_subquery_corpus.py --check
python3 -m unittest discover -s scripts -p 'test_row_in_subquery_extraction.py'
# Optional pinned pglast 7.21 syntax/token observations, with no SQL execution:
/path/to/pglast-7.21/python scripts/extract_row_in_subquery_corpus.py --check --oracle
```

Offline checks bind the closed manifest, preregistered registry, source/license
bytes, exact input boundaries and written declarations. Tests reject altered
source identities, invented metadata, expanded eligibility, input fragments,
statement assembly and byte-changing substitutions. The optional oracle checks
row-IN arities, syntax dependencies and globally distinct token identities.
