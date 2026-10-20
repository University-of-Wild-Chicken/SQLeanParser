# Unchanged SUBSTRING source statements

The fixed population contains 50 distinct complete source-free SELECTs: 27
PostgreSQL regressions, 11 CockroachDB regressions, and 12 Materialize
regressions. No SQL is rewritten, renamed, generated, or executed. Upstream
expected-result sections remain opaque; they are not PostgreSQL runtime oracles.

The 27 PostgreSQL queries reuse the pinned
[`strings.sql`](https://github.com/postgres/postgres/blob/f0595c3d839debdb140903621c1b44a4f4d86256/src/test/regress/sql/strings.sql)
and
[`regex.sql`](https://github.com/postgres/postgres/blob/f0595c3d839debdb140903621c1b44a4f4d86256/src/test/regress/sql/regex.sql)
snapshots under the existing PostgreSQL license. Three explicitly marked
runtime-error SUBSTRING examples in `strings.sql` are excluded. BIT, VARBIT,
CITEXT, Unicode-prefixed literals, and table-dependent queries are outside this
closed population.

The 11 CockroachDB statements come from
[`builtin_function`](https://github.com/cockroachdb/cockroach/blob/5b78463ed2e7106a8477b63fa837564ad02bb510/pkg/sql/logictest/testdata/logic_test/builtin_function)
at the `v22.1.0` pin. Its original
[license notice](../factor_sources/licenses/cockroach-v22.1-LICENSE),
[BSL parameters](../factor_sources/licenses/cockroach-v22.1-BSL.txt), and
[Apache license](../factor_sources/licenses/cockroach-v22.1-APACHE.txt) are retained.
The BSL specifies a change date of April 1, 2025 and a change license of
Apache-2.0. Its selected statements include the authentic reversed
`FOR … FROM` spelling. CockroachDB-specific binary literal syntax and error
records are not selected.

The 12 Materialize statements come from
[`string.slt`](https://github.com/MaterializeInc/materialize/blob/726570dba1d2e4d839c707a84a986fb3b3acc5c3/test/sqllogictest/string.slt).
This snapshot remains source-available under its retained
[Business Source License 1.1](../factor_sources/licenses/materialize-20261020-LICENSE),
which permits copying, redistribution, and nonproduction use. Its stated change
date is October 20, 2030, with Apache-2.0 as the change license. These source
excerpts keep their upstream licensing and attribution; the project's license
does not replace those terms.

The syntax inventory is exact: 14 `FROM … FOR`, 13 `FROM` only, 12
`SIMILAR … ESCAPE`, three `FOR` only, one `FOR … FROM`, and seven ordinary
comma calls. The FROM forms include numeric positions and POSIX patterns; the
FROM/FOR forms include the older SQL regular-expression spelling. Six first
arguments explicitly cast to BYTEA. Five projections wrap the call in `IS NULL`
and two compare it with a string literal. All other projections are direct calls.

The separate finite Cockroach-style SQLLogicTest reader recognizes the prefix
through each selected complete query block. Before that block it accepts only
comments, blank lines, optional initial `mode cockroach`, statement records,
query-error records, and the finite query-header variants needed by these
snapshots. It skips unselected results as opaque text and rejects unknown
directives before a selection. It does not interpret later records, execute
control flow, substitute variables, or reuse expected values. Every selected
header is exactly `query T`; byte-exact source boundaries and hashes are checked.
The original stricter reader used by other factors is unchanged.

The observer requires one source-free projection with one SUBSTRING call and
literal/NULL arguments, optional direct BYTEA casts, or the two declared wrapper
forms. Raw-parser locations are decoded as UTF-8 byte offsets before the source
keyword order is inspected. The metadata retains PostgreSQL's inserted start
position and integer cast for FOR-only syntax. The `arguments` list uses
PostgreSQL's normalized function argument order; the separate `form` retains
the source distinction between FROM/FOR and FOR/FROM. Literal forms and written
casts are recorded without evaluating patterns, choosing overloads, or borrowing
a catalog.

The fixed empty catalog and parameter environments allow all 50 queries to
receive independent full static certificates, with expected output metadata
registered separately in Lean tests. Identity/PostgreSQL rendering checks exact
AST round trips. Source SQL is never sent to a database. Separate authored
`synthetic.json` examples supply finite native PostgreSQL observations.

```sh
python3 scripts/extract_factor_corpus.py --factor substring --check
python3 -m unittest discover -s scripts -p 'test_substring_extraction.py'
```

The optional `--oracle` check reproduces raw syntax observations using pinned
pglast 7.21 (PostgreSQL 17.7). The project's independent broad grammar replay
uses its pinned PostgreSQL 16 grammar. Neither parser check establishes runtime
conversion or regular-expression validity.
