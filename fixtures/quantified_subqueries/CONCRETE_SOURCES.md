# Unchanged quantified-subquery inputs

The active population has **84 distinct whole SELECT inputs: 50 scalar and 34
row quantified comparisons**. It does not satisfy the required 50 row inputs:
**16 are still missing from the active rendering population**. There are 75
DuckDB, four Materialize, three PostgreSQL and two Calcite inputs, covering
ANY (46), SOME (13), ALL (25), and all six comparison operators. Classification
uses the left operand of the raw quantified SubLink; these inputs contain no
mixed scalar/row comparisons, and no statement counts toward both classes.

`deferred_values.jsonl` separately retains **17 additional whole row queries**
using derived VALUES bodies. These are not active rendering cases or static
certificate candidates. A bounded search of 98 files under the pinned DuckDB
`test/sql/subquery` tree plus retained PostgreSQL regression sources found no
additional non-VALUES row population large enough to close the shortage.
Deferred cases must remain unchanged. Activating all 17 after actual VALUES
query-body support would yield 101 distinct statements: 50 scalar and 51 row.
Activation requires typed parsing and rendering certificates for every whole
input, independently preregistered static metadata for any promoted certificate
candidates, and the normal native authored-case gate. Raw grammar acceptance
alone cannot activate them or close the present shortage.

`concrete_sources.json` pins complete source files, immutable commits, licenses
and notices, exact whole-input selectors, SQL hashes and comment-free token
hashes. `concrete.jsonl` and the deferred file reproduce inputs byte for byte.
SQLLogicTest statements are bounded by their query header and separate
expected-result delimiter; Quidem queries are complete terminated inputs;
PostgreSQL queries use complete statement boundaries. Expected outputs and
controls stay opaque. No SQL, source declaration or fixture data executes.
Inputs are not rewritten, extracted from plans, manufactured from expression
fragments or expanded from test loops. Case/whitespace/comment/optional-final-
semicolon variations cannot pad the population. IDs and token hashes are
unique across active and deferred records.

The original 50 selectors, identities, SQL hashes, observations and assurance
metadata remain unchanged as the first 50 selections. Their canonical hash is
`1d681dc55687e84d4a5346534ffebf35fb33122fedc91437c3c76984d6cf0a99`.
The original 47 registry objects remain unchanged as the first 47 entries;
their canonical hash is
`373a558b17f343ddc67946a8df6e444c0f66d14de5d5cbed5ef3f120fec3c30f`.

`source_contracts.json` now preregisters **80 conditional full-certificate
candidates with 93 ordered output columns**, independently of the new checker:
46 are closed and 34 use four conditional catalogs transcribed from complete
preceding DuckDB declarations in the same retained file. The declarations are
`integers(i INTEGER)` in three separate test files and
`test_data(a INTEGER, b INTEGER)` in one. These catalogs assert PostgreSQL
INTEGER meanings and an unchanged namespace; they do not assert source DDL
execution or import fixture data. All declared fields are nullable. Scalar
comparison nullability is the disjunction of left and child-column nullability;
direct row comparisons remain conservatively nullable. The nested scalar child
in the PostgreSQL scalar candidate is nullable. The 33 appended candidates
comprise 22 table-backed scalar queries and 11 closed flat-row queries.

Four active inputs remain rendering-only: a PostgreSQL nested-composite
comparison, a PostgreSQL row comparison over `tenk1` without a retained typed
catalog, and two Calcite queries without complete retained table-type catalogs,
one correlated. No catalog is invented to promote them. Successful raw parsing
or rendering does not establish native analysis, runtime success or full
PostgreSQL coverage.

Reproduce both populations with
`python3 scripts/extract_quantified_subquery_corpus.py --check`.
Add `--oracle` in the pinned pglast 7.21 environment to recheck raw syntax,
dependency observations and token identity. These checks never execute SQL.
The extractor API `reproduce(manifest, oracle=False)` returns the 84 active
records; `reproduce(manifest, oracle=False, deferred=True)` returns the 17
separate deferred records. Each output adds `query_class` and `coverage_gaps`.
The manifest records `expected_classes`, `required_classes` and
`coverage_shortfall`; none is an assertion of typed-checker success.

The implemented increment must still pass typed parsing, rendering certificates
and all 80 preregistered static candidates. Extraction makes no claim those
gates have passed, and the 16-row active coverage shortage remains open.
