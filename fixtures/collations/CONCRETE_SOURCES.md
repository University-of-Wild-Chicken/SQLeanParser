# Unchanged COLLATE sources and written declaration context

This fixed population contains 50 complete PostgreSQL engine-regression
queries with 67 explicit `COLLATE` clauses and 26 distinct written collation
names. Thirty-seven queries come from `collate.icu.utf8.sql`, ten from
`collate.linux.utf8.sql`, and three from `collate.sql`. The statements are
distinct exactly and under the repository's case/whitespace comparison;
none repeats an earlier factor's concrete query.

All three complete source files are reused from the retained PostgreSQL
snapshot at
[`f0595c3d839debdb140903621c1b44a4f4d86256`](https://github.com/postgres/postgres/tree/f0595c3d839debdb140903621c1b44a4f4d86256).
The existing PostgreSQL license copy is retained unchanged.
`concrete_sources.json` records the source and license hashes, whole-statement
selectors, original SQL hashes, line numbers, and links. Every emitted `sql`
equals `raw_sql`; there are no transformations or inferred parameter bindings.
These are engine tests, not application traffic.

Thirty-four queries have no relation or parameter dependency; sixteen refer
to source-declared tables. This source-free observation does not establish
that a query is catalog-free: named collations are catalog objects even in
a literal-only expression. Eligibility is preregistered separately from the
source extractor and requires the independent collation environment and
validity rules.

`declaration_contexts.json` preserves 28 complete preceding declarations:
14 `CREATE COLLATION`, eight `CREATE TABLE`, three `CREATE SCHEMA`, and three
`SET search_path` statements. It also retains the three original file
preambles, including encoding, provider, operating-system, and psql skip
controls. Each query links to the preceding written declarations in its
source file. One retained table declaration follows exactly
`\d collate_test_like`; the finite context selector preserves that psql
prefix separately and selects the unchanged complete `CREATE TABLE` body.
The prefix is neither run nor treated as SQL.

Declaration observations preserve only written options, names, array bounds,
column `NOT NULL` constraints, and explicit field collations. An omitted
provider, determinism option, or column collation remains omitted. The
observer does not simulate execution, DROP/ALTER effects, effective search
paths, catalog lookup, or successful object creation. The records are source
context, not a snapshot of an installed catalog.

Dependencies without a preceding retained `CREATE COLLATION` are marked
`unresolved-catalog-reference`. This includes bootstrap names such as `C`
and `POSIX`, imported ICU names, and libc locale names. The source evidence
does not assign their OIDs, providers, determinism, encodings, or installed
locale availability. Even two names with equivalent behavior must not be
collapsed into one catalog identity. Execution or a full static contract
needs a separately declared environment that supplies those facts.

`source_contracts.json` lists all 50 original IDs in order. Eighteen are
preregistered as checker-eligible under explicit caller-asserted catalogs:
nine literal-only statements and nine referring to source-declared tables.
Their 28 ordered output positions are twelve BOOL, five INT32, nine TEXT,
and two TEXT arrays. Labels, duplicate labels, nullable flags, and output
collation identities are fixed before checker execution. Thirty-two entries
are `deferred`, with `eligibility: catalog_prerequisite`, their exact unresolved
names, and no catalog or output schema. This records missing source evidence;
it is not an Unsupported result from the checker.

The three `source_*` catalog files are conditional assertions, not observations
of a running database. Their provenance is in `source_snapshot_provenance.json`.
The ICU snapshot includes nine source-defined collations and five source-defined
tables; the portable snapshot includes the actual C-collated table declaration;
the built-in snapshot contains no tables. Each custom identity is a distinct
symbol tied to its complete source `CREATE COLLATION`, never an invented OID.
The assumptions include successful declarations, provider/locale availability,
the recorded source schema/search path without shadowing, and a UTF8 connection.
No assertion is made that these conditions hold on the CI machine.

The conversion retains explicit determinism. Where it is omitted, the
caller-asserted snapshot uses PostgreSQL 16's documented default of true;
ICU declarations use the encoding-independent identity described by the
pinned `DefineCollation` implementation. These facts are separate from the
written-option observations. The exact PostgreSQL source files
`collationcmds.c` and `pg_collation.dat` are retained and hashed with the same
license and commit. [CREATE COLLATION documentation](https://www.postgresql.org/docs/16/sql-createcollation.html)
and the [pinned implementation](https://github.com/postgres/postgres/blob/f0595c3d839debdb140903621c1b44a4f4d86256/src/backend/commands/collationcmds.c)
describe those declaration rules.

Table column types, nullability, and explicit collation sidecars are converted
from their retained DDL. Omitted text/text-array field collations assert the
database-default identity; integer fields have no collation. Predicate
equality does not invent nonnullable output metadata. The ICU tables whose
fields refer to unresolved imported locales remain deferred even when their
query predicate explicitly selects C.

A separate `source_observed_contracts.json` preregisters those remaining
32 queries under `source_observed_catalog.json`. It does not alter the
declaration-only baseline. The added context combines ten actually observed
collation objects from a disposable PostgreSQL 16.15 UTF8 database with
conditional source-defined collation/table declarations. Its 43 ordered
outputs are thirty BOOL, six INT32, and seven TEXT positions. Together the
two registries cover all 50 original IDs and 71 output positions, under
their stated environments.

The observed database initially supplied eight imported names. Independently
authored setup created the two missing libc names after `localedef` generated
private locale data under `/tmp`; global locales were not changed. The
retained `provenance/fixture-catalog-observation.json` records the exact
catalog/version queries, actual OIDs, namespace, provider, determinism,
encoding, locale strings, versions, setup commands, binary hashes, and locale
input/output hashes. `source_observed_provenance.json` maps every imported
symbolic identity to its distinct observed catalog row. `ucs_basic`, `C`,
`POSIX`, `unicode`, and `und-x-icu` remain distinct objects even where locale
behavior overlaps.

This is evidence for a declared test context, not for the original source
deployment. The source tables and custom ICU declarations are still caller
assertions; no downloaded query or setup was executed. Offline CI validates
the retained snapshot, exact registry, and declaration conversions without
requiring these locales to be installed. Optional local observation
instructions are in [provenance/REPRODUCE.md](provenance/REPRODUCE.md).

The syntax observer verifies each raw-parser `CollateClause` against the
exact UTF-8 byte position and written identifier components. Quoting and
case are retained separately from decoded names. It also records all
relation occurrences and rejects the unselected nested-query, function,
parameter, aggregation, set-operation, and window prerequisites. The fixed
population includes scalar literals, array constructors, column references,
comparisons, sorting, and concatenation. All selected collation names are
one component; qualified collation names and explicit COLLATE in recursive
queries are coverage gaps of this authentic population. Authored fixtures
can exercise those forms separately.

No downloaded SQL, declaration, source program, psql command, or condition is
executed. Upstream expected values are not used as native database oracles.
Native observations use separately authored fixtures and explicitly
constructed catalogs. The corpus makes no guarantee that locale-dependent
setup succeeds on the machine running CI.

```sh
python3 scripts/extract_collation_corpus.py --check
python3 -m unittest discover -s scripts -p 'test_collation_extraction.py'
python3 -m unittest discover -s scripts -p 'test_collation_source_contracts.py'
```

The optional `--oracle` recomputes query and declaration observations using
pinned pglast 7.21. Its PostgreSQL 17 raw parser provides syntax observations,
not the PostgreSQL 16 catalog/type specification. The separate PostgreSQL 16
grammar replay includes these 50 inputs. Offline reproduction requires only
the retained source files, standard-library readers, selectors, and hashes.
