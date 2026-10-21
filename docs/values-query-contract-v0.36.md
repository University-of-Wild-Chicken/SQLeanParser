# VALUES query contracts, profile v0.36

This development increment adds VALUES query bodies and PostgreSQL 16
anonymous derived sources to independent validity and identity/PostgreSQL
renderer preservation. The active contract profile is
`sqlean-basic-select-v0.36`. Full PostgreSQL contracts remain incomplete and
`0.0.1-alpha` publication remains withheld. Development pauses after this
iteration at the user's request; correlation work is not part of this increment.

`Advanced.QueryBody.values` retains rows of expressions as an actual query body.
It is distinct from INSERT VALUES and participates in complete query contexts:
local CTEs, derived sources, set operands, sorting and pagination. Rows must be
nonempty and have equal positive width. Cell expressions use the existing
scalar profile and complete child-query judgment, with visible CTE bindings
and no local row namespace.

The independent rules in
[`Values.lean`](../SQLean/SelectContract/Values.lean) type every cell before
resolving each entire column in written row order. Common-type selection uses
all rows, rather than a left-associated UNION encoding that could prematurely
resolve an initial pair of unknown NULLs. All-unknown columns resolve to TEXT.
Every cell must admit the selected implicit coercion. Exact type modifiers
survive only when all post-coercion inputs agree: an unknown NULL can remove a
bounded sibling's modifier, while a matching explicitly typed NULL retains it.

Collation merges separately for each column after coercion. Implicit conflicts
may produce indeterminate output collation; conflicting explicit identities
fail. Default labels are `column1`, `column2`, and so on. A column is nullable
if any input expression is nullable; WHERE does not refine this flag. Relation
and CTE aliases apply separately. Query-level VALUES sorting uses output names
or ordinals, and pagination retains its existing conversion and runtime bounds
obligations. Direct VALUES locking is invalid.

`Advanced.From.derivedAnonymous` retains the absence of an alias. Its output
supports unqualified lookup and star expansion without inventing a visible
relation qualifier. Duplicate unqualified labels remain ordered outputs and
become ambiguous when referenced by name. Names such as `unnamed_subquery`,
`*SELECT*` and `*VALUES*` do not become accessible aliases. The existing derived
locking guard also covers anonymous sources, including base-table children;
outer derived locking remains Unsupported. LATERAL and correlation remain
separate contract obligations.

The new cell, row and column judgments are independent of executable checker
acceptance. Parameter-translation proofs preserve their exact output metadata,
collations and lexical parameter occurrences. VALUES parameters retain row-major
written order, followed by the actual LIMIT/OFFSET spelling order. Generic
query roundtrip, translation and serialization proofs cover both constructors.
SQLite VALUES-query rendering retains an explicit Unsupported boundary.

The authored population contains fifty queries and thirteen boundary fixtures.
Original and canonical PostgreSQL checks pass 100 row captures, 100 metadata
captures, 116 exact descriptor positions and 24 separate stage controls. The
controls distinguish static failures, unsupported coverage and excluded runtime
conversion or arithmetic failures. Static validity does not establish successful
literal conversion, scalar-subquery cardinality or arbitrary runtime evaluation.
Only independently authored SQL is executed by the native harness.

The [authentic source registry](../fixtures/values_queries/CONCRETE_SOURCES.md)
contains fifty unchanged whole inputs: nine PostgreSQL and 41 DuckDB queries.
Seven are standalone VALUES queries and 43 are SELECT queries containing VALUES.
All fifty have independently preregistered complete output descriptors under
empty catalogs: 65 ordered final columns. Twelve additionally require anonymous
derived scope. Their 54 internal VALUES-body descriptors remain preregistered
but are **not separately certified** by the whole-query source gate.
The twelve anonymous-source inputs are dependency coverage within this VALUES
population, not a separate fifty-authored/fifty-source anonymous-derived factor.
That independent example target remains open.

The whole-source gate passes every original query and both identity/PostgreSQL
canonical forms: 150 exact static reports, 195 ordered output-column positions,
200 renderer reports and 100 canonical forms. Strict protocol checks retain
names, exact types, Boolean nullability, collation, status, profiles, parameter
transport and canonical stability. Missing or duplicated records and altered
source/catalog metadata fail closed. Source SQL, setup DDL, controls and expected
result blocks are never executed.

VALUES and anonymous-derived support also activate all seventeen unchanged
inputs deferred at the [v0.35 checkpoint](quantified-subquery-contract-v0.35.md).
The quantified-query population now contains 101 sources, fifty scalar and
51 row, with 97 complete certificates and 110 ordered output columns. All 101
receive checked rendering. The sixteen-row authentic-example shortage is
closed; the original seventeen-input deferred snapshot remains archived as
`deferred_values_v0.35.jsonl`.

The main build passes 503 jobs, with 37 new Lean checks. The compiled trust
audit covers 31,831 project declarations, including 18,024 theorems and 635
generated executable recursion helpers. Permitted foundational axioms remain `propext`,
`Classical.choice` and `Quot.sound`. The grammar regression passes 12,978 records:
12,975 acceptances and three pinned version-boundary rejections, with 44 protocol
checks, 125 observed outer statement families and 2,398 observed reduction
productions. These are finite test and audit counts, not a full PostgreSQL
mechanical-closure result.

The original application corpus remains at 257 typed-parser acceptances and
nineteen rejections among 276 records. Its
[audit checkpoint](corpus/values-queries-v0.36/README.md) binds the unchanged
source inputs to CLI SHA256
`001e8511ccc5351ca8716131352ca9d4474e39eaa1679eeda88302ed17250dbc`.
All 56 local integration gates pass. The initial matrix passed 55 gates; its
stale anonymous-source parse-error expectation was repaired and that gate was
rerun successfully. A clean export passes 1,385 Python tests and 89 offline
fixture/provenance checks. The Python run also caught a second normative-import
allowlist requiring the reviewed Values module; the complete suite passes after
that repair. CI enforces these regression surfaces. General grouping/aggregate
ownership, windows, DISTINCT ON,
correlation, LATERAL, remaining mutation/DDL/utility contracts and full-grammar
source-example obligations continue to block the alpha release.

```sh
lake build --wfail
lake exe sqlean_tests
lake exe sqlean_scope_tests
python3 scripts/generate_values_query_examples.py --check
python3 scripts/extract_values_query_corpus.py --check
python3 scripts/check_values_sources_cli.py
python3 scripts/check_values_queries_cli.py --local-bin /path/to/postgresql-16/bin
python3 scripts/extract_quantified_subquery_corpus.py --check
python3 scripts/check_quantified_subqueries_cli.py --local-bin /path/to/postgresql-16/bin --source-registry
python3 scripts/check_lean_trust.py --evidence-json .lake/trust-audit-v36.json
```
