# Recursive SELECT CTE validity, profile v0.31

`sqlean-basic-select-v0.31` extends the independent SELECT contract to a bounded
recursive CTE fragment. It composes with the existing SELECT, set-operation,
join, ordinary CTE, derived-source, scalar and parameter contracts. The broader
typed parser and complete pinned PostgreSQL grammar interface keep their
existing assurance levels. Full PostgreSQL contracts still gate `0.0.1-alpha`.

## Independent rules

`RecursiveCTEsValid` distinguishes an actually recursive definition from an
ordinary definition in a `WITH RECURSIVE` list. A keyword alone does not change
ordinary set-operation unknown resolution. Definitions must already be in
dependency order; forward and mutual dependencies return Unsupported rather
than resolving against an inherited CTE or physical-table homonym.

`RecursiveCTEValid` requires a root `UNION` or `UNION ALL`, a self-reference-free
anchor, and exactly one permitted recursive reference. The reference analysis
respects local shadowing, qualified table identities, nested ordinary CTEs and
derived queries. Unused inner definitions still count as syntactic references.
The recursive reference cannot occur on a nullable outer-join side, beneath
`INTERSECT ALL`, or on a prohibited `EXCEPT` side. Expression subqueries retain
their separate typed-contract boundary.

The anchor receives a complete query derivation. Its exact output, after
positional aliases, establishes the recursive binding with conservative nullable
flags. The step receives a set-operand derivation in that extended environment.
Independent common-type rules merge the original pending anchor inputs and the
step inputs. The complete merged scalar types, including modifiers, must equal
the anchor's complete scalar types. This is not a requirement that the two raw
arms have identical types: an unmodified anchor can accept a modified step when
the common result has the anchor's type.

Actual recursion finalizes an unknown anchor result before exposing it to the
step. Consequently, an untyped NULL anchor becomes TEXT and cannot later become
INTEGER because of the recursive arm. An ordinary definition without a
self-reference retains the existing contextual UNION rules.

Root sorting, pagination and locking on a recursive definition are excluded
by the recursive rule; supported clauses inside a parenthesized operand remain
local to that operand. Outer SELECT sorting and pagination work normally.
All exposed recursive columns have `nullable = true`, a conservative bound
independent of whether the selected finite data actually contains NULL.
An outer expression such as `n IS NULL` can still have a nonnullable result.

## Collation boundary

Exact scalar type and modifier agreement does not establish recursive collation
agreement. In PostgreSQL, NAME-derived text can carry a different collation
from an ordinary TEXT literal even when both arms have the same TEXT type.

This increment admits noncollatable outputs and a structurally proved
uniform-default fragment. That fragment checks every defining expression and
referenced namespace. It excludes NAME casts, NAME-bearing parameter types,
NAME-returning session functions, and unresolved collatable external catalog or
inherited CTE columns. Nested arrays and casts cannot hide those dependencies.
The rule is intentionally sufficient: some PostgreSQL-valid statements remain
Unsupported.

Full expression-level collation provenance, explicit `COLLATE`, catalog
collation metadata and mixed-collation propagation are the named follow-up.
They are not inferred from the existing scalar type field. Forward dependency
ordering, SEARCH/CYCLE, VALUES anchors, grouping/aggregates, LATERAL and
expression subqueries also retain explicit remaining obligations.
An actually recursive definition with its own `WITH RECURSIVE` prefix returns
`recursive_body_with` Unsupported; an ordinary local WITH prefix is admitted
when its definitions are independent of the outer recursive binding.

## Parameters and checked rendering

Definitions contribute parameter occurrences once, in written order, including
unused definitions. Recursive references and evaluation rounds do not duplicate
lexical parameter positions. Numbered parameters retain their identities;
anonymous parameters retain their sequential positions. Anchor, recursive-arm
and outer modifiers preserve their own order.

The public complete-query certificate and unchanged-catalog interface are
retained. Independent recursive judgments compose with the existing validity
judgments and their parameter-translation preservation theorems. Successful
checking constructs these derivations; validity is not defined as checker
success. Identity and PostgreSQL rendering continue to require their separate
checked AST roundtrip and parameter-preservation contracts.

## Verification populations

The factor has [50 authored queries](../fixtures/recursive_contract/synthetic.json)
and [50 unchanged source queries](../fixtures/recursive_contract/CONCRETE_SOURCES.md).
Every source query contains an actual recursive reference. The authentic
population consists of 31 DuckDB engine regressions, 14 PostgreSQL regressions,
four SQLC tests and one shipping Hatchet application constant. Pinned files,
selectors, SQL hashes and licenses are retained; original SQL is never executed.

Twenty-one source queries have independently preregistered complete output
schemas: 24 positions comprising 20 INT32, two TEXT, one INTEGER array and one
BIGINT. All are nullable recursive references. The other 29 receive checked
rendering without invented catalog, parameter or helper-function declarations.
Eligibility is established by source inspection and the independent premises,
not by filtering for checker success.

The authored fixtures specify 58 ordered output positions, parameter values,
finite expected row bags and four populations: empty, nodes only, edges only,
and both. They cover integer and floating sequences, exact NUMERIC/VARCHAR
modifiers, NULL, arrays, duplicate elimination, Fibonacci pairs, nested sources
and definitions, lexical parameters, hierarchies, graph paths and weighted
paths. A separate frontier model computes the finite graph expectations.
Ordered pagination cases compare sequence as well as multiplicity.

Native PostgreSQL observations compare both source and checked canonical forms,
with 400 finite result comparisons and 116 exact descriptor positions.
SQLite uses separately declared expectations, explicit input/rendering
exclusions, and registered analysis errors for its recursive-reference and
column-alias restrictions.

The separate 85-case boundary population never executes a recursive query.
It uses PREPARE outcomes and prepared result descriptions to observe reference
placement, modifiers, unknowns, exact type modifiers and collation differences.
Its static classifications are registered independently from PostgreSQL
acceptance, including native-success cases that remain Unsupported.

These native observations do not establish universal row semantics,
termination, planner equivalence, literal-conversion success, privileges or
resource bounds. The contracts remain static validity and rendering contracts.

## Integration results

The focused Lean suites pass 56 type/scope/boundary checks, all 50 authored
full-query certificates, all 21 registered authentic certificates and 105
renderer checks. All fifty authentic statements receive checked identity and
PostgreSQL rendering.

The native harness passes 400 PostgreSQL 16.15 result comparisons and 116 exact
descriptor positions. SQLite 3.45.1 passes 312 result comparisons and sixteen
registered analysis errors; nine queries have explicit input/render exclusions.
The separate boundary harness passes forty exact positive schemas, 24 Invalid
and 21 Unsupported classifications, 170 PostgreSQL source/canonical PREPARE
outcomes and ninety prepared descriptions. An ordinary, nonrecursive UNION
control involving CURRENT_SCHEMA retains its nullable result independently
from nonnullable CURRENT_CATALOG.

The warning-free build completes 459 jobs. The full Lean and scope suites,
1,135 Python tests, focused boundary protocols and offline generators pass.
Existing set-operation, CTE, SQL92 ordering and assurance CLI regressions pass.

The broad renderer replay passes 1,237 SELECTs, 2,474 identity/PostgreSQL
renderings, four hundred SQLite renderings and eight hundred bounded SQLite
comparisons. Grammar replay passes 12,209 records, 44 protocol checks, 125
outer statement families and 2,396 observed reduction productions. The
[industrial corpus replay](corpus/recursive-cte-v0.31/README.md) retains
257 typed-parser acceptances and nineteen documented rejections.

The compiled trust audit checks 28,122 declarations, including 15,607 theorems
and 601 generated recursion helpers, and rejects all five deliberate bypass
witnesses. Its frozen input inventory SHA-256 is
`7a0b9e26f7da1aa339c9a067e15cd11550cebee1e0f0d9663561f60bc3330433`,
based on commit `96abfe3e881ec12d8c2599889d6503e583d0caf1`. Both independent
source guards now admit the reviewed normative recursion helper while
rejecting parser, renderer or executable-inference imports into the validity
specification.

## Reproduction

```sh
lake build --wfail
python3 scripts/generate_recursive_contract_examples.py --check
python3 scripts/extract_recursive_contract_corpus.py --check
python3 -m unittest discover -s scripts -p 'test_recursive*.py'
python3 scripts/check_recursive_contract_cli.py --local-bin /path/to/postgresql-16/bin
python3 scripts/check_recursive_boundaries.py --local-bin /path/to/postgresql-16/bin
python3 scripts/check_lean_trust.py --evidence-json .lake/trust-audit-v31-final.json
```

CI includes the new fixtures, extraction, native comparisons, boundary
observations and pinned grammar replay. Lean's disclosed foundational axioms
remain `propext`, `Classical.choice` and `Quot.sound`; project-defined axioms,
proof placeholders and native proof shortcuts remain prohibited.

## Primary references

- [PostgreSQL 16 recursive query evaluation](https://www.postgresql.org/docs/16/queries-with.html#QUERIES-WITH-RECURSIVE)
- [PostgreSQL 16 SELECT and WITH syntax](https://www.postgresql.org/docs/16/sql-select.html)
- [PostgreSQL 16 expression collation rules](https://www.postgresql.org/docs/16/collation.html)
- [SQLite recursive common table expressions](https://www.sqlite.org/lang_with.html#recursive_common_table_expressions)
