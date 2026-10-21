# Expression subquery contracts, profile v0.33

This increment adds independent validity and parameter-rendering preservation
for uncorrelated scalar subqueries, EXISTS and scalar IN-subquery comparisons.
It retains the broader PostgreSQL grammar and existing SQLite rendering domain.
Release `0.0.1-alpha` remains held for full PostgreSQL contracts.

## Independent judgments and scope

Expression typing, expression collation and output labels have separate
inductive judgments. Their generic forms accept a strictly positive child-query
judgment. The complete query specification instantiates that argument with its
own independent query judgment, its immutable catalog and parameter environment,
and the exact CTE environment visible at the expression.

The implementation passes a proof-producing child checker into the expression
checkers. A successful child contributes a derivation of the independent rules;
checker success is never a specification premise. Query recursion consumes a
smaller fuel budget. Exhaustion remains inconclusive.

A child can see inherited CTE bindings, including sequential definitions and
nested shadowing. Its local row namespace starts empty and is populated by its
own FROM clause. Outer input columns and output aliases do not become child
bindings. Correlated references remain an explicit unsupported boundary.
The legacy expression-only APIs retain a default relation with no child-query
capability; the new Core judgments make the dependency explicit.

Child queries retain their complete lexical parameter occurrences. Anonymous
indices continue across query boundaries; a child never restarts numbering.
The public SELECT judgment checks notation and order once, after collecting
occurrences from the complete statement. Numbered parameters retain their
identities and can repeat. Runtime observation binds supplied values through
PREPARE/EXECUTE rather than replacing parameters in query text.

## Scalar, EXISTS and IN behavior

A scalar subquery requires exactly one output column. Its concrete type and
modifiers survive, and its result is conservatively nullable because the child
can return no rows. Its strong output label comes from the certified child
column, including SELECT-star expansion. Casts, CASE result inheritance,
subscripts and COLLATE retain the corresponding label rules.

A scalar subquery's known output collation reenters with implicit strength.
A collatable child with an indeterminate output collation remains explicitly
unsupported: PostgreSQL's implicit-invalid SubLink state differs from a stored
relation column with no identity. This increment does not conflate those states.

EXISTS produces nonnullable BOOL with no result collation and the native
`exists` output label. Its complete child is statically checked, including the
projection and every parameter occurrence. This does not claim that PostgreSQL
will evaluate the projection. Planning and execution can discard expressions
or expose errors at different stages.

Scalar IN requires one child output column and an admitted equality overload.
The child has already finalized unknown outputs: `SELECT '1'` produces TEXT,
so an INTEGER left operand is not compared as if the child were an unknown
literal. Operand coercions and input-collation merging have their own premises.
The child is represented with the native PARAM_SUBLINK collation behavior,
which differs from scalar SubLink reentry when its identity is absent.
NOT IN uses Boolean negation of the same typed comparison. Row-valued IN and
quantified query comparisons remain separate coverage gaps.

A static derivation does not establish row cardinality, successful literal
conversion, successful expression evaluation or query termination. PostgreSQL
can raise `21000` when a scalar subquery returns multiple rows. SQLite can
instead select its first row; those are separately registered native outcomes.

## Composition and rendering

Recursive-reference premises inspect expression subqueries in projections,
predicates, JOIN ON conditions, sorting and pagination, as well as FROM and
WITH definitions. Entering an expression SubLink makes a self-reference
forbidden while preserving lexical CTE shadowing. Forward dependencies remain
an explicit coverage boundary rather than falling through to a physical table.

IN-list normalization likewise distinguishes references to a parent input
column from local columns inside an uncorrelated child. This prevents separate
pairwise collation contexts from hiding a required explicit-collation conflict.

The general parameter-translation proof preserves the exact independent output
row, including names, types, nullability and collations. Generic expression and
label lemmas assume preservation only for child queries smaller than their AST
bound; the outer query proof discharges those premises by well-founded
recursion. They do not import or rely on the executable checker.

Identity and PostgreSQL rendering retain checked parser roundtrips, canonical
rendering and ordered parameter transport. SQLite has its existing separate
rendering profile. Native comparisons describe bounded authored fixtures and
do not establish cross-dialect execution equivalence.

## Evidence and reproduction

The authored population has fifty distinct queries per class, with independent
expected rows under four table populations. It includes NULL and empty results,
duplicate rows, exact modifiers, nested queries, aliases, CTE visibility,
collation identities and reordered/repeated parameters. Downloaded source SQL
is retained unchanged with pinned provenance and is never executed. A source's
catalog and legacy feature requirements determine its assurance tier; provenance
alone does not establish full-query static validity.

The [unchanged-source registry](../fixtures/subqueries/CONCRETE_SOURCES.md)
fixes 78 eligible queries and 84 ordered output columns: 37 closed queries and
41 queries under eighteen catalogs derived from retained written declarations.
The other 72 retain rendering assurance. All 150 source inputs are globally
distinct after token normalization. Their original SQL and DDL are never run.

Source replay also exposed a keyword-classification bug: unquoted `key` is a
PostgreSQL unreserved identifier, but the typed parser's clause heuristic
rejected it. PostgreSQL identifier parsing now admits the pinned grammar's
unreserved category while retaining the existing SQLite behavior. Focused AST
and rejection checks cover the distinction. The corpus remains unchanged.

The grammar regression population includes the 300 new queries. Twelve authored
question-mark binding templates undergo an explicit lexical conversion to
numbered PostgreSQL markers for that separate grammar API; their originals and
the conversion are retained in its reports. Authentic source inputs do not
undergo that conversion.

Native replay on PostgreSQL 16.15 passes 1,200 typed-row captures, 1,200
collation captures, 318 descriptor positions, 72 PREPARE/planning/execution
boundary observations, eight operator-input collation checks, and 44
PREPARE-only recursive-reference/IN-normalization controls. SQLite 3.45.1
passes 176 authored row/label observations, including its two registered
scalar-cardinality differences. These counts refer to the bounded authored
experiments, not execution of source examples.

The completed local checkpoint includes `lake build --wfail`, the full Lean
test executable and scope suite, 1,242 offline Python tests from a clean Git-index
export, and all 81 generated-fixture/provenance checks from that export. The
compiled trust audit traverses project declaration dependencies and rejects its
five deliberately forbidden bypass controls. The existing renderer regression
passes 1,237 SELECTs; the separate grammar regression passes 12,559 records.
The original application audit remains 257 accepted statements out of 276;
this static-contract increment does not claim to close its remaining syntax
gaps. Its [audit checkpoint](corpus/subqueries-v0.33/README.md) records the exact
binary and unchanged source inputs.

```sh
lake build --wfail
python3 scripts/generate_subquery_examples.py --check
python3 scripts/extract_subquery_corpus.py --check
python3 -m unittest discover -s scripts -p 'test_subquer*.py'
python3 scripts/check_subqueries_cli.py --local-bin /path/to/postgresql-16/bin --source-registry
python3 scripts/check_lean_trust.py --evidence-json .lake/trust-audit-v33.json
```

CI includes the authored fixtures, unchanged-source extraction, kernel witnesses,
static and rendering checks, native descriptor/collation observations and the
separate PREPARE, planning and execution boundaries. Project-defined axioms,
proof placeholders and native proof shortcuts remain prohibited. Lean's
standard disclosed foundations remain `propext`, `Classical.choice` and
`Quot.sound`.
