# Quantified query contracts, profile v0.35

This development increment adds scalar and flat-row `ANY`, `SOME` and `ALL`
query comparisons with independent validity, collation and renderer-preservation
rules. It does not authorize `0.0.1-alpha`; full PostgreSQL contracts and the
final review/closure ladder remain required.

`Advanced.Expr.quantifiedQuery` stores the comparison operator, quantifier,
left expression and child query separately from quantified array expressions.
The parser retains the native distinction: `1 = ANY(SELECT ARRAY[1])` compares
INTEGER to a child INTEGER[] output and has no admitted operator, while
`1 = ANY(CAST((SELECT ARRAY[1]) AS INTEGER[]))` is a quantified array expression.
Extra parentheses alone do not convert the former into the latter. A constructed
array-expression AST with a bare scalar-query operand retains an explicit
renderer boundary because its spelling would parse as a different AST.

The child uses the complete independent query judgment and the exact visible
CTE environment. Its row namespace remains local: correlation is a separate
coverage obligation. Scalar comparisons require one finalized child column and
an exact Boolean operator signature. Their potential-NULL flag is the disjunction
of operand nullability. Flat rows require positive equal arity and an exact
operator at every position. Equality/inequality use their requested field
operators without a B-tree requirement; ordering retains the admitted row
strategy. Nested composite fields remain unsupported. Row results remain
conservatively nullable.

Each selected field has its own independent coercion and input-collation merge.
The child reenters with PARAM_SUBLINK behavior. Collations at unrelated row
positions are not merged together. The generic expression/query preservation
proofs retain the complete output metadata and ordered parameter occurrences.
The executable checker contributes derivations of the independent rules;
checker acceptance is not a premise of those rules.

Fifty scalar and fifty row queries have independent finite expected rows under
four table populations. Eighteen additional single-child controls distinguish
all six scalar comparison directions. They include NULL and empty inputs,
duplicate rows, lexicographic row short-circuiting, contextual left literals,
finalized child types, casts, collations, arrays, CTEs and reordered/repeated
parameters. Native checks compare original and canonical SQL: 944 typed-row
captures, 944 collation captures, 236 exact descriptor positions and thirty
PREPARE-only controls. Empty ANY/SOME is false and empty ALL is true even for a
NULL left operand in these observations; static validity does not establish
runtime success for arbitrary queries.

The [authentic registry](../fixtures/quantified_subqueries/CONCRETE_SOURCES.md)
at the v0.35 checkpoint retained 84 unchanged inputs: fifty scalar and 34 row queries.
Eighty preregistered inputs, with 93 ordered output columns, received complete
certificates under closed or retained written catalog declarations. All 84
received checked identity/PostgreSQL rendering. That checkpoint had an explicit
shortage of sixteen authentic row examples. Seventeen additional unchanged
inputs were retained separately: they required VALUES query bodies, including
anonymous derived sources. They were not counted as covered by v0.35 or rewritten
into an easier query. Source SQL and setup DDL are never run.

The [v0.36 VALUES increment](values-query-contract-v0.36.md) subsequently closes
this source shortage. All seventeen retained inputs activate unchanged after
VALUES and anonymous-derived static/rendering gates pass. The active population
is now 101 queries, fifty scalar and 51 row, with 97 complete certificates and
110 ordered output columns. All 101 receive checked rendering. The historical
17-input snapshot remains in `deferred_values_v0.35.jsonl`; these later results
do not rewrite the v0.35 checkpoint counts above or its audit artifacts.

The isolated and main builds pass with warnings treated as errors. The full
Lean executable includes 72 quantified-query constructor, scope and transport
checks. Native replay passes all authored cases and the fixed authentic
registry. The compiled declaration audit checks 31,441 project declarations
and their dependencies; permitted foundations remain `propext`,
`Classical.choice` and `Quot.sound`. This is a bounded development checkpoint,
not a mechanical-closure result for full PostgreSQL.

The clean Git-index export passes 1,341 Python tests and all 87 fixture and
provenance checks. All 54 CI integration checkers pass against the final v0.35
CLI. The grammar regression replays 12,861 records, with three pinned version
rejections. The original 276-query application corpus retains 257 typed-parser
acceptances; the [audit checkpoint](corpus/quantified-subqueries-v0.35/README.md)
binds these observations to the executable and exact source inputs.

```sh
lake build --wfail
lake exe sqlean_tests
lake exe sqlean_scope_tests
python3 scripts/generate_quantified_subquery_examples.py --check
python3 scripts/generate_quantified_row_subquery_examples.py --check
python3 scripts/extract_quantified_subquery_corpus.py --check
python3 scripts/check_quantified_subqueries_cli.py --local-bin /path/to/postgresql-16/bin --source-registry
python3 scripts/check_lean_trust.py --evidence-json .lake/trust-audit-v35.json
```
