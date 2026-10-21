# Row-valued IN contracts, profile v0.34

This increment extends independent SELECT validity and renderer preservation to
flat row-valued `IN (SELECT …)` and its Boolean negation. The full PostgreSQL
16.15 contracts still gate `0.0.1-alpha`; this increment is not that release.

The typing judgment requires a positive left arity, the same number of child
output columns, and an admitted equality overload for every corresponding pair.
The child query uses the complete independent query judgment and its visible CTE
environment. Its outputs are already finalized: an untyped child string or NULL
is TEXT, rather than an unknown literal that can adopt the left operand's type.
Equality does not acquire an unrelated B-tree ordering requirement.

Collation derivations follow the selected coercions independently for each
field. A child's output reenters with PARAM_SUBLINK behavior; separate field
comparisons do not merge their collations with each other. The result is BOOL,
conservatively nullable. The constructor-only witnesses in
[SubqueryContract.lean](../Tests/SubqueryContract.lean) establish the rules without
calling the checker. Generic expression and complete-query translation proofs
preserve output names, exact types, nullability, collation and lexical parameter
occurrences. Correlation and nested composite-valued fields remain explicit
coverage boundaries.

The [authored population](../fixtures/row_in_subqueries/synthetic.json) has fifty
queries, independent expected rows under four table populations, and cases for
empty sets, NULL fields, duplicates, field arity, type coercions, CTEs, derived
sources, sorting and parameters. Row equality's three-valued oracle handles a
false field before unknown fields; IN is an existential disjunction and is false
for an empty child. Expected rows are not copied from either SQL engine.

The [source registry](../fixtures/row_in_subqueries/CONCRETE_SOURCES.md) retains
fifty unchanged complete inputs from six pinned projects. Twelve inputs and
twenty output positions have preregistered full static certificates, using
closed queries or retained written schema declarations. All fifty inputs have
checked identity and PostgreSQL rendering. Other inputs retain their honest
assurance tier. Downloaded SQL and setup DDL are never executed.

The native authored checks compare original and canonical SQL on PostgreSQL
16.15, including exact output descriptors, collations and four data populations.
A portable subset is checked separately on SQLite. PREPARE-only controls keep
arity, operator, collation and unsupported-scope boundaries explicit. These
finite observations do not prove PostgreSQL execution equivalence or successful
runtime evaluation for every statically valid query.

## Constructed preflight objections

The first requested ladder ran two GPT-6 Luna reviewers, then two GPT-6.1 Sol
reviewers, then two GPT-6 Astra reviewers against the same frozen v0.33 source.
The Astra reviewers constructed two blockers. Their original reports and input
manifest are retained under [docs/reviews/21cd72b](reviews/21cd72b/index.json).
The original candidate remains failed; repairs belong to a new input root.

`ASTRA2-001` exposed typing before PostgreSQL's complete minus-only integer-literal
fold. `SELECT -(-2147483648)` requires BIGINT; the corresponding positive `2^63`
requires NUMERIC. Independent rules now type the completed raw fold. Ordinary
unary negation cannot provide a competing derivation for that literal spine.
Unary plus, casts and subqueries retain their native barriers. The independent
signed-integer registry contains seventy authored controls, including exact
native descriptors and separately registered runtime failures.

`ASTRA1-001` exposed a missing element contribution in known-array coercions.
`CAST((SELECT ARRAY['x']) AS NAME[])` needs C collation. Implicit POSIX input
can instead produce an indeterminate result. Coercion now merges the synthesized
element collation while preserving explicit strength, raw ARRAY handling and
same-OID/scalar controls. The independent registry contains 181 authored cases
and checks exact native descriptors and collation identities, including absent
identities. Neither repair adds a custom axiom or proof bypass.

The [review ladder plan](releases/review-closure-ladder.md) requires fresh reviews
on the final frozen release candidate, registered mechanical verifiers, explicit
trusted dependencies and two isolated clean builds. LLM opinions generate
objections; they do not discharge formal claims.

The completed checkpoint passes the Lean build, complete test executable and
scope suite, the compiled declaration trust audit, 1,307 Python tests from a
clean Git-index export, and all 84 fixture/provenance checks from that export.
All 53 CI integration checkers pass, including reruns after correcting stale
concatenation and EXTRACT scalar-subquery expectations. The separate grammar
regression accepts 12,656 records and retains three pinned rejections. The
[application audit](corpus/row-in-subqueries-v0.34/README.md) retains 257 of 276
typed-parser acceptances; its source SQL is not executed.

```sh
lake build --wfail
lake exe sqlean_tests
lake exe sqlean_scope_tests
python3 scripts/generate_row_in_subquery_examples.py --check
python3 scripts/extract_row_in_subquery_corpus.py --check
python3 scripts/check_row_in_subqueries_cli.py --local-bin /path/to/postgresql-16/bin --source-registry
python3 scripts/check_signed_literals_cli.py --local-bin /path/to/postgresql-16/bin
python3 scripts/check_array_coercion_collations_cli.py --local-bin /path/to/postgresql-16/bin
python3 scripts/check_review_ladder.py
python3 scripts/check_lean_trust.py --evidence-json .lake/trust-audit-v34.json
```
