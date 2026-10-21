# Release review and closure ladder

`0.0.1-alpha` remains gated on full independent typed-validity and rendering
contracts across the pinned PostgreSQL 16.15 grammar. The separate raw-grammar
certificate and a successful development increment do not satisfy that gate.

The required review order is:

1. Two independent **GPT-6 Luna** reviewers.
2. Two independent **GPT-6.1 Sol** reviewers.
3. Two independent **GPT-6 Astra** reviewers.

Both reviewers at a level inspect the same frozen candidate. A concrete
constructed objection stops advancement: retain its SQL/AST witness, catalog
and parameters, expected behavior, actual result, code location and raw evidence.
Resolve its semantic cause, register an independent regression check, and obtain
a fresh review of the repaired candidate. An unavailable or incomplete review
does not count as a clean result. Known documented coverage gaps remain release
obligations even when they are not defects in an admitted fragment.

Reviews generate candidate issues and experiments. Their opinions are not
proofs or final verifiers. An objection is discharged by its registered kernel
check, exact native observation, provenance check or other appropriate mechanical
verifier, followed by independent review of the repair. Tests establish only
their finite surface; native runtime failures are kept separate from static
validity and exact metadata claims.

The release candidate must also pass the mechanical closure protocol: a finite
claim set and verifier registry, canonical input hashes, explicit trusted
dependencies, unique implementation-to-proof correspondence, checked witnesses,
two isolated clean builds, declared determinism comparisons, and complete public
claim provenance. The final state must be `VERIFIED` for that frozen surface.
There is no manual override or conversion of an unresolved result into a pass.
Changing verification-relevant inputs invalidates the candidate's evidence;
earlier review or proof results are not inherited by a new release candidate.

The whole-grammar denominator is 3,284 upstream productions and 125 outer
statement families at PostgreSQL commit
`f0595c3d839debdb140903621c1b44a4f4d86256`. Required authentic examples, typed
AST coverage, independent validity and rendering obligations must remain
explicit. Missing examples are not replaced by authored or rewritten inputs.
Full PostgreSQL contracts cannot be inferred from the production count.

## Initial preflight

The first complete six-reviewer preflight examined development commit
`21cd72b60b9b42825ac568ad5f3cb4f47db153c3`, not a release candidate. Both Luna
and both Sol reviews found no concrete in-scope objection. The Astra level
constructed two blocking counterexamples:

- **ASTRA2-001:** minus-only integer-literal chains were typed before complete
  raw-literal folding. `SELECT -(-2147483648)` was reported as INT32 instead of
  PostgreSQL's BIGINT; the corresponding `2^63` case requires NUMERIC.
- **ASTRA1-001:** known array element coercion could lose a synthesized collation
  contribution. `CAST((SELECT ARRAY['x']) AS NAME[])` was reported with default
  collation instead of C; implicit POSIX inputs could instead become indeterminate.

These findings stop the preflight at the Astra level. Their independent native
regression registries are retained under `fixtures/review_regressions/`.
The repairs and rechecks belong to a later input root; this baseline remains a
recorded failed candidate and cannot authorize publication.

The [v0.34 independent rechecks](../reviews/repairs-v0.34/index.json) retain
the repaired binary hash and the finite witness counts for both objections.
CI reruns their checked-in regression registries. Historical temporary log
paths are recorded as such; the retained fixtures and scripts reproduce the
checks. `python3 scripts/check_review_ladder.py` validates this design policy
and the original archive's hashes, routing and blockers. It does not evaluate
release readiness or produce a mechanical-closure state.

The machine-readable [release plan](../../release/0.0.1-alpha/plan.json) fixes
the required models, escalation order and release obligations. It is a design
record, not a completed mechanical-closure report or permission to publish.
