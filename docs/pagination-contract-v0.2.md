# Expression pagination contract — v0.2

This document specifies the first implementation increment from the
[external PostgreSQL syntax audit](corpus/postgresql-2026-10-20/README.md):
expression-valued `LIMIT` and `OFFSET`. It extends the implemented independent
SELECT profile to **`sqlean-basic-select-v0.2`**. It supplements the broader
[SELECT validity draft](SELECT_validity_contract.md) and
[renderer contract](SELECT_render_contract.md); it does not claim their
remaining general SELECT or semantic-preservation obligations are complete.

The implementation, targeted Lean proof tests, pagination corpus checks, and
native-database witnesses have passed. This completes the first factor at the
assurance levels specified below; it does not close the broader contracts.
Historical corpus reports retain their original versions, counts, and hashes.

## 1. Representation and grammar

`Advanced.Query.limit` and `Advanced.Query.offset` have type
`Option Advanced.Expr`. `none` means that the clause is absent. `some .null`
represents a present NULL expression and must survive serialization as such.
These cases must not be merged because their syntax and dialect behavior differ.

The ordinary advanced grammar accepts:

```ebnf
pagination = [LIMIT expr] [OFFSET expr] ;
```

The existing expression AST represents literals, parameters, unary and binary
operators, casts, and nested expressions in these positions. Parsing a
represented expression does not imply that it is valid as a row count.
Parentheses preserve the expression tree. Clause-level parameter traversal is
query body, ordering, LIMIT, then OFFSET, after any preceding CTEs; nested
queries retain their own structural traversal.

`OfNat Advanced.Expr n` and `Coe Nat Advanced.Expr` construct integer-literal
expressions. Hand-built records such as `{ query with limit := some 10 }`
therefore remain convenient. This is source-construction compatibility, not
an assertion that clients pattern-matching the former `Option Nat` fields need
no changes. The older relational compatibility AST and grammar retain their
literal pagination interface.

The SQLite parser also retains `LIMIT offset, count` **for unsigned integer
literals only** and represents it in canonical LIMIT/OFFSET fields.
`LIMIT ALL`, OFFSET-before-LIMIT, and expression-valued comma pagination are
deferred. In particular, accepting anonymous `?` expressions in reversed clause
order would need an explicit binding-order design; silently renumbering them
is not allowed.

## 2. Independent static rules

The normative judgments are in
[SelectContract.Spec](../SQLean/SelectContract/Spec.lean), which imports the
fixed [profile](../SQLean/SelectContract/Profile.lean) and immutable syntax,
not the executable checker. The profile's concrete scalar types remain INT32,
TEXT, and BOOLEAN, each with explicit nullability.

`PaginationValid params bound uses` shall hold for an absent bound, or for a
present expression with:

1. An `ExprValid params [] expr type uses` derivation in an **empty local
   scope**. Neither current input columns nor SELECT output aliases are
   available. Declared parameters remain available.
2. A `RowCountCoercion type` derivation: either an unknown NULL acquires the
   row-count context, or a nullable/non-null INT32 result widens to PostgreSQL's
   signed 64-bit `int8` row-count target.

`int32_row_count_widening` proves that every signed INT32 value is within the
signed 64-bit range. This contextual conversion does not add BIGINT to the
general scalar profile, change expression result types, or add implicit
conversions to the operator/cast tables. BIGINT declarations and casts,
decimal expressions, and integer literals beyond the implemented INT32
literal range remain unsupported by independent validity checking.

INT32 arithmetic, parameters, unary signs, and existing explicit casts can
therefore form bounds. A concrete TEXT or BOOLEAN expression cannot be used
directly as a row count under this profile; an appropriate explicit cast must
first produce INT32. Bare string literals receive `unsupported` because their
PostgreSQL contextual conversion is outside the implemented rules. NULL is
permitted directly. Scalar subqueries in bounds remain outside independent
basic validity, even when the expanded syntax and renderer can represent them.

The full `SelectValid` rule shall include derivations for **both** bounds and
include their occurrences in query-wide `ParameterOrder`:

```text
projection ++ WHERE ++ ORDER BY ++ LIMIT ++ OFFSET
```

For this basic fragment there are no CTEs or derived sources. Positive numbered
parameters may repeat. Anonymous occurrences must be exactly `1, 2, …` across
all represented clauses; mixed notation is invalid. Pagination must not hide
undeclared parameters, skipped anonymous ordinals, or mixed styles.

## 3. Full-query evidence and bounds-only evidence

`checkQuery .basicV02 catalog params query` returns a full independent
`Certificate` only when the complete basic SELECT derivation exists. Its
ordered output names, exact types, and nullability remain justified, and
`catalog_unchanged` retains the input catalog. All supplied catalog and
parameter declarations must be supported by the full profile, including
unused declarations.

The basic fragment still consists of source-free or single-table SELECTs,
projection aliases and wildcards, WHERE, ordinary DISTINCT, supported scalar
expressions, and the documented ORDER BY rules. Joins, derived sources,
grouping/aggregates, correlation, CTEs, set operations, DISTINCT ON, and ILIKE
do not acquire full independent validity through this increment.

`checkPaginationBounds .basicV02 params query` instead returns
`PaginationBoundsCertificate`, proving only `PaginationBoundsValid` for the
**outer** LIMIT and OFFSET of that exact query. It checks parameter-metadata
well-formedness and each bound's closed typing/coercion derivation. Unused
parameter declarations need not belong to the scalar profile; referenced
parameters must support the required expression derivation.

This local certificate does **not** validate the body, catalog, output schema,
nested queries' pagination, or query-wide parameter notation. It records the
two occurrence lists without assuming that they begin at anonymous ordinal
one. Applications must not promote it to `SelectValid` or describe the whole
query as independently valid. The separate whole-AST rendering check can
establish representation and parameter-notation conditions, but does not fill
the missing static rules.

Full SELECT CLI assurance remains explicit: `--assurance contract` reports
`valid`, `invalid`, `unsupported`, or `inconclusive`. It does not fall back to a
bounds-only certificate. The expanded `checked` and `syntax` tiers remain
available with their existing weaker evidence. Budget exhaustion is
inconclusive; an unimplemented rule is unsupported.

## 4. Runtime and dialect obligations

Static typing is not expression evaluation. Division by zero, INT32 overflow,
invalid text-to-integer casts, and actual parameter values can still cause
execution errors. Even a statically valid negative literal bound retains a
runtime obligation.

`PaginationValueAllowed value` requires every non-NULL evaluated value to be
nonnegative. `PaginationBoundsCertificate.runtimeObligation` states that
condition for both evaluated bounds. The certificate supplies **no proof**
that either expression evaluates successfully or that this predicate holds;
it also does not define a database execution semantics.

PostgreSQL coerces pagination to `int8` and prohibits current-query row
references in that context. NULL LIMIT means no limit; NULL OFFSET means zero.
Negative non-NULL results are execution errors. The implemented independent
profile is narrower than PostgreSQL's complete coercion and correlation rules.
[PostgreSQL 16 SELECT](https://www.postgresql.org/docs/16/sql-select.html#SQL-LIMIT),
[row-count analysis](https://github.com/postgres/postgres/blob/REL_16_STABLE/src/backend/parser/parse_clause.c),
[executor behavior](https://github.com/postgres/postgres/blob/REL_16_STABLE/src/backend/executor/nodeLimit.c).

SQLite accepts row-count expressions convertible losslessly to integers,
rejects NULL bounds, treats a negative LIMIT as unlimited, and treats a
negative OFFSET as zero. Its OFFSET clause requires LIMIT. The SQLite renderer
retains these native semantics; a PostgreSQL-oriented static certificate does
not establish equivalent SQLite execution.
[SQLite LIMIT clause](https://www.sqlite.org/lang_select.html#the_limit_clause).

No certificate guarantees deterministic pagination without sufficient
ordering, identical row selection across tied sort keys, or successful query
execution.

## 5. Renderer obligations and proved laws

The independent common and SQLite admissibility traversals shall inspect both
bound expressions recursively. Parameter occurrences, depth, names, literal
lexemes, constructor consistency, and target exclusions inside pagination
must be checked just as in other expression positions. A SQLite-excluded
construct nested inside a pagination subquery must remain excluded.

A successful `RenderContract.check` certificate covers exact full AST
reconstruction, canonical rendering, independent admissibility, and the
parameter map, including occurrences used only in LIMIT/OFFSET. The identity,
PostgreSQL, and SQLite target profiles retain their published v0.1 IDs; this
document versions the independent static pagination extension. Their separate
target assumptions and slot limits continue to apply.

The general proofs extend through the new expression fields:

- `translateParameters_idempotent` preserves structural idempotence.
- `renderPostgres_translateParameters` and
  `renderSQLite_translateParameters` preserve rendered bytes under parameter
  translation for every finite AST.
- `pagination_valid_translated` and `pagination_bounds_valid_translated`
  preserve the local typing derivations and parameter indices.
- `translateParameters_valid` preserves a full independent basic SELECT
  derivation with the same parameter environment and exact ordered output.
  The existing checked-roundtrip corollaries transfer that evidence to the
  reconstructed AST.

These are Lean kernel-checked AST/static laws. Full roundtrip success remains
certified per successful checked instance. A universal theorem that every
admissible AST succeeds, independent source-parser fidelity, and complete
database-semantic preservation remain open obligations.

The proof policy forbids `sorry`, custom axioms, native proof shortcuts, and
kernel-check bypasses. The project audit permits only Lean's standard
`propext`, `Classical.choice`, and `Quot.sound` foundations. Its build manifest
identifies source/artifact hashes and toolchain versions. Runtime execution of
the compiled checker additionally relies on the compiler and runtime.

## 6. Coverage populations and incremental status

The pagination populations are separate and must retain separate evidence:

- [50 synthetic whole queries](../fixtures/pagination/synthetic.json) use a
  declared INT32 fixture schema, explicit parameter types/values, and
  independently stated expected slices. The full-query checks require
  basic independent validity and checked rendering. Native observations
  distinguish PostgreSQL NULL behavior from SQLite errors rather than demand
  cross-dialect agreement.
- [50 concrete whole statements](../fixtures/pagination/concrete.jsonl) retain
  upstream SQL and provenance: **42 application constants** (20 Temporal,
  21 Cadence, one River) and **eight sqlc compiler regression statements**.
  These are not production traffic and are not 50 independently typed
  application workloads. Their local pagination proofs use explicit test
  parameter declarations and certify the bounds only; source schemas and
  complete application binding contracts have not been proved. Whole-query
  rendering remains a separate obligation.

The [concrete-source ledger](../fixtures/pagination/CONCRETE_SOURCES.md) records
commits, licenses, extraction methods, exclusions, and source hashes.
Re-extraction is offline and does not run upstream application code or SQL.
The optional pinned PostgreSQL raw-parser oracle establishes syntax only.

The completed local integration run checked all 50 synthetic queries with full
independent validity and all three renderer profiles, plus all 50 unchanged
concrete statements with bounds-only validity and identity/PostgreSQL
rendering. It also checked 22 focused static/grammar boundaries. PostgreSQL
`$n` inputs are not submitted directly to the SQLite CLI: synthetic SQLite
fixtures explicitly map them to native `?n` slots and replace the one tested
`::` spelling with CAST. The concrete source corpus remains unchanged and is
not claimed as SQLite input coverage.

Native witnesses used SQLite **3.45.1** and PostgreSQL **16.15**:

- **204 SQLite executions:** source/canonical forms of the 50 synthetic cases
  on empty and seeded databases, plus four negative-bound observations.
- **212 PostgreSQL PREPARE/EXECUTE cases:** the same 200 ordinary observations,
  plus 12 source/canonical runtime-error cases for negative LIMIT/OFFSET,
  division by zero, failed casts, and overflow.

The expected row slices are stated independently of the renderer. NULL and
negative bounds retain their database-specific observations. These results
are finite witnesses, not proofs of all executions or application schemas.

Replaying the original 276-statement external corpus after this increment
increases syntax acceptance from **161 to 185** (from **145 to 169** of the
260 unique statements), with **91** rejections remaining. Fourteen remaining
rejections contain pagination together with other unsupported syntax. The
[new audit evidence](corpus/pagination-v0.2/audit.json) and
[remaining failure catalog](corpus/pagination-v0.2/failures.md) preserve the
original baseline separately. Acceptance counts do not establish source
interpretation or independent static validity.

The targeted [pagination renderer tests](../Tests/PaginationRendering.lean)
include constructive admissibility and 82 cases covering hidden parameters,
depth, malformed bounds, slot limits, nested target exclusions, and exact
roundtrips. They supplement the 50+50 populations rather than count toward
either one.

Reproduce the focused fixture and native checks from the repository root:

```sh
python3 scripts/generate_pagination_examples.py --check
python3 scripts/extract_pagination_corpus.py --check
lake exe sqlean_tests
python3 scripts/check_pagination_cli.py --local-bin /usr/lib/postgresql/16/bin
```

Use the local PostgreSQL installation's binary directory for `--local-bin`.
Alternatively, pass `--dsn` for a test PostgreSQL connection. The CLI runner
requires one of these options and always checks both database runtimes.

Subsequent factors retain the audit's priority: extended concrete types,
general functions and CASE/conditional forms, locking clauses, then
arrays/quantified and row comparisons. Each requires its own grammar,
independent rules, renderer treatment, and distinct synthetic/concrete
evidence. No coverage is claimed for those factors by pagination alone.
The audit's known special-form interpretation defects (`ISNULL`/`NOTNULL`,
session/time value forms, and `ONLY`) also remain pending; reproducing the
parser's AST in the renderer does not resolve those source-interpretation
defects. The historical reports remain unchanged for comparison.
