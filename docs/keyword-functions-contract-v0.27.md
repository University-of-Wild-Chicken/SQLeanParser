# Keyword function heads and LEFT/RIGHT: v0.27

The profile `sqlean-basic-select-v0.27` adds the two exact PostgreSQL 16
declarations `left(TEXT, INTEGER) → TEXT` and `right(TEXT, INTEGER) → TEXT`.
The typed parser also accepts PostgreSQL type/function keywords in their
ordinary unqualified function-call position. This closes the LEFT call syntax
dependency in River's original `indexReindexArtifacts` query without claiming
an independent contract for that query's CTE and catalog dependencies.

## Exact static contract

Both declarations use the existing `Expr.call`, `ExprValid.call`, overload
resolution and proof-carrying checker. There is no new expression constructor
or alternate validity path. Adding the two declarations brings the fixed
ordinary function inventory to 94. The separate two-entry signature fixture
is linked to these normative declarations and native catalog observations.

The first argument accepts TEXT, VARCHAR, CHAR and NAME through the existing
exact implicit coercion rules. The second accepts INTEGER or SMALLINT widened
to INTEGER. BIGINT, NUMERIC, REAL and DOUBLE PRECISION counts require an
explicit cast; concrete TEXT counts and BOOLEAN counts do not coerce
implicitly. BYTEA and array subjects have no admitted overload. Unknown
string/NULL operands receive the unique TEXT/INTEGER signature context,
including when both operands are unknown.

Both functions are strict and return unmodified TEXT. The conservative output
nullable flag is the OR of the two input flags. Input modifiers do not appear
on the result. CHAR-to-TEXT conversion strips trailing padding before the
function executes; VARCHAR preserves its spaces. NAME uses its existing
implicit TEXT conversion. These conversions are not AST rewrites.

Negative and extreme INTEGER counts remain statically valid. Unknown
non-integer strings and out-of-range counts can fail native input conversion
during analysis or execution. An explicitly invalid argument conversion can
fail even if another argument is NULL. The contract proves typing and
nullability bounds, not successful execution or a complete value semantics.
PostgreSQL counts encoded characters, not bytes or user-perceived grapheme
clusters; combining marks and joined emoji therefore remain separate character
positions.

## Syntax, names and rendering

An unquoted `TYPE_FUNC_NAME_KEYWORD` head is admitted as an ordinary function
name when immediately followed by `(`. It does not thereby become a column or
relation identifier. Quoted names retain exact spelling, so `"left"` denotes
the admitted function while `"LEFT"` is a distinct unregistered name.
`pg_catalog.left` and `pg_catalog.right` use existing structured qualified-call
names. Arbitrary functions with the newly admitted keyword spelling remain
outside the fixed signature inventory.

Both functions have no registered parameter names or defaults. This increment
does not manufacture a named-call environment for them. The preceding
`make_interval` named/default contract remains separate.

The native strong output label is `left` or `right` and survives casts.
The existing CASE label rule inherits an ELSE label; a function appearing
only in THEN does not supply the CASE label. Expression traversal preserves argument order,
including anonymous occurrences and repeated or reversed numbered bindings.
The existing universal translation-validity, idempotence and serialization
theorems continue to apply unchanged. Identity and PostgreSQL rendering retain
their exact AST round-trip certificates. SQLite's independent rendering
profile does not claim native LEFT/RIGHT function support.

## Registered checks and source scope

The focused registry covers all pairs of 25 exact declarations for both
functions, under all four input-nullability combinations, plus unknown
contexts, explicit conversions, labels, malformed arities, unsupported
functions, parameter ordering and resource exhaustion. Independent kernel
derivations construct admitted calls without invoking the checker.

The targeted `--wfail` build and replay pass 5,076 focused contract checks,
50 authored complete-query certificates, 49 fixed authentic-query certificates,
and 376 renderer checks. All fifty authentic statements pass both checked
rendering profiles. The previous 100 scalar corpus cases and 54 boundary cases
also pass, including exact linkage of the expanded 94-declaration inventory.

The authored corpus has fifty distinct queries: 25 LEFT and 25 RIGHT cases.
Every authored query requires a complete independent SELECT certificate,
ordered output metadata, both checked renderings, and translation preservation.
Native value/descriptor checks execute authored SQL only.

The authentic corpus has fifty unchanged queries. Its fixed eligible
population contains 49 source-free queries and 50 output positions. The
PostgreSQL source projects both functions, four Materialize NULL cases have
nullable TEXT outputs, and all other eligible outputs are nonnullable TEXT.
The River catalog/CTE query receives rendering certificates only; no invented
catalog or parameter declarations are supplied. Eligibility and output
expectations are registered by source identity before checking. Original
source SQL is not executed.

## Recorded extreme-count boundary

The local PostgreSQL binary reports version
`16.15 (Ubuntu 16.15-0ubuntu0.24.04.1)`, version number `160015`, compiled for
x86_64 by GCC `13.3.0-6ubuntu2~24.04.1`. Its binary SHA-256 is
`201d8daff9a5bd9df70b820471b965c39f5a776d677f395232c477d051270722`.
Both a constant query and a forced-generic prepared query observed
`right('abcde', -2147483648)` returning `abcde`; the adjacent count
`-2147483647` returned an empty string.

The separately pinned PostgreSQL source commit
`f0595c3d839debdb140903621c1b44a4f4d86256`, file
`src/backend/utils/adt/varlena.c`, has SHA-256
`2fd36782cec91e87dc93166423294d627e07bf8fb2fa36fc30b89414a2d3f236`.
Its lines 5552–5557 explicitly clamp the INT32_MIN case. This establishes an
observed source/binary discrepancy; its cause is not established here.
The fifty authored value expectations exclude this RIGHT extreme. Static
typing and authentic-source rendering still cover it, without asserting an
execution result.

The native integration replay passed 100 value/OID observations, 100 SQL NULL
observations, 124 ordered descriptors and 16 expected execution errors. Its
1,266 analysis outcomes and two exact `pg_proc` declarations agree with the
registered profile. The CLI checks also passed 1,279 static/parser boundaries
and fifty exact SQLite exclusions: two qualified calls reach the scalar-function
coverage boundary, while the other 48 unquoted keyword heads are rejected by
SQLite input parsing. Original source SQL is never executed.

The [boundary observation](corpus/keyword-functions-v0.27/int32-min-observation.json)
retains the authored SQL, exact native output and source/binary hashes.
The full 437-job `lake build --wfail`, complete Lean suites and 959 Python
tests passed. The broad renderer replay passed 1,237 inventoried SELECTs and
2,474 identity/PostgreSQL renderings; its SQLite replay passed 400 renderings
and 800 bounded execution comparisons. Previous scalar, context-value and
named-argument native integrations also passed.

The compiled audit checked 26,350 declarations, including 14,552 theorems
and 576 generated recursion helpers, and rejected all five bypass witnesses.
Its input inventory SHA-256 is
`e3dd43854c12f54cb8895741a7f295c44de67531bdeae9adda0da25a7a573688`,
computed over the frozen working tree based on commit
`b890cbdfec07452766ece6a506a9f3bdfdc2d81d`. The disclosed Lean foundations are
`propext`, `Classical.choice` and `Quot.sound`. No custom axioms, `sorry`, unsafe
declarations or native proof-evaluation shortcuts are introduced. This bounded
increment does not complete PostgreSQL validity contracts or authorize release.

## Primary references

- [PostgreSQL 16 string functions](https://www.postgresql.org/docs/16/functions-string.html)
- [Pinned PostgreSQL grammar](https://github.com/postgres/postgres/blob/f0595c3d839debdb140903621c1b44a4f4d86256/src/backend/parser/gram.y), `func_name` and `type_function_name`
- [Pinned LEFT/RIGHT implementation](https://github.com/postgres/postgres/blob/f0595c3d839debdb140903621c1b44a4f4d86256/src/backend/utils/adt/varlena.c#L5541)
