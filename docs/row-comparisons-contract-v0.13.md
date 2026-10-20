# Row-constructor comparisons: v0.13

`sqlean-basic-select-v0.13` adds direct row-constructor comparisons using `=`,
`<>`, `<`, `<=`, `>` and `>=`. This completes the next bounded part of the
original external-corpus audit's array/quantified/row-comparison priority.
The audit includes six Temporal SELECT statements and a DELETE containing
such a SELECT whose tuple comparisons were still rejected before this
increment. Their source presence motivates syntax coverage; it supplies no
application catalog or execution guarantee.

The AST represents a row as an ordered list of expressions. Explicit
`ROW(a,b)` and implicit `(a,b)` normalize to that same constructor. A binary
comparison retains its two complete row operands. Explicit `ROW(a)` is a
one-field row, whereas `(a)` remains a parenthesized scalar expression.
`ROW()` is preserved syntactically, but comparing empty rows is Invalid,
matching PostgreSQL's rejection. Unequal field counts are also Invalid.

The independent `ExprValid.rowComparison` constructor requires two
`ExprListValid` derivations and an explicit selected-operator list from
`rowComparisonSignature`. Each field pair uses scalar overload resolution,
including contextual unknown inputs and admitted implicit casts. Every
selected result must be Boolean. A singleton comparison uses its scalar
operator directly. For longer rows, every selected operator must also
belong to the fixed admitted B-tree strategy inventory; `<>` uses the
negator of equality. The contract follows PostgreSQL's
[row-comparison transformation](https://github.com/postgres/postgres/blob/REL_16_STABLE/src/backend/parser/parse_expr.c).

The scalar inventory reuses the 32 argument pairs already checked for the
six quantified-comparison operators. Same-type array fields use the admitted
polymorphic array comparison family and retain its element-operator
requirements. INTEGER[] versus BIGINT[] fields do not silently gain a common
array type. JSON scalar fields lack an equality operator and are Invalid.
JSON[] fields remain Unsupported because PostgreSQL can defer the missing
element operator until execution. JSONB fields are admitted.

All successful comparisons report conservative nullable BOOL metadata.
For equality, a decisive unequal field can determine false despite another
NULL comparison; ordering instead proceeds lexicographically until a field
determines the result or produces NULL. The current static metadata does not
attempt value-dependent refinement. The native examples exercise these
[distinct row-comparison behaviors](https://www.postgresql.org/docs/16/functions-comparisons.html#ROW-WISE-COMPARISON),
without claiming a general evaluation theorem.

Bare string and NULL fields receive the scalar operator's context. That
establishes admissible type conversion, not successful input parsing:
malformed literal contents can fail when PostgreSQL analyzes or evaluates
the query. Other runtime failures remain outside the static certificate.

Standalone row values, nested composite fields, row-valued IN, composite
columns and quantified row subqueries require a separate record-type
contract. The syntax and checked renderer retain standalone/nested row
constructors, but independent value checking reports Unsupported. Nested
rows are not flattened: PostgreSQL composite-record comparisons have
different NULL behavior from flat constructor comparisons.

There is intentionally no general `ExprValid.row` constructor in this
profile. Consequently the old generic binary-expression rule cannot bypass
the specialized constructor-pair rule. A direct kernel theorem checks this
absence, while another constructs a nontrivial row comparison without
calling the checker. Noncomparison binary operators on two row constructors
are Invalid. Exhausted checker fuel remains Inconclusive.

Parameter uses preserve the complete left field list followed by the
complete right field list. Pairwise operator selection does not interleave
their lexical occurrences. Global anonymous ordering and placeholder
notation checks still occur once at the outer query boundary. General
translation proofs retain the selected signatures, row shape, nullable
output metadata and whole-query validity.

PostgreSQL canonical rendering spells constructors with `ROW(...)` and
preserves exact normalized AST roundtrips. The SQLite renderer uses tuple
syntax for rows with at least two fields and rejects empty/singleton rows.
Its structural rendering evidence does not assert cross-dialect comparison
semantics.

Verification includes 50 synthetic full-query certificates with exact BOOL
metadata, identity/PostgreSQL rendering certificates and validity transport.
The 274 focused Lean checks include all 192 declared scalar operator
triples, full two-field query certificates for those operators, every
comparison spelling, singleton and implicit constructors, mixed scalar
types, arrays, NULLs, unknown inputs, invalid arities, unsupported composites
and parameter/resource boundaries. A separate PostgreSQL catalog audit
checks B-tree strategy membership and the equality-negator relation.

Fifty unchanged concrete source statements receive rendering evidence only,
retaining their original dialect and provenance: 16 Hatchet, six Temporal,
eight PostgreSQL and twenty SQLite queries. The population contains no
authentic `<>` spelling; synthetic cases cover all six operators. The
updated 276-record industrial audit accepts 233 records, including all seven
original row-comparison cases, and documents 43 remaining syntax rejections.

Native verification checks 100 source/rendered PostgreSQL value-and-OID
observations, 112 exact descriptors, 198 operator/strategy entries, and ten
expected execution errors. The SQLite profile admits 38 synthetic cases;
28 have directly portable source spelling, giving 66 native observations.
Twelve further cases are explicitly excluded by its syntax or rendering
domain. The CLI reads SQLite tuple spelling, while direct Lean renderer tests
also transport explicit PostgreSQL ROW ASTs to that spelling.

SQLite expectations are authored separately. Unknown string fields do not
receive PostgreSQL's scalar operator context, and NUMERIC/VARCHAR modifiers
are not enforced in the same way. Four synthetic cases intentionally have
different expected comparison values in the two engines. These differences
are checked, not hidden by a shared oracle. The 89 focused renderer checks
also distinguish direct tuple syntax from parenthesized subscript bases.

Native values, descriptors, operator catalog checks and expected errors supplement the independent
typing rules. This increment does not complete PostgreSQL record typing or
the full PostgreSQL validity contract.
