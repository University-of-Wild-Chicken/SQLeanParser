# Quantified array comparisons: v0.11

`sqlean-basic-select-v0.11` adds scalar comparisons against arrays using
`ANY`, `SOME` and `ALL`. Its dedicated AST records one of `=`, `<>`, `<`,
`<=`, `>` or `>=`, the quantifier spelling, and the two expressions.
`!=` normalizes to `<>`. Array subqueries, subscripts, slices, row comparisons
and the distinct quantified-subquery form remain later increments.

The independent `ExprValid.quantifiedComparison` rule requires validity
derivations for both operands and an explicit selected scalar operator from
`quantifiedComparisonSignature`. Selection uses the left scalar and the right
array's scalar element type. It does not compute a common type of the left
operand and the whole array. The fixed PostgreSQL 16 operator environment
contains 32 scalar argument pairs for each of the six operators, with a
Boolean result. The selected argument types and result remain part of the
derivation. User-defined operators and search-path overrides are outside this
closed environment.

Mixed scalar comparisons can therefore succeed where whole-array comparison
cannot: `1 = ANY(ARRAY[1::BIGINT])` is admitted even though equality between
INTEGER[] and BIGINT[] is unavailable. Multidimensional arrays still have one
scalar element type; an array-valued left operand is not interpreted as a row
or subarray comparison. The rule also verifies that the original right array
can coerce to the selected operator's right-input array type. This follows
the structure of PostgreSQL's
[scalar-array operator transformation](https://github.com/postgres/postgres/blob/REL_16_STABLE/src/backend/parser/parse_oper.c).

Bare string literals and untyped NULL remain unknown inputs. Thus
`2 = ANY('{1,2}')`, `2 = SOME(NULL)` and `'b' = ANY('{a,b}')` can acquire
their contextual array types. An explicitly typed TEXT expression remains
TEXT: `2 = ANY('{1,2}'::TEXT)` is Invalid. PostgreSQL can reject malformed
literal contents during analysis or execution. This type-level evidence
does not prove successful value conversion in either phase.

Every admitted result has BOOL type with `nullable = true`. This is a
deliberate conservative bound because current array metadata contains neither
member nullability nor cardinality. It also applies to constant empty arrays.
PostgreSQL evaluates empty-array ANY/SOME as false and ALL as true, including
a NULL left operand. NULL arrays and NULL members can instead yield NULL;
a decisive successful ANY comparison or unsuccessful ALL comparison can
determine the result despite other NULL members. These observations follow
the [PostgreSQL array-comparison rules](https://www.postgresql.org/docs/16/functions-comparisons.html#FUNCTIONS-COMPARISONS-ANY-SOME).
They are exercised by native examples, rather than claimed as a proved
evaluation semantics.

Scalar JSON comparison against JSON[] is Invalid because there is no admitted
scalar JSON comparison operator. This differs from the existing Unsupported
boundary for whole-array JSON[] comparison, whose element-operator problem
can be deferred by PostgreSQL until execution. Unsupported child expressions
and unknown function signatures retain their own Unsupported status. Budget
exhaustion remains Inconclusive.

The parser and checked renderer distinguish the array form from quantified
subqueries. An exact scalar-query RHS cannot be encoded as this constructor:
adding parentheses does not resolve PostgreSQL's subquery interpretation.
A cast-wrapped scalar subquery can be rendered as an array expression but
still receives Unsupported from the current independent SELECT contract.
SQLite refuses quantified array comparisons.

Parameter uses concatenate the left expression's occurrences followed by the
right expression's occurrences. The existing whole-query check enforces
global anonymous ordinals and consistent placeholder notation. General
parameter-translation proofs preserve the chosen operator, quantifier,
ordered uses, exact output metadata and complete validity derivation.
Identity and PostgreSQL checked rendering retain exact normalized AST
roundtrips.

Verification includes 50 synthetic full-query certificates, exact nullable
BOOL outputs, checked identity/PostgreSQL rendering, and validity preservation.
The focused Lean suite also checks every declared operator pair in a full
query, all quantifier/operator spellings, contextual literals, invalid type
combinations, unsupported subqueries, parameter order and resource exhaustion.
The 192-row operator fixture is parsed independently into exact types and
must match the overload selected by both normative scalar and quantified
resolution. A separate PostgreSQL catalog audit checks those declared
operator signatures, strict Boolean results, argument count and absence of
set-returning implementations. Direct kernel witnesses construct the new
independent validity rule without invoking the checker.

Fifty unchanged concrete source statements receive rendering evidence only.
They contain 41 ANY and 10 ALL occurrences; no authentic SOME spelling was
found in the pinned source population. The synthetic cases cover all three
spellings. Native verification includes 100 source/rendered value-and-OID
observations, 106 exact descriptors, 10 expected errors and the 192 operator
catalog observations.
Native source/canonical executions and catalog observations supplement the
Lean contracts; they do not establish arbitrary PostgreSQL evaluation
equivalence or complete the full PostgreSQL validity contract.
