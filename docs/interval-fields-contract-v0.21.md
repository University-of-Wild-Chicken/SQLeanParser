# Interval field qualifiers: v0.21

`sqlean-basic-select-v0.21` adds exact PostgreSQL interval field qualifiers
to declarations, casts, typed literals, array element types, and metadata
environments. `Advanced.IntervalFields` enumerates the thirteen legal
qualifiers. `TypeName.intervalRange fields` records the qualifier, while
`DataType.modifiers` retains its optional fractional-second precision.
Existing unqualified `INTERVAL` and `INTERVAL(p)` constructors remain
unchanged.

The independent type is `ScalarType.intervalRange fields modifiers`.
YEAR, MONTH, and YEAR TO MONTH are distinct exact types, as are all other
qualifiers. They share PostgreSQL's INTERVAL base identity but have different
type modifiers. An omitted precision is retained separately from an explicit
precision of six. The representation uses a closed field enum rather than
exposing native integer bit masks as unchecked API inputs.

Qualified precision is admitted only for SECOND, DAY TO SECOND, HOUR TO
SECOND, and MINUTE TO SECOND, and the canonical profile covers zero through
six. Invalid modifier arities and precision on non-SECOND ranges are Invalid.
Excess SECOND precision is Unsupported: native PostgreSQL accepts it with
a warning and clamps it to six, while this profile does not normalize that
source declaration. Casts and catalog/parameter metadata receive this same
coverage diagnosis. Other metadata errors remain Invalid even when an
unsupported precision is also present. The diagnostic check never creates a
certificate for replacement metadata.

The [PostgreSQL 16 interval documentation](https://www.postgresql.org/docs/16/datatype-datetime.html#DATATYPE-INTERVAL-INPUT)
describes the allowed field combinations and precision. Qualifiers do not
mean that every larger field is absent from the stored value: for example,
an INTERVAL MONTH value can contain years as well as months. The certificate
preserves the exact type modifier and does not invent a refinement asserting
that particular value components are zero.

Catalog columns and explicit casts retain the complete field range and
precision, including array element modifiers. Parameter environments retain
their exact declarations, but parameter expression results erase these
modifiers, matching PostgreSQL PREPARE behavior. An explicit expression cast
restores them. Repeated array suffixes retain their existing syntax identity;
the concrete array type has one wrapper around the exact interval element.

The existing static rules continue to distinguish expression contexts.
COALESCE, CASE, and ARRAY constructors preserve a common modifier only when
the participating known types have exactly the same range and precision;
otherwise the common INTERVAL type is unmodified. NULLIF retains the left
expression modifier when no underlying-type conversion is needed.
Arithmetic, unary negation, array concatenation, and explicit casts to
unqualified INTERVAL erase modifiers according to their existing signatures.
Array extraction preserves element modifiers. Equality and array predicates
compare the shared underlying interval identity, while the six temporal
EXTRACT declarations still select the unqualified interval input and return
unmodified NUMERIC.

The specification's well-formedness and concrete-type conversion rules
admit the new exact declarations. Existing independent cast, column,
parameter, conditional, array, operator, and EXTRACT judgments provide the
corresponding evidence; the checker constructs those derivations. General
parameter-translation preservation continues to retain exact metadata,
output types, and nullable flags.

Typed literals normalize directly to a cast from their original string.
For example, `INTERVAL '1' YEAR` must retain its target context when rendered
as `CAST('1' AS INTERVAL YEAR)`. Introducing an intermediate unqualified
interval conversion would change the value. Unknown string input, concrete
TEXT input, an existing interval value, and array input can undergo different
native value conversions even when the final static modifier is identical.
The native tests exercise those distinctions; the static certificate does
not prove the complete interval input parser, truncation, rounding, overflow
behavior, or successful evaluation of arbitrary strings.

Canonical type spelling places the qualifier before its precision and array
suffixes, such as `INTERVAL DAY TO SECOND(2)[]`. Default cast and typed-literal
labels remain `interval`. Both checked PostgreSQL rendering profiles prove
exact normalized AST roundtrips, while the SQLite profile rejects qualified
interval syntax. Original source dialect provenance is retained separately
from the PostgreSQL static contract.

The 1,701 focused checks cover every qualifier and every admitted fractional precision,
catalog/cast/parameter behavior for scalar and repeated array declarations,
pairwise common-type rules, NULLIF and arithmetic behavior, EXTRACT,
subscripts, invalid metadata, the unsupported precision boundary, and fuel.
Kernel examples construct a qualified interval cast derivation, demonstrate
array parameter modifier erasure, and select the existing EXTRACT overload.

Fifty authored queries and fifty unchanged authentic queries receive full
query certificates with exact ordered output metadata, identity and
PostgreSQL rendering certificates, and general validity transport. The
authentic population is fixed by source identity and expected qualifier:
49 PostgreSQL regression statements and one DuckDB statement, all
source-free, unaliased literals without parameters. Every statement uses
an explicit field qualifier; prior unrestricted INTERVAL(p) syntax is not
counted as a new source example. No schema or binding assumptions are invented.

The native harness checks 116 bound value/type observations, 116 independent
SQL NULL observations, 132 exact prepared-result descriptors, eight expected
runtime errors and fifty raw typmod integers covering scalar and array
declarations. Source SQL is never executed. The 468 focused renderer checks
include normalization, lexical parameter order, malformed declarations and
explicit SQLite exclusions.

These additions extend the bounded PostgreSQL SELECT contract. Native
descriptors, values, parameter behavior, and expected runtime errors
supplement the independent proofs; they do not constitute a general
execution-semantics proof or complete PostgreSQL validity.
