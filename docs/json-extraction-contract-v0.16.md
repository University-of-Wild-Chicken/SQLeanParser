# JSON extraction: v0.16

`sqlean-basic-select-v0.16` adds PostgreSQL JSON and JSONB extraction with
`->`, `->>`, `#>` and `#>>`. The AST retains the exact spelling through
`JsonAccessOp.field`, `fieldText`, `path` and `pathText`, used by
`Expr.jsonAccess op arg key`. A field or path expression is not rewritten
into a function, a string cast, or a different extraction operator.

The normative catalog has twelve declarations. Each JSON family supports
INTEGER and TEXT keys for `->` and `->>`, and a TEXT[] path for `#>` and
`#>>`. The single-arrow and single-chevron path forms retain the input's
JSON or JSONB type. The double forms produce TEXT. These result types have
no modifiers. The declaration and native function identities are recorded
in `jsonAccessCatalog` and `jsonAccessFunctionName`.

`jsonAccessSignature` applies the existing finite overload resolver to
that exact operator's catalog. SMALLINT keys widen implicitly to INTEGER;
INTEGER keys select the same declaration. BIGINT, NUMERIC, REAL and DOUBLE
PRECISION do not implicitly narrow to INTEGER. String-family keys coerce
to TEXT, including removal of CHAR padding. No scalar family is collapsed
into a coarse numeric or string category when selecting an index.

An unknown arrow key receives TEXT context. Thus
`'[10,20]'::JSONB -> '1'` requests the object key `1`, whereas
`'[10,20]'::JSONB -> 1` requests array element one. An unknown JSON argument,
including a bare JSON-shaped string or SQL NULL, is ambiguous between the
JSON and JSONB declarations and is Invalid in the closed built-in operator
environment. An explicit cast or a declared JSON/JSONB binding resolves
that ambiguity.

Path operators accept TEXT[] and implicit elementwise conversions from
VARCHAR[] and CHAR[]. INTEGER[] and a concrete scalar TEXT value are
Invalid path operands. An unknown string receives TEXT[] context instead:
its array syntax still has to parse successfully in PostgreSQL. Declared
array rank is not a separate type identity. Native observations cover
multidimensional paths traversed in storage order and paths whose array
lower bound is not one.

Every extraction rule reports a conservatively nullable result, including
when both operands are non-NULL. A missing field, out-of-range index,
incompatible JSON structure, SQL NULL input, or NULL path element can
produce SQL NULL. PostgreSQL's
[JSON operator documentation](https://www.postgresql.org/docs/16/functions-json.html)
specifies the extraction signatures and missing-structure behavior.

JSON null remains distinct from SQL NULL. For example,
`'[null]'::JSONB -> 0` returns a non-NULL JSONB value containing JSON null,
while `->> 0` returns SQL NULL. Extracting an absent element also returns
SQL NULL. The same distinction applies to `#>` versus `#>>`, including
an empty path selecting a JSON null value. Native observations therefore
check `value IS NULL` separately from serialized JSON values; serialization
alone would hide this distinction.

The independent `ExprValid.jsonAccess` constructor requires both operand
derivations and the selected signature. It returns the signature's exact
result type with nullable=true. The checker constructs that evidence.
Malformed input strings, invalid array literal contents, allocation
failure and other value-dependent failures remain outside the certificate.
In particular, a statically admissible unknown path string can fail during
PostgreSQL analysis when its TEXT[] conversion is attempted. The rule does
not prove successful execution or general JSON evaluation semantics.

Extraction has PostgreSQL's general-operator precedence and associates
left, like concatenation and regex operators. Nested extraction and
interleaved concatenation preserve their tree structure. Canonical
rendering parenthesizes operands, retains the exact operator, and proves
the normalized AST roundtrip. The default output label is `?column?`;
an explicit alias overrides it.

Parameter occurrences preserve the complete JSON argument before the
complete key or path expression. Global anonymous numbering and notation
checks still occur once at the outer query boundary. The general
translation theorems preserve the selected declaration, nullable output
type and full SELECT validity. Existing JSON comparison restrictions also
remain: JSONB results can use their admitted equality/order operations,
while JSON results do not acquire an equality operator through extraction.

The SQLite profile rejects these PostgreSQL extraction forms. Although
SQLite also has JSON operators, this increment supplies no shared typing
or evaluation contract for them. Unsupported child expressions, such as
scalar subqueries or external functions, retain their existing coverage
status. Unavailable or ambiguous extraction signatures are Invalid, while
exhausted checker fuel is Inconclusive.

Verification includes 367 focused Lean checks and twelve exact catalog
declarations. The focused population covers known and unknown operands,
all admitted and rejected key families, implicit array-path conversions,
nullable parameters, nested operators, default labels, comparison
boundaries, lexical parameter order and resource exhaustion. Direct kernel
examples construct a nullable JSONB extraction and demonstrate unknown-key
selection and ambiguous-input rejection without calling the checker.

Fifty authored synthetic queries receive full query certificates with
exact output metadata, identity/PostgreSQL rendering certificates and
general validity transport. All fifty unchanged concrete PostgreSQL
regression queries also receive those certificates: 25 come from
`json.sql` and 25 from `jsonb.sql`. This entire registered population is
source-free and parameter-free, so its environment is actually empty.
The test requires every registered identity to succeed and checks its
explicit expected output type; it does not choose a successful subset or
invent application schemas.

The concrete extraction metadata remains unchanged provenance data.
Independent Lean tests add validity evidence for these particular
source-free statements. Native catalog, result-type, value and SQL-NULL
observations supplement that evidence. They do not complete JSON existence,
containment, JSONPath, arbitrary operator environments, or the full
PostgreSQL validity contract.

The native CLI checks 100 value/type observations, 100 separate `IS NULL`
observations, 118 prepared result descriptors, all twelve native operator
signatures, and ten expected execution errors. Fifty explicit SQLite exclusions
and 26 failure boundaries supplement the 367 focused Lean checks and 154
rendering checks. JSON null is the non-NULL text observation `null` when retained
as JSON; SQL NULL is captured separately, never decoded through a JSON-only
result wrapper. These finite observations supplement the static contracts.
