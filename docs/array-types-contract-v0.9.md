# Array type SELECT validity: v0.9

`sqlean-basic-select-v0.9` adds built-in array declarations, exact catalog and
parameter bindings, and explicit casts to the independent SELECT contract.
Both `CAST(value AS INTEGER[])` and `value::INTEGER[]` are supported.
Unsized suffixes may repeat, including `NUMERIC(8,2)[][]`. Element types are
the previously supported PostgreSQL built-ins. The modifiers belong to the
scalar element type and receive the same well-formedness checks.

The syntax tree retains every declared `[]`. The concrete semantic type
normalizes these to one `ScalarType.array` around the exact scalar element.
Consequently, INTEGER[], BIGINT[] and NUMERIC[] remain distinct, but
INTEGER[] and INTEGER[][] have the same concrete type. This follows
PostgreSQL's treatment of declared dimensions; the contract does not impose a
runtime shape or length. `concreteType_array_rank` proves the normalization
of repeated suffixes, and the `arrayElement`/`asArray` lemmas establish that
normalizing twice has the same result. See PostgreSQL 16's
[array declarations](https://www.postgresql.org/docs/16/arrays.html#ARRAYS-DECLARATION).

Catalog projections and explicit casts preserve element modifiers.
Parameter occurrences use the unmodified type, including recursively removing
array element modifiers. The exact parameter declaration remains in the
certificate's environment. This corrects the previous scalar parameter rule:
PostgreSQL's analyzed parameters carry type OIDs rather than declaration
typmods. For example, a binding declared `NUMERIC(6,2)[]` produces a bare
`$1` of type NUMERIC[]; `CAST($1 AS NUMERIC(6,2)[])` restores the explicit
modifier. The same distinction applies to scalar numeric, character and
temporal parameters. Declaring a parameter does not itself enforce the
modifier on supplied values.

Array casts use the admitted scalar cast relation on their elements. This
permits INTEGER[] to NUMERIC(8,2)[] and TEXT[] to INTEGER[], while rejecting
BOOLEAN[] to BIGINT[] and INTEGER[] to JSONB[]. String-category conversion
also permits TEXT to an array and an array to TEXT. These are static cast
rules: malformed element text, overflow and invalid array input remain
execution errors outside the certificate. Generic typed-string syntax such
as `INTEGER[] '{1,2}'` is rejected; use an explicit cast.

Comparisons use a different rule from common-type selection. Array equality
and ordering require the same unmodified element type and a covered element
operator. INTEGER[] versus BIGINT[] therefore has no admitted comparison,
while COALESCE of those types can resolve to BIGINT[]. Conditional forms
reuse the explicit implicit-cast relation and retain modifiers only when the
existing common-type rule permits them. NULLIF keeps the left operand's
modifiers when no underlying type conversion is inserted. This separation
also applies to USING/NATURAL join key equality and merged output typing.
The relevant PostgreSQL references are
[array comparisons](https://www.postgresql.org/docs/16/functions-array.html)
and [common-type resolution](https://www.postgresql.org/docs/16/typeconv-union-case.html).

Nullability describes the entire SQL array value, not its elements. An array
containing NULL elements can be nonnullable. Covered array comparisons use
the operands' outer nullability; array NULL tests return a nonnullable Boolean.
Casting JSONB[] to INTEGER[] preserves SQL NULL elements without making a
nonnull array itself NULL. A JSON null value is different: PostgreSQL 16
rejects its conversion to INTEGER at execution. The existing conservative
nullability flag for scalar JSONB conversion does not apply to the outer array.

JSON[] is admitted as a projected or cast type. Comparisons, ordering,
DISTINCT, extrema, NULLIF, comparison-list predicates and join-key operations
requiring its element operator return Unsupported. PostgreSQL can resolve
the polymorphic array operator before discovering the missing JSON element
operator during execution. The contract neither certifies that gap nor labels
it an analysis-time PostgreSQL rejection.

The independent judgments remain separate from executable checking. Successful
checking constructs a derivation indexed by the exact profile, catalog,
parameter environment and AST. Global parameter order, nested derived-source
scope, output ordering and nullability continue to be preserved by the general
parameter-translation theorem. The identity and PostgreSQL render certificates
retain exact array suffix syntax; SQLite explicitly rejects these types.
The older expanded checker lacks exact array element identities and therefore
refuses comparison contexts where its coarse type families would lose them.

Verification includes 50 fixed synthetic complete-query certificates with
exact output metadata, both render certificates and translation preservation.
Focused cases cover every builtin element type at multiple declared ranks,
catalog/cast versus parameter modifiers, casts, conditional promotion,
operator availability and malformed metadata. Fifty unchanged external
statements receive rendering evidence only, without invented application
catalogs or parameter values. Native PostgreSQL observations are separate
finite evidence; they do not turn the static derivation into a proof of
successful execution.
The native suite includes 126 bound source/rendered value and type-OID
observations and 126 exact result descriptors obtained with PostgreSQL's
prepared-statement description. Descriptors independently check labels and
type modifiers, which `pg_typeof` and SQL function return declarations do not
retain. Two additional observations require the JSON-null conversion error
SQLSTATE `22023`. Fifty SQLite inputs use its own placeholder notation and
must fail specifically at the array-type boundary.

ARRAY constructors, ANY/SOME/ALL, indexing, slices, fixed-size declaration
syntax, array-specific functions, row values, custom types and domains are
later increments. Existing unsupported query forms retain their stated
boundaries. This increment does not complete the full PostgreSQL validity
contract or authorize a release.
