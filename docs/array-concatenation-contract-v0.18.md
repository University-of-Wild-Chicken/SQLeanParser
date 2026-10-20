# Array concatenation: v0.18

`sqlean-basic-select-v0.18` extends validity for the existing `Expr.concat`
AST to PostgreSQL array concatenation, append and prepend. The five scalar
concatenation families retain their existing signatures and NULL rules.
The new independent `ArrayConcatOperator` inventory has three declarations:
array/array calls `array_cat`, array/element calls `array_append`, and
element/array calls `array_prepend`. Their catalog types use
`anycompatiblearray` and `anycompatible`.

`arrayConcatSignature` records the selected family, concrete argument
instantiation and exact output type. Known element types use the existing
directional common-type rules, followed by erasure of modifiers. Thus
INTEGER[] concatenated with BIGINT[] produces BIGINT[], and INTEGER[]
appended with REAL produces REAL[]. This differs from array comparisons,
which require equal concrete element types in the current profile.

String common-type selection also retains direction: CHAR[] followed by
TEXT[] produces unmodified `bpchar[]`, whereas the reverse produces TEXT[].
VARCHAR followed by TEXT[] can produce VARCHAR[]. Even matching
NUMERIC(8,2)[], VARCHAR(5)[], CHAR(5)[] or TIME(3)[] input modifiers do not
survive the operator result. Input values retain conversions already
performed by their casts. The CLI distinguishes unmodified `bpchar[]`
metadata from the declaration `CHAR[]`, whose default modifier is one.

An unknown literal next to a known array receives that array type and
selects `array_cat`. Consequently, `ARRAY[1] || NULL` leaves the array
unchanged, while `ARRAY[1] || NULL::INTEGER` appends a NULL element.
`ARRAY[1] || '2'` selects array concatenation and can fail when PostgreSQL
tries to parse the string as an array; it does not select scalar append.
Two unknown operands continue to use the existing TEXT concatenation rule.
The PostgreSQL [array documentation](https://www.postgresql.org/docs/16/arrays.html#ARRAYS-MODIFYING)
describes this unknown-literal distinction.

These three families are non-strict. Array concatenation returns SQL NULL
only when both arrays are SQL NULL, so its conservative nullable flag is
the conjunction of the two operand flags. Append and prepend always
produce a non-NULL array on successful evaluation, including when the
array and the element are both SQL NULL: the result then contains one NULL
element. The array's nullability is separate from its elements' nullability.

Concatenation requires no equality or ordering operator for the elements.
JSON[] is therefore admitted for concatenation, append and prepend. Its
existing comparison and containment boundaries are unchanged. JSON null
can occur as a non-NULL JSON array element, independently of SQL NULL
elements.

`ExprValid.arrayConcat` requires independent operand derivations and the
selected array signature. It concludes the exact array result with the
family-specific nullable flag and left-then-right parameter occurrences.
The checker constructs that evidence and retains the existing scalar
rule as a separate derivation. Incompatible known element types are
Invalid; unsupported child expressions remain Unsupported. Exhausted fuel
is Inconclusive.

The certificate does not prove successful execution on every value.
Array concatenation permits compatible equal-dimensional arrays or arrays
whose dimensions differ by one. Extents and lower bounds must also meet
the native operation's requirements. Append and prepend require an empty
or one-dimensional array. Incompatible dimensions or bounds, malformed
array literals, allocation failures and other value-dependent errors
remain runtime or input-conversion obligations. Declared rank remains
syntax metadata rather than a distinct PostgreSQL array type.

No syntax or precedence change is needed. Both checked PostgreSQL
rendering profiles retain the `||` tree and operand order, and general
validity transport now includes the new independent derivation. Default
output labels remain `?column?`. The SQLite renderer still refuses the
explicit PostgreSQL array syntax; there is no cross-dialect array
evaluation claim.

Verification includes 1,342 focused Lean checks. A fixed native-reviewed
matrix registers all 64 compatible pairs among twenty scalar element
types. It exercises all 1,200 array/array, array/scalar and scalar/array
combinations, rejecting every unregistered pair. Eighty cases check unknown
array selection. Further checks cover the NULL truth tables, modifiers,
JSON elements, nested expressions, known runtime-error shapes, parameter
order and fuel. Direct kernel witnesses construct an appended array with
nullable inputs and prove exact signature examples.

Fifty synthetic queries receive full query certificates with exact
ordered output metadata, identity/PostgreSQL renderer certificates and
general parameter-translation preservation. All fifty unchanged authentic
queries also receive full certificates: eight PostgreSQL array regression
statements and forty-two RisingWave SQLLogicTest statements. Their actual
ASTs are source-free and parameter-free; the tests use empty environments
and a fixed identity-to-output map rather than inventing schemas or
selecting cases by checker success.

RisingWave provenance and dialect labels are retained. The certificates
describe these statements under the closed PostgreSQL profile; they do not
assert that RisingWave produces identical types or values. Native catalog,
prepared descriptors, values and expected failures supplement the proofs.
Array functions, further polymorphic families, arbitrary operator
environments and complete PostgreSQL validity remain separate work.
