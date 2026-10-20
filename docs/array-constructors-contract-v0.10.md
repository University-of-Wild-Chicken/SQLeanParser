# ARRAY constructor validity: v0.10

`sqlean-basic-select-v0.10` adds `ARRAY[...]` expressions to the independent
SELECT validity contract. Constructors may contain ordinary expressions or
nested arrays. The parser normalizes shorthand such as `ARRAY[[1],[2]]` into
the same nested AST as `ARRAY[ARRAY[1],ARRAY[2]]`. The canonical renderer uses
the explicit spelling. ARRAY subqueries, indexing, slices and quantified
comparisons remain later increments.

A nonempty constructor uses the admitted PostgreSQL common-type rules for
its members. Examples include INTEGER plus REAL becoming REAL[], and INTEGER[]
plus BIGINT[] members producing a multidimensional value with concrete type
BIGINT[]. Runtime dimensions are still absent from type identity. Equal
element modifiers survive when all members have the same concrete type and
modifier; an unknown NULL member removes that modifier from the inferred
result. `ARRAY[NULL]` is a nonnull TEXT[] containing one NULL element.

Empty constructors require a direct array cast. `ARRAY[]::INTEGER[]`,
`ARRAY[[]]::INTEGER[]` and `ARRAY[[],[]]::INTEGER[]` are supported. An uncast
`ARRAY[]` has no inferred type and is Invalid. A sibling expression does not
retroactively supply a target to an empty child.

A direct array cast supplies its target recursively to raw nested constructor
nodes and explicitly coerces their elements. This is different from first
inferring an array type and then converting it. For example,
`ARRAY[TRUE,2]::INTEGER[]` succeeds because each element can be cast to INTEGER.
Conversely, a direct TIME[] cast of a constructor containing DATE and TIMESTAMP
elements is invalid because DATE cannot be cast directly to TIME. Wrapping
the constructor in COALESCE first can produce a TIMESTAMP[] expression which
can then be cast to TIME[].

The specification enforces that distinction with `OrdinaryCast`, excluding a
raw constructor with an array target from the generic cast rule.
`ExprValid.castArray` instead requires an independent `ArrayValid` derivation.
Its mutually inductive `ArrayElementsValid` rule passes context through raw
nested constructors while using ordinary expression validity for other nodes.
Context does not pass through arbitrary calls, conditionals or intervening
casts: `ARRAY[COALESCE(ARRAY[],ARRAY[1])]::INTEGER[]` still has an untyped empty
constructor and is Invalid. These rules follow PostgreSQL 16's
[constructor behavior](https://www.postgresql.org/docs/16/sql-expressions.html#SQL-SYNTAX-ARRAY-CONSTRUCTORS)
and its
[target-directed array transformation](https://github.com/postgres/postgres/blob/REL_16_STABLE/src/backend/parser/parse_expr.c).

Constructor results are nonnullable array objects, even when their members
are nullable. This is conditional on successful evaluation. Ragged nested
arrays and incompatible runtime subarray shapes can have valid static types
but fail during execution. Element conversion can also fail: a quoted JSON
null value is distinct from an SQL NULL array element, and converting the
former to an integer can raise an error. The certificate does not establish
rectangularity, successful value conversion or absence of runtime errors.

Default output labels are `array`, including explicit cast chains rooted at a
constructor. An explicit alias overrides that name. Parameter occurrences are
collected recursively from left to right. The outer statement retains the
single global numbered/anonymous notation check; nested constructors neither
restart nor reorder anonymous ordinals. The general parameter-translation
theorems preserve constructor types, scopes and ordered output metadata.

The checker constructs the new independent derivations directly. Exhaustion
remains Inconclusive. Unknown function signatures and unsupported nested query
forms remain Unsupported. The expanded coarse checker refuses constructor
inference rather than substituting an approximate element type. The identity
and PostgreSQL rendering profiles preserve the normalized constructor AST.
SQLite explicitly rejects array constructors.

Verification includes 50 synthetic complete-query certificates with exact
output metadata, identity/PostgreSQL rendering certificates and translation
preservation. Focused tests cover inferred types, element modifiers, nested
and empty constructors, direct-cast boundaries, runtime-only shape errors,
parameter order and exhausted budgets. Direct kernel proofs establish that
untyped empty arrays have no validity derivation, that an explicit target
permits an empty constructor, and that NULL elements do not imply a NULL
array object.

Fifty unchanged concrete source statements receive rendering evidence only.
Native PostgreSQL checks separately compare fixed values, type OIDs, exact
type modifiers, output labels and selected execution errors. Those finite
observations supplement the static contract; they do not prove execution
semantics for arbitrary queries or complete the full PostgreSQL contract.

The native suite records 112 source/rendered value-and-OID observations,
120 exact result descriptors and 14 expected execution errors. Six extra
character-type regressions distinguish unmodified `bpchar`/`bpchar[]`
results from `CHAR(n)` declarations. Result JSON uses `bpchar` for the
unmodified type: spelling it `CHAR` would incorrectly imply a length of one.
The declaration-shaped `ScalarType.dataType` helper is not a universal
roundtrip encoding of inferred result types.
