# Array subscripts and slices: v0.12

`sqlean-basic-select-v0.12` adds array element extraction and slicing to the
independent SELECT validity contract. A subscript group contains one or more
ordered dimensions. Each dimension is either an index expression or a slice
with independently optional lower and upper expressions.

The AST retains consecutive brackets in one group. For example, `a[1][2]`
performs one multidimensional extraction, whereas `(a[1])[2]` performs two
operations. They cannot be merged: the first operation in the latter form
already has the array's scalar element type. A colon anywhere in a group makes
its result an array. PostgreSQL interprets each nonslice dimension in such a
mixed group as a slice starting at one. Omitted endpoints use the array's own
bounds. These distinctions follow the documented
[array access rules](https://www.postgresql.org/docs/16/arrays.html#ARRAYS-ACCESSING).

The independent `ExprValid.subscript` constructor requires a concrete array
base, a nonempty group of at most six dimensions, and a `SubscriptsValid`
derivation for its bounds. All-index groups return the exact scalar element
type; groups containing a slice return the exact original array type.
Element modifiers survive both operations, including NUMERIC precision/scale,
character lengths and temporal precision.

Each present bound needs its own expression derivation and an admitted
assignment conversion to INTEGER. This conversion is deliberately separate
from ordinary implicit operator conversion: SMALLINT, INTEGER, BIGINT,
NUMERIC, REAL and DOUBLE PRECISION bounds are accepted. Unknown string and
NULL inputs can receive an INTEGER context, while concrete TEXT, VARCHAR,
CHAR, BOOL, temporal, JSONB and array bounds cannot. The fixed rule follows
PostgreSQL 16's
[array subscript transformation](https://github.com/postgres/postgres/blob/REL_16_STABLE/src/backend/utils/adt/arraysubs.c),
including its six-dimension implementation limit.

Both extraction and slicing currently report conservative nullable output.
An extraction may encounter a NULL member, missing position or incompatible
runtime dimension count even when its base and indices are nonnullable.
Slices can encounter NULL bases or endpoints. Empty or out-of-range slices
usually yield empty arrays instead. The contract does not infer shape,
cardinality or position refinements from array values.

Static conversion evidence does not establish successful value conversion.
Numeric bounds can round or exceed INTEGER range, and unknown string contents
can be rejected during PostgreSQL analysis. These value failures are separate
from the admitted assignment signature. No claim of successful execution
follows from a static certificate.

Empty hand-built groups are Invalid. Groups beyond PostgreSQL's six-dimension
limit receive Unsupported with the `subscript_dimensions` diagnosis.
Nonarray bases are Invalid except JSONB, whose valid PostgreSQL container
syntax requires a separate contract and is explicitly Unsupported here.
Unknown functions and uncovered subqueries retain Unsupported. Exhausted
checker fuel remains Inconclusive.

Parameter occurrences follow the base, then each dimension's lower and upper
bounds in lexical order. Omitted endpoints introduce no fabricated parameter
uses. The existing outer query check enforces global anonymous ordinals and
placeholder notation. The general translation theorem transports
`SubscriptsValid`, the complete expression derivation, output metadata and
whole-query validity.

The parser preserves the grammar's grouping boundary. Columns, parameters
and parenthesized expressions can be subscript bases; arbitrary constructors
or calls require parentheses. Sized type suffixes remain a separate deferred
syntax: `'{1,2}'::INTEGER[][1]` denotes a type declaration in PostgreSQL, while
`('{1,2}'::INTEGER[])[1]` extracts an element. The parser must not silently
reinterpret the former. The canonical renderer parenthesizes each group's
base, preserving nested operations and exact AST roundtrips. SQLite refuses
this PostgreSQL array syntax.

This increment also repairs inferred projection names. `outputLabel` follows
the covered cases of PostgreSQL's
[FigureColnameInternal](https://github.com/postgres/postgres/blob/REL_16_STABLE/src/backend/parser/parse_target.c):
columns, calls and constructors supply strong names; casts replace weak
names with the normalized built-in type name; CASE inherits a strong ELSE
name and otherwise supplies weak `case`; subscripts inherit their base's
name. Thus `NULL::INTEGER[]` and its extraction are named `int4`, an array
constructor's extraction is named `array`, and a cast or extraction of column
`a` remains `a`. Explicit aliases still override inferred names. This changes
previous fallback labels where the earlier contract used `?column?`.

Verification includes 50 synthetic complete-query certificates with exact
types/modifiers, conservative nullability, identity/PostgreSQL checked
rendering and translation preservation. The 190 focused Lean cases include
85 independently observed default-label cases, twenty scalar element types,
assignment conversions, grouping, omitted/NULL bounds, dimension limits,
parameter order and resource exhaustion. Direct kernel witnesses construct
both extraction and slicing derivations and show that an empty group cannot
have one.

Fifty unchanged concrete statements receive rendering evidence only, with
their source dialect and dependencies retained: 24 PostgreSQL and 26 DuckDB
statements. Native verification checks 100 source/rendered value-and-OID
observations, 270 exact result descriptors and 10 expected runtime errors.
The descriptor population includes 85 default-label regressions; two further
native FLOAT spelling probes remain explicitly rejected by the typed parser.
These label probes are separate from both 50-example populations. The native
suite also checks 20 type, syntax and profile boundaries. The 80 focused
renderer checks retain grouping and parameter identity.

Native observations supplement these static proofs. They do not establish
arbitrary execution equivalence, JSONB subscripting, subscripted assignment,
or full PostgreSQL validity.
