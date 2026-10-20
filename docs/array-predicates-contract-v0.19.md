# Array containment and overlap: v0.19

`sqlean-basic-select-v0.19` adds independent validity for PostgreSQL array
containment (`@>`, `<@`) and overlap (`&&`). Containment uses the existing
`Expr.containment` AST, while overlap uses `Expr.overlap`. The separate
JSONB containment rule remains unchanged.

The normative `ArrayPredicateOperator` inventory records three strict
catalog declarations with arguments `anyarray, anyarray` and Boolean
result: `arraycontains`, `arraycontained`, and `arrayoverlap`. These
declarations require equal concrete element identities after modifiers
are erased. INTEGER[] and BIGINT[] are incompatible predicate inputs,
as are TEXT[] and VARCHAR[]. This differs from array concatenation's
`anycompatiblearray` common-type promotion.

Matching element types may have different modifiers. For example,
VARCHAR(5)[] and VARCHAR(9)[] select the same array predicate, as do
NUMERIC(8,2)[] and NUMERIC(9,3)[]. Declared array dimensions do not create
different element identities. A single unknown literal receives the
known operand's array type. Two unknown inputs remain ambiguous in the
closed PostgreSQL built-in operator environment and are Invalid.

The selected generic operator requires a separate admitted element
equality implementation. `arrayPredicateElementTypes` enumerates nineteen
supported unmodified scalar element types. VARCHAR uses the native TEXT
equality implementation; CHAR uses `bpchareq`. The nineteen mappings are
linked to the existing scalar equality signatures and independently
checked against the native catalog. They are not inferred from a coarse
string or numeric family.

JSON[] is intentionally Unsupported for these predicates. PostgreSQL can
analyze a generic anyarray operator on JSON[], but ordinary execution can
fail because JSON lacks the required element equality. Even empty arrays
can encounter that missing implementation, while SQL NULL inputs can
short-circuit without invoking it. The contract does not label this
generic-operator analysis success as native rejection, and it does not
depend on a particular NULL value to bypass missing equality. A mismatched
JSON[]/JSONB[] pair is instead Invalid because its element identities do
not agree. JSONB[] is supported.

All three predicates propagate outer SQL NULL strictly, so the result
nullable flag is the disjunction of the input flags. NULL elements do not
make the containing array SQL NULL and do not match another NULL element
in these native predicates. Duplicate elements, dimensions and lower
bounds do not change the static type rule. PostgreSQL's
[array operator documentation](https://www.postgresql.org/docs/16/functions-array.html)
describes containment as element membership and overlap as sharing an
element; these are distinct from array ordering and dimensional equality.

`ExprValid.arrayContainment` and `ExprValid.overlap` require independent
operand derivations and the exact selected array signature. Their result
is Boolean with strict outer-NULL propagation and all left operand
parameter uses before all right operand uses. The finite checker constructs
this evidence. Incompatible concrete types are Invalid, unavailable JSON
element equality and unsupported child expressions are Unsupported, and
fuel exhaustion is Inconclusive.

The certificate does not formalize the general native element-membership
evaluation algorithm or prove successful execution of arbitrary values.
Malformed array input strings, value conversion, unavailable runtime
resources and failures in evaluated child expressions remain separate
obligations. Runtime element comparisons use the fixed built-in environment;
custom equality operators, domains, ranges, geometric types and text-search
operator families remain outside this profile.

The operators share PostgreSQL's general-operator precedence and associate
left. Canonical rendering retains parentheses, containment direction and
operand order. Default output labels are `?column?`. Both checked
PostgreSQL rendering profiles prove exact normalized AST roundtrips, and
general parameter-translation preservation now covers both new validity
constructors. The SQLite profile rejects these PostgreSQL array operators.

The focused Lean suite contains 1,576 checks. It exercises all 1,200
twenty-type array-pair/operator combinations, matching-type modifier
erasure, unknown contexts, strict NULL flags, NULL elements, duplicate and
multidimensional values, explicit JSON[] coverage boundaries, parameter
order and fuel. Three generic declarations and nineteen element equality
mappings are linked to the normative inventories. Those mappings use
eighteen distinct native equality declarations because VARCHAR shares
TEXT equality. Direct kernel
examples construct overlap validity and demonstrate exact same-element,
mixed-element and missing-equality decisions.

Fifty authored containment queries and fifty authored overlap queries
receive full query certificates, exact ordered output metadata, identity
and PostgreSQL rendering certificates, and general validity transport.
Each factor also has fifty unchanged authentic source queries. A fixed
source-free population of six containment queries and five overlap queries
receives full certificates with empty environments: eight RisingWave
array-constructor statements have nonnullable Boolean outputs, while
three RUM statements with outer SQL NULL arrays have nullable Boolean
outputs. The remaining 89 table-dependent statements receive rendering
evidence only. No source schema or parameter type is invented. Tests
register every identity, check actual source ASTs and parameter absence,
and fail if a new source-free statement would silently fall into the
rendering-only population. Original source provenance and dialect labels
remain distinct from the PostgreSQL typing contract.

Native catalog, result-type, value, SQL-NULL and expected-error observations
supplement these proofs. Complete PostgreSQL validity and arbitrary
operator environments remain separate work.
