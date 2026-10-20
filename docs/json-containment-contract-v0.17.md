# JSONB containment: v0.17

`sqlean-basic-select-v0.17` adds PostgreSQL JSONB containment with `@>` and
`<@`. `Expr.containment left right containedBy` retains operand order;
`containedBy = false` denotes `@>` and `true` denotes `<@`. Rendering does
not reverse operands to normalize one spelling into the other.

The independent signature inventory admits two native declarations:
`JSONB @> JSONB → BOOLEAN`, implemented by `jsonb_contains`, and
`JSONB <@ JSONB → BOOLEAN`, implemented by `jsonb_contained`. Both functions
are strict and return scalar Boolean results. Their function names and
operator spellings are exposed beside `jsonContainmentSignature`.

At least one operand must have a known JSONB type. The other can be JSONB
or an unknown literal, including SQL NULL. An unknown string receives JSONB
context; a string that was explicitly cast to TEXT does not. JSON also
does not implicitly become JSONB. Two unknown operands are Invalid:
PostgreSQL's built-in operator environment includes other containment
families, so the expression is ambiguous. Resolving it against only a
single JSONB candidate would incorrectly erase that ambiguity.

Known array operands are Unsupported in this increment. PostgreSQL has
separate polymorphic array-containment declarations, with exact element
identity and element-comparison requirements. For example, equal integer
array types can use containment, integer and bigint arrays do not silently
widen to a common type, and JSON arrays can pass operator analysis but fail
when element equality is required during execution. This contract makes no
claim about those families. Range, multirange, geometric and text-search
containment also remain outside the admitted concrete type environment.

The result is Boolean with nullable equal to the disjunction of the two
operand flags. Non-NULL JSONB values produce non-NULL Boolean results on
successful evaluation. JSON null is a JSONB value, not SQL NULL:
`'null'::JSONB @> 'null'` returns true, while `NULL::JSONB @> 'null'`
returns SQL NULL. This differs from extraction's always-nullable result.
The PostgreSQL 16
[JSON operator documentation](https://www.postgresql.org/docs/16/functions-json.html)
and [containment description](https://www.postgresql.org/docs/16/datatype-json.html#JSON-CONTAINMENT)
describe the native structural containment behavior.

The certificate establishes static typing and conservative nullability.
It does not prove the general JSONB containment evaluation algorithm,
successful conversion of arbitrary strings, or successful execution.
A contextually typed malformed JSON string can fail during PostgreSQL
analysis when the input conversion is attempted; allocation and other
value-dependent failures are also outside the proof.

`ExprValid.containment` requires independent derivations for both
operands and the exact admitted signature. The finite checker constructs
this evidence. Missing or ambiguous closed scalar signatures are Invalid;
unmodeled array families and unsupported child expressions remain
Unsupported. Fuel exhaustion is Inconclusive. No parser success or
renderer success is substituted for a validity derivation.

Containment uses PostgreSQL's general-operator precedence and associates
left, sharing its level with concatenation, regex and JSON extraction.
Canonical parentheses preserve the parsed expression tree. In particular,
`a @> b || c` means `(a @> b) || c`; it is not silently regrouped as
`a @> (b || c)`. Default output labels are `?column?`.

Parameters retain their lexical order: all occurrences in the left
operand precede those in the right. General translation theorems preserve
the direction, selected signature, nullable result, and complete SELECT
validity. Both identity and numbered-parameter PostgreSQL renderers prove
exact AST roundtrips. The SQLite profile rejects this PostgreSQL operator
family rather than assigning it unrelated semantics.

Verification includes 241 focused Lean checks, the two exact native
catalog declarations, and direct kernel derivations for nonnullable and
nullable containment. The focused population covers scalar rejection,
unknown ambiguity, array boundaries, nullability, default labels,
compositions, parameter order and resource exhaustion. Fifty authored
synthetic queries receive full query certificates, exact output metadata,
both rendering certificates and general validity transport.

The authentic corpus contains fifty unchanged PostgreSQL regression
queries. A fixed list of forty-two source-free, parameter-free statements
receives full query certificates with genuinely empty environments and
exact Boolean, nonnullable output. The remaining eight table-dependent
statements receive rendering evidence only. The tests register both
populations before validation, check their actual AST shapes and metadata,
and reject missing, duplicate or unregistered identities. They neither
select a successful subset nor invent source table schemas.

Native catalog and finite type/value observations supplement these
proofs. JSON existence operators, JSONPath, other containment families,
arbitrary operator environments and the full PostgreSQL validity contract
remain separate work.

The native CLI checks 100 source/canonical value/type observations, 112 prepared
result descriptors, both native operator declarations and eight expected
conversion errors. It also requires 26 explicit failure/coverage boundaries
and 50 SQLite exclusions. Independent review compared 338 native/CLI overload
cases and 12 nested expressions, including 24 source/canonical value-and-NULL
observations. These are finite tests, separate from the general static and
rendering proofs.
