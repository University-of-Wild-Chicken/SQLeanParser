# Scalar functions and conditional expressions: v0.4

`sqlean-basic-select-v0.4` extends the independent basic SELECT contract with
ordinary positional function calls, searched and simple CASE, COALESCE,
NULLIF, GREATEST and LEAST. The AST retains qualified function names, ordered
arguments, optional CASE operands and ELSE clauses, and ordered WHEN/THEN
pairs. Parameter occurrences follow that exact source order.

The complete-function validity environment is deliberately closed. It contains
44 built-in names: 40 names with 78 explicit scalar overloads and four
variadic-any rules for CONCAT, CONCAT_WS, NUM_NULLS and NUM_NONNULLS.
[`functionNames` and `functionCatalog`](../SQLean/SelectContract/ScalarSignatures.lean)
are the normative inventory. Both unqualified built-in names and explicit
`pg_catalog` qualification are supported. User-defined routines, search-path
overrides, additional overloads and unlisted built-ins are outside this
environment. Their syntax can be parsed and rendered, but their independent
validity outcome is Unsupported. An admitted built-in with invalid arity,
incompatible inputs or ambiguous overload selection is Invalid.

The declarative judgments require typed arguments and an explicit signature.
The shared normative resolution tables inspect scalar inputs rather than
recursively inferring expressions. They distinguish unknown string constants
and NULL from declared TEXT columns and parameters. Implicit conversion,
explicit casting and numeric operator promotion remain separate rules.
The executable checker constructs these independent derivations; its resource
limit can produce Inconclusive but is absent from the specification.

CASE checks Boolean searched conditions or an equality signature for each
simple-CASE comparison. PostgreSQL coerces an unknown simple-CASE operand to
TEXT before comparing it. ELSE is the first input to CASE result-type
selection. COALESCE, CASE, GREATEST and LEAST use directional common-type
selection; INTEGER with REAL therefore yields REAL, unlike some arithmetic
operator overloads. Matching exact type modifiers are retained, while unknown
or differently modified inputs discard the modifiers.

NULLIF uses the first input type of its resolved equality operator, which can
promote the original left operand. Its original modifiers survive when that
operand's nominal type does not change. NULLIF is conservatively nullable.
COALESCE, GREATEST and LEAST can be non-null when at least one argument is
non-null; CASE combines the possible branch nullabilities and treats a missing
ELSE as NULL. Function signatures use explicit strictness/nullability rules.
JSON has no admitted equality or ordering operator; JSONB does.

These are static guarantees. Successful evaluation, valid literal conversion,
overflow, function-specific input restrictions, collation behavior, temporal
settings, nondeterministic values and execution equivalence remain outside the
proof. Temporal and random functions are admitted only for their static
signatures. Full-query scope is still source-free or one base table; aggregates,
joins, grouping, CTEs and subqueries retain lower assurance tiers.

The total printers, exact AST equality and parameter translation include every
new constructor. General proofs retain translation idempotence, PostgreSQL and
SQLite serialization laws, and preservation of the independent SELECT
derivation. Checked PostgreSQL/identity rendering establishes exact parser
roundtrip and canonical stability. The SQLite checked boundary currently
refuses generic calls and GREATEST/LEAST, and requires at least two COALESCE
arguments; it supports the representable CASE and NULLIF forms recursively.

The expanded AST parser now rejects unsupported unquoted PostgreSQL session
value keywords, ISNULL/NOTNULL predicates and ONLY relation modifiers instead
of silently reinterpreting them as identifiers or aliases. Quoted identifiers
remain available. These constructs can be recognized by the separate complete
PostgreSQL grammar interface without implying an expanded AST or static
validity certificate.

Verification includes 50 function and 50 conditional synthetic full-query
certificates, exact identity/PostgreSQL rendering certificates and translation
preservation, plus 54 focused boundaries and kernel-checked closed derivations.
The 78-entry native catalog fixture must exactly match the normative Lean
inventory; the PostgreSQL 16 runner independently checks the actual server
catalog. Native value/type checks are finite execution evidence, distinct from
the general structural theorems.

Normative references:
[function type resolution](https://www.postgresql.org/docs/16/typeconv-func.html),
[conditional expressions](https://www.postgresql.org/docs/16/functions-conditional.html),
[common-type selection](https://www.postgresql.org/docs/16/typeconv-union-case.html),
and the PostgreSQL 16
[function catalog](https://github.com/postgres/postgres/blob/REL_16_STABLE/src/include/catalog/pg_proc.dat).
