# JSONB existence: v0.24

`sqlean-basic-select-v0.24` adds PostgreSQL JSONB existence operators `?`,
`?|`, and `?&`. `JsonExistenceOp.key/any/all` and
`Expr.jsonExistence op arg keys` preserve the spelling and lexical operand
order. They do not rewrite an existence predicate into containment or
extraction.

The independent inventory contains three exact native declarations:
`JSONB ? TEXT → BOOLEAN` (`jsonb_exists`),
`JSONB ?| TEXT[] → BOOLEAN` (`jsonb_exists_any`), and
`JSONB ?& TEXT[] → BOOLEAN` (`jsonb_exists_all`). Each function is strict,
immutable, binary, and non-set-returning in PostgreSQL 16. The signature
fixture is checked against the Lean inventory and separately against the
native server's catalog.

Unknown string and NULL literals receive the selected declaration's type
context. Known JSON and TEXT subjects do not implicitly become JSONB.
Known CHAR and VARCHAR keys coerce to TEXT; their array forms coerce
itemwise to TEXT[]. This conversion removes CHAR padding. Numeric and
BYTEA keys, non-string key arrays, and concrete TEXT in an array-key
position are Invalid within the admitted concrete type environment.
Array dimensions and declared bounds are not separate element type
identities.

Two unknown operands require a deliberate distinction. `?` and `?&` have
unique binary built-in declarations and resolve their unknown inputs.
`?|` also has the geometric `POINT ?| POINT` declaration, so two unknown
operands are ambiguous. The normative resolver explicitly retains that
ambiguity instead of selecting a singleton JSONB candidate incorrectly.
A known JSONB subject or a known admissible string-array right operand
provides enough context for the JSONB `?|` declaration. Geometric types,
extension-provided overloads, arbitrary operator search paths, and custom
operators remain outside the fixed profile.

The result is Boolean with nullable equal to the OR of the two outer
operand flags. Non-NULL arguments return a non-NULL Boolean on successful
evaluation. NULL key-array members are skipped, rather than introducing
nullable Boolean results. Empty or all-NULL key arrays produce false for
`?|` and true for `?&` when the subject is non-NULL. An outer SQL NULL
still produces NULL even with empty keys. JSON null is a non-NULL JSONB
value. Top-level keys and string array members are considered; nested
keys and numeric array members are not recursively converted into names.
A root JSON string can itself match a key. These native behaviors are
described by the [PostgreSQL JSON operator documentation](https://www.postgresql.org/docs/16/functions-json.html)
and the [pinned existence implementation](https://github.com/postgres/postgres/blob/f0595c3d839debdb140903621c1b44a4f4d86256/src/backend/utils/adt/jsonb_op.c).

The static contract proves the selected types and conservative nullability,
not the JSONB search algorithm or successful execution. An unknown string
that is assigned JSONB or TEXT[] context can fail input conversion during
analysis or execution. Memory, encoding, and other value-dependent failures
remain outside the certificate. Extraction's always-nullable output rule
is intentionally separate from existence's strict outer-NULL rule.

`ExprValid.jsonExistence` requires independent operand derivations and
an exact normative signature. The fuel-bounded checker constructs that
evidence; fuel exhaustion is Inconclusive. Unsupported child syntax or
types remain Unsupported. No parser or renderer acceptance is used as
static validity evidence. General parameter translation preserves the
operator, selected declaration, output metadata, and left-then-right
occurrence order through the full query derivation.

All three spellings use PostgreSQL's generic-operator precedence and
associate left with concatenation, regex, and JSON extraction. Thus
`j ? 'a' || 'b'` groups as `(j ? 'a') || 'b'`; a caller wanting a concatenated
key must group the right operand. Default output labels are `?column?`.
The typed parser distinguishes the existence operator from anonymous
parameter occurrences by syntactic role. The identity renderer preserves
anonymous parameters; the PostgreSQL renderer translates only actual
parameter nodes and proves an exact AST roundtrip. SQLite remains an
explicit unsupported rendering profile for these PostgreSQL operators.

Question-containing operator runs retain native maximal token boundaries
until the parser determines their role. The existing anonymous-template
extension admits compact forms such as `1=?`, `?+?`, `?||?` and
`CAST(? AS JSONB)??`; the last form has two bindings separated by an
existence operator. This is explicitly template syntax, not native PostgreSQL
lexing equivalence. Unsupported infix runs such as `?-`, `?!`, `?||` and
`?&&` remain whole. Parser alternatives restore both tokens and binding
counters; nullable parameter declaration suffixes do not consume bindings.
The separate Python execution adapter observes exact binding spans, with
independently authored replacement expectations. It is a bounded test
observer, not another SQL validator or a universal lexer proof.

The 2,419 focused checks include a 2,352-case closed type matrix registered independently
of the signature function, direct kernel derivations, all three exact
native declarations, NULLability, unknown ambiguity, coercion, composition,
labels, resource exhaustion, and lexical placeholder order. Fifty authored
queries receive full certificates and exact ordered output checks, together
with identity/PostgreSQL rendering evidence and validity transport.

Authentic source eligibility is registered before checking. Forty-four
source-free literal queries from PostgreSQL, CockroachDB, and Materialize
receive full certificates with genuinely empty catalogs and parameter
environments. They have fifty ordered Boolean output positions, including
six duplicate-label pairs and two nullable outputs. Five PostgreSQL
table-dependent queries and one River application query retain only
syntax and rendering evidence. River's actual `$1` occurrence is preserved
without inventing a parameter or table environment. All fifty sources
receive exact rendering certificates. Missing, duplicate, changed, or
unregistered source identities fail the corpus checks. Native finite observations
supplement these guarantees; they do not establish universal PostgreSQL
evaluation equivalence or completion of the full PostgreSQL validity
contract.

The native harness checks 100 value/type observations, 100 SQL NULL
observations, 120 exact result descriptors, ten expected runtime errors,
the three JSONB declarations and competing POINT declaration, and 32
analysis outcomes. It executes only authored statements. SQLite checks
register 25 explicit existence-operator exclusions and 25 earlier input
boundaries for extraction, ARRAY constructors or PostgreSQL array types.
The [industrial replay](corpus/json-existence-v0.24/README.md) accepts 249
of the original 276 statements; these syntax observations do not invent
application catalogs or full static certificates.
