# Temporal EXTRACT: v0.20

`sqlean-basic-select-v0.20` adds independent validity for PostgreSQL
`EXTRACT(field FROM expression)`. `Advanced.Expr.extract` stores the decoded
field string and the argument expression separately. The field is syntax,
not a parameter-bearing expression. Canonical rendering quotes that string,
preserving its decoded contents, while only the argument contributes
parameter occurrences.

The normative `extractCatalog` contains the six PostgreSQL 16 declarations
with a TEXT field and one DATE, TIME, TIME WITH TIME ZONE, TIMESTAMP,
TIMESTAMP WITH TIME ZONE, or INTERVAL argument. Each returns unmodified
NUMERIC. Exact argument identities win over available temporal implicit
casts, and argument modifiers do not select different declarations. The
finite `extractSignature` resolver records both declared input types and
the result type. An untyped string or NULL argument remains ambiguous
between temporal categories; concrete TEXT and non-temporal scalar or
array arguments have no admitted overload and are Invalid. SQL EXTRACT
is distinct from the ordinary `date_part` function, whose result type is
DOUBLE PRECISION.

Nullability is conservative and depends on the temporal input family.
DATE and both timestamp families always produce a nullable result type,
even when the input is declared NOT NULL. These types admit infinity,
and successful extraction of some fields from an infinite value returns
SQL NULL. TIME, TIME WITH TIME ZONE, and INTERVAL preserve the operand's
nullable flag in PostgreSQL 16. The rule does not attempt to prove that
an arbitrary expression is finite or refine flags for individual field
names and aliases. The
[PostgreSQL 16 temporal documentation](https://www.postgresql.org/docs/16/functions-datetime.html#FUNCTIONS-DATETIME-EXTRACT)
describes the numeric result and infinity behavior; the pinned native
[date/time implementation](https://github.com/postgres/postgres/blob/f0595c3d839debdb140903621c1b44a4f4d86256/src/backend/utils/adt/date.c)
and
[timestamp/interval implementation](https://github.com/postgres/postgres/blob/f0595c3d839debdb140903621c1b44a4f4d86256/src/backend/utils/adt/timestamp.c)
provide the corresponding built-in behavior.

Field recognition and field/type compatibility are runtime obligations.
For example, `EXTRACT(hour FROM DATE '2024-01-01')` selects the DATE
declaration during analysis but fails when evaluated. Unknown or empty
field names likewise analyze; a NULL temporal argument can short-circuit
without a field error. Consequently, a static certificate is allowed for
arbitrary decoded field strings, including such runtime-error cases.
It does not assert successful execution of arbitrary values. Temporal
input conversion, overflow, evaluated child-expression errors, time-zone
settings, and resource availability are also separate from this static
contract. The TIMESTAMPTZ declaration depends on the session time zone;
the implementation does not treat its values as immutable across settings.

`ExprValid.extract` requires an independent argument derivation and the
selected declaration. It retains exactly the argument's parameter-use
list and gives the selected NUMERIC output its conservative nullable flag.
The checker constructs that evidence; unsupported child expressions remain
Unsupported and exhausted fuel remains Inconclusive. Default output labels
use PostgreSQL's strong `extract` name, which is retained by enclosing casts
and inherited through a CASE ELSE expression.

Both checked PostgreSQL rendering profiles retain exact normalized AST
roundtrips. General parameter translation preserves the argument,
decoded field, selected type, nullability, and independent validity.
The SQLite rendering profile explicitly rejects this PostgreSQL syntax.
There is no cross-dialect execution-equivalence claim.

The focused suite contains 232 checks and links all six fixture declarations
to the normative catalog and selected signatures. It checks scalar and array input
boundaries, argument modifiers, nullability, arbitrary field strings,
infinity, runtime-only errors, inherited labels, argument parameter order,
unknown-input ambiguity, unsupported children, and fuel exhaustion.
Direct kernel examples construct an EXTRACT validity derivation and
demonstrate exact selection and conservative nullability.

Fifty authored queries and fifty unchanged authentic PostgreSQL queries
receive full query certificates, exact output metadata, identity and
PostgreSQL rendering certificates, and general validity transport. The
authentic population is registered by fixed source identities: 22 DATE,
6 TIME, 9 TIMETZ, 9 INTERVAL, 2 TIMESTAMP, and 2 TIMESTAMPTZ queries. Each
is checked to remain a source-free temporal-literal expression with no
parameter uses, so no schema or binding assumptions are invented.
Failed cases cannot silently move to a weaker assurance tier.

Native declaration, value, descriptor, NULL, and expected-error checks
supplement these proofs. The independent specification remains a bounded
PostgreSQL SELECT contract, not a proof of arbitrary PostgreSQL evaluation
or a complete contract for the entire grammar.
