# Extended scalar contract v0.3

The frozen `sqlean-basic-select-v0.3` increment certifies source-free and
single-base-table SELECT queries using independent declarative rules. Its
certificate retains the exact original catalog, parameter declarations and AST,
and records ordered output names, concrete scalar types and conservative
nullability. Joins, grouping, aggregate queries, CTEs and subqueries remain
outside this full-query validity tier.

The scalar inventory is SMALLINT, INTEGER, BIGINT, NUMERIC, REAL, DOUBLE
PRECISION, TEXT, VARCHAR, CHAR, BOOLEAN, DATE, TIME, TIME WITH TIME ZONE,
TIMESTAMP, TIMESTAMP WITH TIME ZONE, INTERVAL, UUID, JSON, JSONB and BYTEA.
Representable type modifiers are retained. Bare CHAR declarations mean CHAR(1).
Negative NUMERIC scales and INTERVAL field qualifiers are not represented yet.

The normative tables admit explicit PostgreSQL 16 casts, numeric promotions,
selected temporal arithmetic, comparisons, and string/BYTEA LIKE signatures.
They do not infer compatibility merely from a broad numeric or text category.
JSON projection is supported, while JSON equality, DISTINCT and ordering are
rejected; corresponding JSONB operations are admitted. Casting JSONB to a
Boolean or numeric scalar yields a conservatively nullable result because a
JSON null can become SQL NULL.

Pagination is typed outside the local row scope. INTEGER-family widening and
NUMERIC/REAL/DOUBLE assignment conversion to PostgreSQL INT8 are explicit
rules. Successful evaluation, conversion range, and a nonnegative final bound
remain runtime obligations. The separate bounds certificate establishes only
these pagination rules when the query body is outside the basic fragment.
Literal interpretation, arithmetic overflow, cast input validity, collations
and database execution are not proved by a static validity certificate.

The checker returns Invalid, Unsupported or Inconclusive failures separately.
A successful certificate contains a kernel-checked derivation. General
parameter-translation preservation retains its output type, nullability and
labels; renderer certificates additionally check exact parser roundtrip.

At the freeze, the focused suite passed 214 checks, all 50 extended-type
synthetic queries received full certificates, and all 100 pagination corpus
cases passed their declared full-query or bounds-only checks. A temporary
PostgreSQL 16 matrix probe also matched 400 explicit-cast pairs, 400 equality
pairs and 36 numeric arithmetic pairs. That temporary probe was additional
development evidence, not a persisted CI artifact or universal execution proof.

The normative reference is PostgreSQL 16's
[cast catalog](https://github.com/postgres/postgres/blob/REL_16_STABLE/src/include/catalog/pg_cast.dat),
[operator catalog](https://github.com/postgres/postgres/blob/REL_16_STABLE/src/include/catalog/pg_operator.dat)
and [operator type-resolution rules](https://www.postgresql.org/docs/16/typeconv-oper.html).
