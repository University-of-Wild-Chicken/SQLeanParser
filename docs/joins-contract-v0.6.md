# Base-table JOIN validity: v0.6

`sqlean-basic-select-v0.6` extends complete independent SELECT certificates to
base-table CROSS JOIN and INNER, LEFT, RIGHT and FULL JOIN with ON predicates.
Sources can be nested on either side. The existing exact catalog, parameter
environment, scalar signatures, projections, filtering, DISTINCT, ordering,
pagination and locking rules continue to apply.

`SourceValid` is an independent inductive judgment. Each leaf must resolve to
a declared base table; aliases replace original relation names. Visible leaf
names must be distinct across a join. Columns keep their original order,
concrete types and modifiers. Bare column references must resolve uniquely,
and qualified wildcards expand the chosen relation's columns in order.

An ON predicate is checked against its two child scopes. The current join
then adds nullability to its outer side: right for LEFT, left for RIGHT, and
both for FULL. Previously nullable child columns remain nullable. The checker
does not refine nullability from equality, WHERE predicates or known data.
Nested ON clauses cannot see unrelated sibling sources or SELECT aliases.

Parameter occurrence order follows the source text: SELECT items, left source,
right source, ON predicate, WHERE, ORDER BY, and pagination in its recorded
LIMIT/OFFSET order. The general translation-preservation theorem carries the
source derivation, exact output types and mapped parameter occurrences.
Structural relation metadata and locking eligibility are also preserved.

Explicit OF lock targets must resolve uniquely to nonnullable visible base
relations. A targetless lock selects every visible leaf and is therefore
rejected if an outer join can null-extend any of them. The existing
DISTINCT/grouping/aggregate/set-operation locking restrictions remain.

USING and NATURAL joins, derived sources, source column renaming, CTEs,
grouping and subqueries retain separate Unsupported outcomes in this full
validity profile. Their expanded syntax and applicable lower assurance tiers
remain available. Contextual Boolean conversion of a bare unknown string
literal, such as `ON 'true'` or `WHERE 'true'`, is also Unsupported.
An explicitly TEXT-typed predicate, such as `ON CAST('true' AS TEXT)`, is
Invalid. This distinction avoids claiming that PostgreSQL rejects its valid
unknown-literal coercion.

The certificate proves static derivability under this fixed model. It does
not prove result-row equivalence, successful expression evaluation, planner
support for every Boolean FULL JOIN condition, lock acquisition, concurrency
behavior, privileges or PostgreSQL-wide completeness. In particular, no
release-completeness claim follows from this increment.

Verification includes 50 synthetic complete-query certificates against an
explicit catalog and parameter environment, exact ordered output types and
nullability, identity/PostgreSQL rendering certificates and translation
preservation. Fifty focused tests cover nested scopes, ambiguous or hidden names,
outer-side locking, type modifiers, anonymous parameter order, malformed
handbuilt ASTs and resource exhaustion. A direct kernel-checked LEFT JOIN
derivation is constructed without invoking the checker. The unchanged
external corpus receives rendering evidence only; application schemas and
parameter types are not invented.

Reference: PostgreSQL 16
[table expressions](https://www.postgresql.org/docs/16/queries-table-expressions.html)
and [locking clauses](https://www.postgresql.org/docs/16/sql-select.html#SQL-FOR-UPDATE-SHARE).
