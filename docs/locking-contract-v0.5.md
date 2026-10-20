# Row locking and pagination order: v0.5

`sqlean-basic-select-v0.5` extends the independent source-free and single-base
table SELECT judgment with PostgreSQL's four row-lock strengths:
FOR UPDATE, FOR NO KEY UPDATE, FOR SHARE and FOR KEY SHARE.
Each clause retains its ordered OF targets and its blocking, NOWAIT or
SKIP LOCKED policy. Repeated targets and multiple clauses are retained.

The independent `LockingValid` judgment resolves explicit targets against the
visible base relation name. An alias replaces the original table name; output
aliases are not lock targets. Targetless source-free locking is accepted,
matching PostgreSQL's valid but ineffective lock clause in `SELECT 1 FOR UPDATE`.
The complete SELECT rules exclude locked DISTINCT, grouped, HAVING and
aggregate queries. The checker reports these incompatible shapes and locked
set-operation results as Invalid, while unsupported query structures retain
their separate Unsupported outcome.

`Query.offsetFirst` preserves OFFSET-before-LIMIT syntax. The full validity
judgment, executable parameter collector, independent renderer inspection and
printers all use that flag when ordering parameter occurrences. Consequently,
`SELECT ? OFFSET ? LIMIT ? FOR UPDATE` retains slots 1, 2 and 3 in source order.
Lock clauses themselves consume no parameter positions. The AST retains
locking metadata exactly during parameter translation.

The general preservation theorem now carries the locking derivation and
pagination order into the translated SELECT certificate. Total rendering,
exact AST equality, translation idempotence, byte-serialization laws and checked
parser roundtrips cover the added fields. The independent name-only scope
embedding explicitly proves that every embedded query has an empty locking
list, so it cannot silently erase a lock clause.

The lower executable tier checks lock targets across joins and rejects a
nullable outer-join side. A separate recursive scope traversal retains CTE
provenance and rejects explicit OF targets naming CTE bindings, including
inside nested queries. Nonrecursive CTE definitions see earlier siblings and
outer bindings, while recursive WITH exposes all its CTE names. Targetless locking does not propagate into CTE
definitions, while a lock written inside a definition is checked there.
Derived-source lock propagation is conservatively rejected by this tier.
The full independent SELECT tier still excludes joins, derived tables, CTEs,
sets, grouping and subqueries; their expanded syntax remains available.

This is static evidence, not a transaction-execution proof. It does not establish
privileges, lock acquisition, absence of blocking or deadlocks, concurrency
behavior, row identity across execution, or successful pagination evaluation.
The strength-combination and wait-policy effects described by PostgreSQL are
not formalized as a runtime transition system.

Verification includes 50 synthetic full SELECT certificates with fixed
catalog and parameter declarations, exact identity/PostgreSQL rendering
certificates, and translation preservation, plus 41 focused contract boundaries.
Native execution and parser corpus replay provide separate finite evidence.
No release-completeness or whole-PostgreSQL validity claim follows from this
increment.

Reference: PostgreSQL 16
[SELECT locking clauses](https://www.postgresql.org/docs/16/sql-select.html#SQL-FOR-UPDATE-SHARE).
