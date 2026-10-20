# Derived-source SELECT validity: v0.8

`sqlean-basic-select-v0.8` adds complete independent certificates for aliased,
non-LATERAL derived tables. A derived query can recursively contain another
derived source and can use every previously supported base-table join form.
Its certified output becomes the derived relation's exposed row and qualified
columns. Inner relation names do not escape through that boundary.

Derived outputs are used directly, rather than being converted into catalog
tables. Duplicate output labels are legal and stay ordered. Wildcards retain
them, while a name reference must resolve uniquely. An optional column alias
list renames a positional prefix; remaining labels retain their names.
Repeated alias names are permitted, empty names are rejected, and the alias
list cannot exceed the child output width. Exact concrete types, type
modifiers and nullability are unchanged by renaming.

The proof structure separates internal query derivations from complete
statement validity. Mutually inductive `QueryValid` and `SourceValid` collect
output metadata and parameter occurrences through arbitrary finite derived
nesting. `SelectValid.certified` checks the exact catalog and parameter
environment and applies `ParameterOrder` once to the complete statement.
Nested queries do not restart anonymous numbering. For example,
`SELECT ? FROM (SELECT ? AS inner_value) q` carries occurrences 1 and 2 in that
order, rather than requiring the inner occurrence to start at 1.

The checker follows this structure with bounded mutual recursion. A successful
public result contains the independent complete derivation; exhaustion remains
Inconclusive. Global mixed parameter styles or repeated anonymous ordinals are
Invalid even in a manually constructed AST. Repeated numbered parameters
remain valid. The general translation-preservation proof is mutual over
internal query and source derivations and preserves the complete occurrence
order, both scope views and all output metadata.

An independently certified lock inside a derived query remains supported.
An outer lock explicitly targeting a nonnullable base-table sibling also
remains supported. Propagating an outer lock into a selected derived relation,
including a targetless lock that would select it, is Unsupported. The
structural locking judgment distinguishes derived aliases from base relations;
the checker does not silently assume propagation is safe.

LATERAL and correlated source references, scalar/EXISTS/IN subqueries, CTEs,
grouping and set operations remain outside this full validity increment.
Base-table column renaming also remains a separate pending rule. Their
expanded syntax and applicable lower assurance tiers are retained. An internal
`QueryValid` witness is deliberately not a standalone complete-statement
certificate: it does not establish environment well-formedness or independent
anonymous numbering for an extracted child query.

This is PostgreSQL static typing and scope evidence. It does not prove
successful evaluation, planner support, result-row equivalence, lock
acquisition or execution privileges. SQLite has separate structural rendering
and native observations. In particular, derived-column alias lists are not
supported by the SQLite renderer, and duplicate derived labels may be renamed
by SQLite; PostgreSQL output metadata is not asserted across dialects.

Verification includes 50 synthetic complete-query certificates with fixed
catalogs and parameter declarations, exact ordered output metadata,
identity/PostgreSQL rendering certificates and translation preservation.
Fifty-five focused tests cover scope hiding, nesting, prefix and duplicate
renaming, nullable outputs, locking boundaries, global parameters and
exhaustion. Additional direct kernel witnesses construct derived-query
validity without invoking the checker. External corpus statements receive
rendering evidence only, with no invented application catalogs.
The native harness compares 400 PostgreSQL source/rendered positional type
and row observations across four table populations. Forty portable cases
also produce 320 SQLite row/label observations; the ten column-alias-list
cases must be explicitly rejected by SQLite. Synthetic duplicate-label
boundaries are checked by the independent rules rather than treated as
cross-dialect metadata equivalence.

Reference: PostgreSQL 16
[derived tables and aliases](https://www.postgresql.org/docs/16/queries-table-expressions.html)
and [SELECT locking clauses](https://www.postgresql.org/docs/16/sql-select.html#SQL-FOR-UPDATE-SHARE).
