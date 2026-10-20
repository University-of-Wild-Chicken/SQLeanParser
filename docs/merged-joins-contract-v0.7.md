# USING and NATURAL JOIN validity: v0.7

`sqlean-basic-select-v0.7` adds independent complete-query rules for INNER,
LEFT, RIGHT and FULL JOIN with USING or NATURAL matching. Base-table sources
can nest these forms with the previously supported CROSS and ON joins.
Existing scalar, projection, filtering, ordering, pagination and locking
rules continue to apply. No parser or rendering normalization is needed.

The scope now stores two distinct views:

- `qualified` retains each visible relation's original column order and types.
  A mixed INTEGER/BIGINT key therefore remains INTEGER in `left_table.key`
  and in `left_table.*`.
- `output` records the exposed joined row. Unqualified references and `*`
  use this view, where matching keys occur once with their common type.

Both views receive the appropriate outer-join null extension. They are
connected by the independent source derivation, without empty-name sentinels
or hidden-column ordering conventions. The public `Scope` API is now a
structure rather than a list; `Scope.empty`, `Scope.ofBindings`,
`Scope.append` and `Scope.columns` make the distinction explicit.

USING keys must be nonempty, distinct, and resolve exactly once in each child
output. Their merged columns appear first, in the supplied key order,
followed by the left and right nonkeys in their original order. NATURAL
matching derives keys from shared output names in left-column order.
Discovery does not deduplicate ambiguous names or consult hidden qualified
copies. No shared names is legal and gives an ON TRUE condition for that
join kind, retaining its outer-join behavior.

`JoinKeysValid` separately requires an equality overload on the original
operands and a common merged output type. These are different PostgreSQL
resolution operations. The closed scalar signature tables retain type
modifiers only when both inputs have the same exact type and modifiers;
otherwise the common type is unmodified. Qualified columns retain their
original modifiers.

Merged-key nullability is conservative. LEFT preserves the original left
key's flag, RIGHT preserves the right key's flag, and INNER/FULL use their
logical OR. FULL cannot use ordinary COALESCE's conjunction of the
pre-join flags: an unmatched nullable key from either side may still produce
a NULL merged key. Nonkey columns and qualified keys keep ordinary outer-join
nullability. Neither equality matching nor later filtering narrows these
flags.

The general validity-preservation theorem carries both scope views, exact
merged output metadata and source parameter occurrences through parameter
translation. USING/NATURAL add no parameter occurrences of their own;
parameters in child ON predicates remain in source order. Visible relation
identity and outer-side locking restrictions remain unchanged.

The full validity tier still excludes derived sources, source column
renaming, CTEs, grouping, subqueries and set operations. Existing expanded
syntax and lower assurance tiers remain available. Static derivability does
not establish execution success, planner support for every possible join,
result-row equivalence, privileges or concurrency behavior.

This static profile models PostgreSQL. SQLite can retain merged keys in the
left table's original positions and can expose merged values through qualified
wildcards on RIGHT/FULL joins even when an explicit qualified key is NULL.
SQLite rendering certificates establish structural roundtrips; separate
native SQLite expectations test its observed rows and labels. PostgreSQL
output metadata is not asserted for SQLite, and no cross-dialect row or value
equivalence is claimed.
Unaliased expressions also retain SQLite's source-dependent labels: quoting
the merged `tag` in a FULL USING projection changes its observed label from
`tag` to `"tag"`. The native harness keeps separate source and canonical label
expectations; structural rendering does not promise label equivalence there.

Verification includes 50 synthetic USING and 50 synthetic NATURAL queries
with complete independent certificates, fixed catalogs and parameter types,
exact ordered outputs, identity/PostgreSQL rendering evidence and translation
preservation. Seventy-two focused tests exercise namespace separation,
qualified wildcard order, nested merging, type modifiers, ambiguous and
missing keys, FULL JOIN nullability, locking and resource limits. Additional
kernel-checked examples construct complete merged-join derivations without
calling the checker. Unchanged external SQL receives rendering evidence
only; its source dialect is retained and no application catalog is invented.
The native suite checks 800 PostgreSQL source/rendered observations and 800
SQLite observations over empty, left-only, right-only and both-populated
tables, plus eight PostgreSQL merged/original type-modifier triples.

Reference: PostgreSQL 16
[table expressions](https://www.postgresql.org/docs/16/queries-table-expressions.html)
and the pinned
[join transformation implementation](https://github.com/postgres/postgres/blob/f0595c3d839debdb140903621c1b44a4f4d86256/src/backend/parser/parse_clause.c).
