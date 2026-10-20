# Nonrecursive CTE validity, profile v0.29

`sqlean-basic-select-v0.29` extends the independent PostgreSQL SELECT contract to
ordinary nonrecursive `WITH` definitions whose SELECT bodies are already covered
by the profile. The expanded parser and checked renderer retain their broader
coverage. Recursive queries, set operations, aggregation, expression subqueries,
LATERAL correlation, materialization directives and data-modifying CTE bodies
require separate contract increments.

## Independent scope and output rules

The normative `CTEsValid`, `QueryValid` and `SourceValid` judgments are mutually
defined. `CTEEnv` is separate from the supplied catalog. Each definition is
checked against inherited definitions and earlier siblings, then inserts its
certified ordered output into the environment. Its own name and later siblings
are not newly visible inside its body: lookup can still find an inherited CTE or
a caller-declared base relation with that name.

Names must be unique within each local WITH list. A nested WITH can shadow an
inherited name. Nested non-LATERAL derived queries inherit the CTE environment
without acquiring access to sibling source columns. Unqualified relation lookup
prefers the nearest visible CTE; schema-qualified lookup bypasses CTEs and uses
the existing exact catalog metadata. There is no fabricated table, primary key,
uniqueness premise or search-path implementation.

CTE definition column aliases and reference alias lists rename an ordered prefix.
Unrenamed columns retain their names. Duplicate exposed labels are preserved;
an ambiguous column reference is rejected. Existing projection rules finalize
unknown NULL/string outputs as TEXT, retain exact supported type modifiers, and
carry conservative nullability into joins. CTE namespaces remain distinct from
base and derived namespaces, so aliases hide original names and schema paths
cannot accidentally address a WITH binding.

The public certificate still starts with an empty CTE environment and proves
`certificate.outputCatalog = catalog`. Its environment and parameter assumptions
are exactly the caller's original declarations.

## Parameter occurrences and proof transport

A definition contributes its lexical parameter occurrences once, even when it
is unused or referenced more than once. All definition occurrences precede the
enclosing SELECT's occurrences. References contribute no additional occurrences.
Nested definitions follow the same rule; the public `ParameterOrder` premise is
checked only once over the complete statement.

The total parameter translation retains every CTE name, alias list, environment,
output column and type. The three mutually recursive preservation theorems
transport `CTEsValid`, `QueryValid` and `SourceValid` while mapping only the
collected parameter occurrences. The public full-query preservation theorem
continues to require no parser or renderer success premise.

## Locking and diagnostics

Targetless outer row locking skips CTE references. It does not propagate into
their definitions, including when a CTE is null-extended by an outer join.
Explicit `OF` naming a CTE or its alias is Invalid. Definition-local locks are
checked independently; selected derived-source lock propagation remains
Unsupported. The existing ordered first-match `OF` resolution is unchanged.

PostgreSQL can avoid planning an unused SELECT CTE. A nullable-side base lock in
its body therefore cannot be reported as an unconditional native-invalid query.
The checker conservatively reports this body-level planning restriction as
Unsupported for both used and unused definitions. It retains the independent
nonnullable-lock premise and does not grant a certificate. Analysis errors such
as locking with DISTINCT, missing relations, missing OF targets and wrong
expression types remain Invalid even in unused definitions.

Successful static certificates do not prove execution, privileges, physical lock
acquisition, optimizer behavior, planning feasibility of every supported join,
runtime conversions or result-value equivalence. A source-free but unsupported
definition is still Unsupported; unused syntax is not silently skipped. Checker
resource exhaustion remains Inconclusive.

## Verification populations

`Tests.CTEContract` contains direct kernel derivations for a definition, its
reference, a complete query and translated validity, plus executable scope,
alias, parameter, locking, diagnostic and fuel checks.

The authored fixture contains 50 queries, including 30 closed queries and 20
queries against an explicitly declared two-table catalog. Every query requires
a full certificate with exact ordered labels, types and nullable flags, and
identity/PostgreSQL checked renderer certificates.

The authentic corpus contains 50 unchanged statements. A fixed registry of 13
closed statements independently declares 21 output positions: 15 INTEGER, two
TEXT and four BOOLEAN, all nonnullable. These receive complete certificates
under empty catalog/parameter assumptions. All 50 receive checked rendering;
the remaining 37 retain rendering-only assurance without invented source
metadata. The registry is chosen from source inspection, not checker success.

The native harness uses authored SQL and independently authored expectations;
authentic source SQL is not executed. PostgreSQL and SQLite observations remain
separate. SQLite rendering or execution does not establish PostgreSQL metadata
or cross-dialect row/value equivalence. The integration audit records the final
build, replay and trust results.

The fresh v0.29 CLI replay passed all 50 authored certificates, the fixed 13
source certificates and all 50 source roundtrips. PostgreSQL 16.15 passed 400
typed-row observations, 174 ordered descriptor positions and 56 separate
analysis/execution-stage observations; 30 CLI boundaries matched their declared
statuses. SQLite passed 288 row/label observations and 32 expected analysis
errors, with ten explicit input/render exclusions. These are finite observations
in addition to the kernel-checked rules and general preservation theorems.

## SQL92 ORDER BY correction

Integration research also identified an older overly permissive sorting rule.
The corrected independent `SortSyntax` classification treats bare INTEGER
tokens and chains of unary minus as ordinal positions. Their original token
must fit PostgreSQL's INT4 scanner category; a larger integer token remains a
noninteger sort constant even after negation. Bare NULL, Boolean, string,
decimal and exponent constants are rejected in the SQL92 sort position.

Unary plus, casts and compound expressions remain ordinary expressions.
Consequently `ORDER BY -(-2)` selects output position two, `ORDER BY -1` is
invalid, and `ORDER BY +2` is an ordinary expression. The translation proof
preserves this classification exactly. A separate focused suite registers 51
native sorting cases and checks parameter order for an ordinary sort expression.

The focused Lean suite passes 45 checks and the renderer suite passes 144.
The 447-job warning-free build, full Lean/scope suites and 1,045 Python tests
pass. Existing derived-source, USING/NATURAL, qualified-name and locking native
integrations also pass. Four earlier locking examples now require complete
CTE certificates instead of an Unsupported result. The qualified-name helper
pins the current SQLite SUBSTRING parse diagnostic without changing acceptance.

The broad renderer replay passes 1,237 SELECTs, 2,474 identity/PostgreSQL
renderings, 400 SQLite renderings and 800 bounded SQLite execution comparisons.
The raw PostgreSQL grammar replay passes 12,009 records across 125 outer
families and 2,395 reduction productions, plus 44 protocol checks.
The [industrial corpus](corpus/cte-v0.29/README.md) remains at 257 accepted
statements out of 276; its 19 syntax rejections are unchanged.

The ordering regression additionally passes 108 authored CLI classifications
and 216 source/canonical PostgreSQL PREPARE outcomes. Eight protocol tests
reject missing, reordered or incorrect native evidence.

The compiled trust audit checks 27,223 project declarations, including 15,142
theorems and 580 generated recursion helpers, and rejects all five deliberate
bypass witnesses. Its frozen input inventory SHA-256 is
`0d8103ae38cf166b404d92e9fd9f45a422926977b40dc07bbf9cacdc4b2de3da`,
based on commit `c11ba9349a45d3e306c7bea4c0b600c85bfe76f6`. The disclosed Lean
foundations are `propext`, `Classical.choice` and `Quot.sound`. No project-defined
axioms, proof placeholders or native proof-evaluation shortcuts are introduced.
This increment does not complete PostgreSQL contracts; the alpha release is held.

## Primary references

- [PostgreSQL 16 WITH queries](https://www.postgresql.org/docs/16/queries-with.html)
- [PostgreSQL 16 SELECT, WITH and locking clauses](https://www.postgresql.org/docs/16/sql-select.html)
- [SQLite WITH clause](https://www.sqlite.org/lang_with.html)
