# Explicit COLLATE and collation provenance, profile v0.32

This increment extends the independent SELECT contract with explicit `COLLATE`
expressions and collation metadata. It retains the broader PostgreSQL grammar,
expanded typed syntax, and existing SQLite rendering domain. Release
`0.0.1-alpha` remains held for full PostgreSQL contracts.

## Catalog assumptions and identity

Collation identity is separate from scalar type, SQL spelling, and locale
behavior. The default snapshot contains distinct database-default, C, and
POSIX objects. C and POSIX remain different identities even where their ordering
behavior agrees. Custom identities are opaque caller-supplied tokens.

A profile carries an immutable collation snapshot. Each entry specifies its
identity, schema, exact name, encoding eligibility, determinism and declared
unqualified visibility. Lookup prefers an entry for the current encoding over
an encoding-independent entry. Unqualified visibility is supplied by the
caller; the checker does not discover `search_path` or installed locales.
The snapshot must be well formed, including unique identities and unambiguous
names within each encoding category.

Schema JSON accepts an optional `collations` object and optional
`columnCollations` sidecars on tables:

```json
{
  "tables": [{
    "name": "words",
    "schema": "public",
    "exposeUnqualified": true,
    "columns": [{"name": "value", "type": "text", "nullable": false}],
    "columnCollations": [{"column": "value", "collation": "C"}]
  }]
}
```

Omitting `collations` asserts the documented built-in UTF8 snapshot. Omitting
a field sidecar asserts that field's native type-default collation; omission
does not mean the catalog metadata is unknown. NAME and NAME arrays have C as
their native type-default collation. TEXT, VARCHAR, CHAR and their arrays use
the database-default identity. Noncollatable types have no native type-default
collation. An analyzed expression can nevertheless retain an identity through
PostgreSQL's unknown-wrapper set coercion behavior; that identity remains
distinct from its result type.
Parameter declarations likewise use their native type-default collation.

Provider, locale, ICU rules, and collation versions are evidence about a native
installation. They are not an implementation of locale evaluation in Lean.
The static contract is conditional on the caller's catalog snapshot being
accurate.

## Expression and query boundaries

Scalar type and nullability derivations remain distinct from collation
derivations. The collation rules retain no identity, implicit identity, explicit
identity, and conflicting implicit identities as separate states. Different
explicit identities conflict during analysis. Explicit identity overrides an
implicit conflict; a nondefault implicit identity dominates the database
default.

Input collation and result collation are different. A comparison can consume
collatable inputs while returning noncollatable BOOL. A cast can preserve
provenance when its result remains collatable or discard it when converting to
a noncollatable type. Unknown literal provenance survives `COLLATE` until its
surrounding coercion resolves it.

CASE combines its result arms independently of its conditions. Pairwise
comparisons, normalized function arguments, joins, set operations and recursive
outputs each retain their own premises. A blanket merge of every expression
child would not express PostgreSQL's rules.
For IN lists, eligible expressions without input-column references can share
an array comparison context; other members retain pairwise contexts. Failure
to find a common array element type falls back to pairwise comparisons.

A projected column stores an optional identity. On entry into an enclosing
query, an identity becomes implicit, and an indeterminate stored column enters
with no identity. Explicit strength and the original conflict explanation do
not cross a derived-table, CTE or set-result boundary.

Recursive CTEs compare the complete anchor and complete UNION result's stored
collations as well as scalar types and modifiers. This replaces v0.31's
sufficient uniform-default restriction with explicit provenance.

Ordering also affects unknown-input resolution before a containing set
operation selects its common types. Unknown literal targets retain their
payload and ordered COLLATE identities. This recognizes qualified and
unqualified names for the same collation object. Sort entries are processed
sequentially: names and ordinals reuse their target, while an expression can
match the next identical target that has not yet been resolved. Resolving only
some duplicate targets can make a later output-name reference ambiguous.

The CLI keeps `outputColumns` unchanged and adds `outputCollations`, an ordered
array parallel to it. Values are `"default"`, `"C"`, `"POSIX"`, a
`"custom:<token>"` string, or JSON `null`.

Static derivation does not promise successful evaluation. Some conflicting
implicit collation expressions can be prepared but fail when evaluated;
registering an indeterminate output as a view can also fail after a SELECT
prepares successfully. Native boundary observations preserve these separate
stages.

## Syntax and rendering

`COLLATE` has its own AST constructor with separate qualified name components.
The PostgreSQL renderer prints a parenthesized expression and quotes each
component. Nested COLLATE expressions preserve their order and outer override.
Parameter traversal counts only expressions, retaining lexical occurrences
and numbered identities.

The parser respects PostgreSQL precedence and the restricted lower operand of
BETWEEN. A parenthesized lower operand can contain COLLATE. Quoted names
containing dots remain single components.

Identity and PostgreSQL rendering retain the existing checked AST roundtrip
and parameter-preservation obligations. SQLite parsing recognizes COLLATE,
but its checked renderer excludes it until a separate SQLite collation
contract is implemented. Earlier parser or rendering exclusions keep their
own diagnostic: the authored population has six SQLite parse exclusions,
39 `coverage.sqlite.collation` exclusions, four scalar-function signature
exclusions and one PostgreSQL-type exclusion. The expanded executable checker
also remains fail closed for this constructor until it accepts the required
collation environment.

## Evidence populations

The increment retains [50 authored queries](../fixtures/collations/synthetic.json)
and [50 unchanged PostgreSQL statements](../fixtures/collations/concrete.jsonl).
The authored examples cover literals, NULL, parameters, exact type modifiers,
casts, arrays, conditional expressions, scalar functions, derived tables, CTEs,
set operations, ordering, joins, and recursive CTEs.

Four independently specified table populations exercise empty results,
duplicates and nullable join sides. PostgreSQL prepares and executes the
authored original and rendered forms with bound values. Separate checks
compare row multiplicities, required ordering, exact type/modifier descriptions
and resolved collation identities. A typed LEFT JOIN wrapper lets
`pg_collation_for` observe collatable output metadata even when the inner query
returns no rows. This does not substitute parameter values into query text or
require the output to be registrable as a view.

Downloaded statements are never executed. Eighteen have complete conditional
catalog snapshots backed by written source declarations, with 28 independently
registered output positions. Thirty-two lack imported collation metadata in
their source declarations and remain explicit `catalog_prerequisite` entries
in that baseline inventory. A second inventory supplies an independently
observed test catalog for those 32 statements and preregisters 43 additional
output positions. All fifty are checked under one of these explicit contexts.

The observed context records ten imported collation objects in a disposable
PostgreSQL 16.15 instance. Eight came from the local catalog. Two required
authored fixture declarations backed by isolated Swedish and Turkish libc
locale files; no system locales were changed. The retained evidence includes
the catalog query, server version, encoding, native identities, providers,
locale metadata, and setup/input hashes. These are observations of the test
catalog, not claims about a source application's deployment.

The [snapshot provenance](../fixtures/collations/source_snapshot_provenance.json)
records source declarations, hashes, native implementation references and the
assumptions of successful creation and unshadowed visibility. Symbolic custom
identities refer to those declarations; they are not invented native OIDs.

## Verification

The final Lean build and complete runtime suites pass. The focused tests
include 139 collation checks, fifty authored full-query certificates, fifty
unchanged-source certificates, and 149 parsing/rendering checks. Six checks
preserve the pre-existing unsupported-expression diagnostics for scalar,
EXISTS and IN subqueries, aggregate forms and standalone row values.

The authored PostgreSQL replay passes four hundred original/canonical row
comparisons, four hundred independent collation observations and one hundred
exact descriptor positions. The separate boundary inventory contains 131
cases: 77 Valid, 45 Invalid and nine Unsupported. Of these, 121 have native
analysis observations; ten exercise declared snapshot behavior. The native
replay checks 242 PREPARE outcomes, 150 view-analysis outcomes, 114 descriptor
records covering 116 column positions, and two visibility snapshots.
Successful PREPARE, view registration and execution remain different claims.
All 1,196 Python regressions and the CI workflow lint pass. The existing
SQLite/PostgreSQL feature, parameter-execution and CLI regression helpers also
pass against the same frozen binary.

The broad renderer replay passes 1,237 SELECTs with 2,474 identity/PostgreSQL
renderings, four hundred SQLite renderings and eight hundred bounded SQLite
row comparisons. Grammar replay passes 12,259 records, 44 protocol checks,
125 outer statement families and 2,396 observed reduction productions.

The earlier recursive boundary population now records 42 Valid, 35 Invalid
and eight Unsupported cases. Its thirteen former collation exclusions become
eleven precise invalid recursive-collation results and two valid C-collation
results. The native replay checks all 170 original/canonical PREPARE outcomes
and ninety descriptor positions.

The compiled trust audit checks 29,939 project declarations, including 16,683
theorems and 622 generated executable recursion helpers. All five deliberate
bypass witnesses are rejected. Its frozen input inventory SHA-256 is
`0d5505c94c4d9275e727daefb6bd3aaa5e90840fdf4be4f4e293a4b7105ff764`,
based on commit `256c33064162ae817f81333cdbe38ffde5377b74`.
The verified CLI SHA-256 is
`30107dab6b193835a00680850b5820fb88a8f62b32676c6813a01e7a078b0ab7`.
The specification's thirteen-module normative import closure excludes the
parser, renderer and executable inference implementations.

The [industrial corpus replay](corpus/collation-v0.32/README.md) retains
257 typed-parser acceptances and nineteen documented rejections among 276
pinned records. This iteration does not close those remaining syntax gaps.

## Reproduction

```sh
lake build --wfail
python3 scripts/generate_collation_examples.py --check
python3 scripts/extract_collation_corpus.py --check
python3 -m unittest discover -s scripts -p 'test_collation*.py'
python3 scripts/check_collations_cli.py --local-bin /path/to/postgresql-16/bin
python3 scripts/check_collation_boundaries_cli.py --local-bin /path/to/postgresql-16/bin
python3 scripts/check_lean_trust.py --evidence-json .lake/trust-audit-v32.json
```

CI runs the new generated fixtures, source provenance checks, full contract
examples, native metadata observations and boundary classifications. Lean's
disclosed foundations remain `propext`, `Classical.choice` and `Quot.sound`;
project-defined axioms, proof placeholders and native proof shortcuts remain
prohibited.

These finite observations supplement the independent kernel-checked static
and rendering contracts. They do not prove locale ordering, termination,
arbitrary literal conversion, native execution equivalence or full PostgreSQL
coverage.
