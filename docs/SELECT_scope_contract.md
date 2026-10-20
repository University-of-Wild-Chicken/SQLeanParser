# Minimal independent SELECT name/scope contract

Baseline: `209f7deff71028931614dcae968cfd10323d448e` (main inspected through
GitHub and matched to the local checkout on 2026-10-20).

## Existing work and this increment

The baseline already contains `SelectContract/Profile.lean`, `Spec.lean`, and
`Checker.lean`, plus `checkQuery_sound`, an axiom guard, and an import guard.
It covers source-free/single-table SELECT, including expression types, but
explicitly excludes joins and correlation. This increment does not replace that
contract or strengthen the public assurance tier. It supplies a separate
**name/scope-only** contract for a small correlated SELECT fragment.
No production parser, resolver, or validator is modified.

When integrated into the current working tree, this contract coexists with
the newer rendering contract and SQLite dialect profile. Its label-visibility
rules follow the existing PostgreSQL-oriented checker, not all SQLite name
resolution behavior. For example, SQLite permits a projection alias in WHERE
(`SELECT u.id AS k FROM users u WHERE k=1`), while this fragment deliberately
rejects it. The new contract is not used to classify SQLite rendering inputs,
and neither public assurance tier is broadened by this patch.

## Normative fragment

Grammar (the public `ScopeContract.Query`/`Expr` datatypes enforce this boundary):

```text
query  ::= SELECT item (, item)* [FROM source (CROSS JOIN source)*] [WHERE expr]
source ::= table [AS alias]
item   ::= expr [AS label]
expr   ::= integer | text | boolean | column | qualifier.column
         | (expr binary-op expr) | unary-op expr | EXISTS (query)
```

Operators are the immutable `BinOp`/`UnOp` constructors. This contract checks
names in their operands, not their types. An empty SELECT list is invalid.
No wildcards, NULL, parameters, functions, aggregates, GROUP BY, HAVING, ORDER BY,
DISTINCT, LIMIT/OFFSET, derived tables, LATERAL, CTEs, set operations, other join
kinds, USING/NATURAL, source column renaming, or mutations are represented.
Unsupported Advanced syntax must NOT be reported invalid by this contract:
there is no general Advanced decoder or automatic fallback in this increment.

`Query.toAdvanced` embeds the fragment into the actual Advanced AST. All excluded
fields are at their default values. Each SQL fixture is separately parsed and
its entire AST compared against this embedding, so ignored SQL clauses cannot
silently disappear from those tests. There is no general parser-correctness proof.

## Environment and binding rules

* Schema table names are unique and nonempty; each table has a nonempty list of
  uniquely named, nonempty columns. Types are retained by the external Schema,
  but irrelevant to this name-only judgment. Keys/data constraints are outside it.
* Names are exact strings after lexer normalization. Manually built ASTs use
  exact strings; this contract does not implement case folding or quoted-name
  lexing. Schema-qualified catalog paths are outside the fragment.
* A source must name an existing table. Its visible relation name is its alias,
  or the table name if no alias is present. An alias hides the original name.
  Visible relation names must be distinct within one query block.
* All CROSS JOIN sources form one local frame. Projection labels do not enter
  that frame: they are unavailable in WHERE, other projection expressions, and
  nested EXISTS. Repeating output labels is permitted; they bind no inputs.
* Frames are ordered innermost first. Within a frame, an unqualified reference
  matches every column of that name; a qualified reference matches only columns
  of its visible relation. Exactly one match resolves. Two or more reject;
  ambiguity never falls through to an outer frame.
* With no match, an unqualified name may search the next frame. A qualified name
  may do so **only if that qualifier is not declared locally**. A local alias
  hides an outer alias even when the requested local column is absent.
* EXISTS pushes a complete new local frame (including an empty one for no FROM).
  It may access any enclosing frame under the same rules, including two or more
  levels outward. Its sources and labels never escape to its parent or siblings.
* A binding records `(lexical depth, visible relation, column)`. Depth zero is
  the current query block; empty query blocks still increase depth. Duplicate
  local aliases are ruled out by `SourcesWF`, so these identify source occurrences.

## Implementation and proof boundary

`ScopeContract/Spec.lean` imports only `AdvancedSyntax`, transitively `SyntaxBase`
and `Std`. `Resolves` has two inference rules: singleton local match, or an outer
resolution with the explicit `MayPass` side condition. `ExprValid` is a structural
proposition with existential `Resolves` derivations for column references;
`NameValid` additionally requires schema well-formedness. Neither relation calls
`Advanced.resolveColumn`, `inferExpr`, or any existing validation procedure.

The independent resolver is accompanied by soundness, completeness, uniqueness,
and a none/refutation equivalence. Its decision procedure is used to construct
`Decidable` instances, not to define the validity relation by checker success.
Expression decision uses a structurally sufficient computed weight: it exposes
no arbitrary fuel limit and does not turn budget exhaustion into invalidity.
`AdvancedNameValid` is the existential image of the fragment under its embedding;
`embedding_valid` merely packages that image, not a theorem about the old checker.

Kernel proof declarations:

| Declaration | Claim |
|---|---|
| `resolve_sound` | Independent resolver success gives a `Resolves` derivation |
| `resolve_complete` | Every `Resolves` derivation is found by that resolver |
| `resolve_iff` | The preceding equivalence |
| `resolves_unique` | Each reference has at most one target |
| `resolve_none_iff` | Failure iff no target is derivable |
| `embedding_valid` | Fragment validity gives validity of its own embedded AST |
| Five named theorems in `Tests/ScopeContract.lean` | Concrete correlated, missing, ambiguous, shadowed-missing, two-level cases (`by decide +kernel`) |

`by decide +kernel` uses kernel reduction, not `native_decide`. The trust test rejects
nonstandard axiom dependencies in the contract and focused test namespaces. Allowed standard Lean
axioms are `propext`, `Classical.choice`, `Quot.sound`; this is not a claim that
those are absent or that Lean's compiler/runtime is formally verified.

## Executable comparisons

```sh
lake build sqlean_scope_tests
lake exe sqlean_scope_tests
python3 -m unittest discover -s scripts -p 'test_scope_contract_independence.py' -v
# Existing full suite also imports and runs the new tests:
lake exe sqlean_tests
```

The focused suite compares 18 SQL fixtures against explicit expected judgments,
the fragment embedding, the independent decision procedure, and the existing
advanced checker. It reuses missing-column, ambiguous-column, hidden-base-name,
duplicate-alias, and correlated examples, then adds sibling leakage, label
leakage, missing-column alias barriers, and multi-level correlation cases.
A separate ill-typed but name-valid query demonstrates that full checker success
is NOT equivalent to name validity.

A deterministic enumeration covers stacks of length 0–3 over six explicit
frames (259 stacks), four qualifier choices, and four names: **4,144** exact
binding/depth comparisons with `Advanced.resolveColumn`. The adapter is test-only,
assigns every column INT, and never sets grouping restrictions. This is finite
coverage, not a theorem for arbitrary schemas, stacks, types, or SQL syntax.

Five deliberately wrong resolvers must each disagree with the independent
specification on at least one enumerated input: choose-first ambiguity,
outer-first resolution, no correlation, missing-column alias fallthrough, and
ambiguity fallthrough. These mutations test the reference probes' discrimination;
they do not mutate the production validator or prove whole-query mutation adequacy.

## Remaining proof obligations

1. Prove `Advanced.resolveColumn` refines `Resolves` for every well-formed frame
   stack produced by this fragment, including preservation of type information
   through the test adapter's generalized replacement. These frames have
   nonempty relation-column lists (from SchemaWF), distinct local qualifiers
   (from SourcesWF), and no grouping restriction (`Scope.allowed = none`).
   Do not generalize the current flattening adapter to arbitrary frames:
   an empty-column relation still creates a qualifier barrier in this spec,
   but flattening it into Advanced bindings loses that declaration.
2. Prove Advanced source construction produces exactly `frame schema sources`,
   preserving relation uniqueness and alias barriers for all fragment queries.
3. Under SchemaWF, prove `Advanced.checkQuery schema [] q.toAdvanced = .ok out`
   implies `NameValid schema q`. This needs an induction through its expression,
   FROM and query traversal, accounting for the existing checker's finite fuel.
4. Do NOT assert the converse: name-valid queries can be ill-typed. A completeness
   theorem would need independent type rules, fragment inclusion, and sufficient
   checker fuel. Parser/embedding injectivity or a checked decoder is separate work.
5. Integrate a proof-producing certificate into the public assurance API only
   after those bridges are proved; this patch leaves its coverage unchanged.

No statement here proves successful database execution, result equivalence,
cardinality, constraints, termination of recursive SQL, or full PostgreSQL
conformance. No PostgreSQL parameter oracle is rerun as part of this task.
