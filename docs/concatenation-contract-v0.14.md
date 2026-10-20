# Scalar concatenation: v0.14

`sqlean-basic-select-v0.14` adds PostgreSQL scalar `||` concatenation to the
independent SELECT contract. This is the next bounded extended-operator
increment in the original external-corpus audit's fourth priority.
The AST uses a dedicated `Expr.concat left right`; existing arithmetic,
Boolean and comparison operators retain their previous representation.

The closed normative inventory contains five PostgreSQL declarations:

- `text || text → text`;
- `text || anynonarray → text`;
- `anynonarray || text → text`;
- `jsonb || jsonb → jsonb`;
- `bytea || bytea → bytea`.

`ConcatSignature` records the selected catalog family, its concrete argument
instantiation, and its result type. The polymorphic text families retain
the other argument's exact scalar identity. They do not assert a general
implicit conversion from that type to TEXT. The supported nonarray
inventory includes numeric, Boolean, temporal, UUID, JSON, JSONB and BYTEA
inputs. String-family arguments select TEXT; VARCHAR/CHAR modifiers are
discarded from the operator result. PostgreSQL converts CHAR input to TEXT
and removes its trailing padding, as specified in the
[string operator documentation](https://www.postgresql.org/docs/16/functions-string.html).

Unknown literals receive operator context. Two unknown inputs select
TEXT/TEXT. With one known JSONB or BYTEA input, the other unknown input
receives that same type. Otherwise an unknown next to a known nonarray
scalar selects the corresponding text family. Explicit TEXT remains
concrete: `JSONB || 'literal'` selects JSONB concatenation, while
`JSONB || CAST('literal' AS TEXT)` selects text concatenation. These are
distinct operator selections under PostgreSQL's
[operator-resolution rules](https://www.postgresql.org/docs/16/typeconv-oper.html).

All five admitted families propagate SQL NULL. Successful applications to
non-NULL operands produce non-NULL results, so output nullability is the
disjunction of the two operand flags. This is a normative rule about these
particular built-ins; catalog strictness alone would not establish that
non-NULL inputs produce non-NULL outputs. JSON's value `null` is separate
from SQL NULL. JSONB concatenation combines objects/arrays/scalars according
to the native [JSONB operator semantics](https://www.postgresql.org/docs/16/functions-json.html);
the static certificate does not evaluate those values or prove a general
execution equivalence.

Literal contents and conversions remain separate obligations. A string
assigned JSONB context may fail input parsing during PostgreSQL analysis,
even though the selected operator accepts JSONB arguments. Runtime
allocation or conversion failures are likewise outside this static
certificate. No successful-execution claim follows from a Valid result.

Array concatenation, append and prepend remain Unsupported. PostgreSQL
resolves them through different polymorphic operators with non-strict NULL
behavior; the scalar rule excludes every array operand before it can use
text conversion. Users can explicitly cast an array to TEXT to enter the
scalar domain. Standalone records, unknown functions and scalar subqueries
retain their existing coverage boundaries. Known nonstring scalar pairs
without an admitted `||` overload, such as INTEGER/INTEGER or JSON/JSON,
are Invalid. Exhausted checking fuel remains Inconclusive.

`ExprValid.concat` independently requires both operand derivations and the
selected normative signature. The checker constructs that derivation.
Parameter occurrences remain the entire left operand followed by the
entire right operand, and global anonymous numbering is checked at the
outer query boundary. General parameter-translation theorems retain the
signature, exact output metadata and full SELECT validity. The default
projection label is `?column?`, unless an explicit alias overrides it.

PostgreSQL gives `||` lower precedence than arithmetic and higher precedence
than comparison operators. SQLite gives it higher precedence than
multiplication. The parser follows the chosen dialect; canonical renderers
parenthesize concatenation to preserve the normalized AST. SQLite rendering
provides structural evidence and separately checked native observations,
not PostgreSQL typing or cross-dialect value equivalence. JSONB/BYTEA
declarations remain outside its corresponding rendering domain.

Verification includes 183 focused Lean checks and 50 synthetic full-query
certificates. The focused checks cover all admitted scalar families and
catalog declarations, unknown versus explicit TEXT selection, exact
modifier handling, each nullable-input combination, nested expressions,
parameter order, and Invalid/Unsupported/Inconclusive boundaries. Every
accepted query also receives identity/PostgreSQL rendering certificates
and general validity transport. Direct kernel examples construct
polymorphic text concatenation and all-NULL concatenation without calling
the checker.

The five-entry operator fixture is checked against the complete normative
inventory. Native PostgreSQL catalog observations independently check those
declarations, argument and result types, procedure identities, strictness and
scalar return behavior. Native verification checks 100 source/rendered
value-and-OID observations, 110 exact descriptors, ten expected errors and
17 type/syntax/profile boundaries. The 130 focused renderer cases also test
twelve shared-source dialect precedence trees and parameter transport.

Twenty-five synthetic cases have admitted SQLite syntax/rendering;
fifteen also have directly portable originals, giving forty native
observations. Twenty-five cases have explicit dialect exclusions.
SQLite expectations account for Boolean-to-text formatting, unenforced
VARCHAR/NUMERIC modifiers, text-bound JSONB parameters and precedence.
The shared spelling `'x' || 1 + 2 * 3` yields PostgreSQL TEXT `x7` and
SQLite INTEGER `6`; the two dialect parsers produce the corresponding
different ASTs, and their canonical renderings preserve those trees.

Fifty unchanged concrete sources, 49 PostgreSQL and one Hatchet,
receive rendering evidence only. They carry no invented schema, bindings,
or application-validity claim. This increment does not complete array
concatenation, all extended operators, or the full PostgreSQL contract.
