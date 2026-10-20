# Named arguments and defaults: v0.26

The profile `sqlean-basic-select-v0.26` adds an independent binding and default
contract for PostgreSQL `make_interval`, alongside generic named-call syntax.
Both `=>` and `:=` are retained in the AST. Calls may use all positional
arguments, all named arguments, or a positional prefix followed by named
arguments. Names can appear in any order after that prefix.

This does not introduce arbitrary function-definition validation. Only the
fixed `pg_catalog.make_interval` declaration has an independently modeled
parameter-name/default environment in this increment. Other named functions
remain rendering-only or Unsupported at the strong validity tier. Existing
ordinary positional function coverage remains available. The original
industrial named-call blockers occur in DML: their syntactic promotion does
not supply whole-DML validity contracts.

## Exact declaration and independent binding

`makeIntervalParameters` records seven parameters in declaration order:
`years`, `months`, `weeks`, `days`, `hours`, and `mins` are INTEGER; `secs` is
DOUBLE PRECISION. Each parameter has a nonnullable zero default, represented by
an explicit typed default constructor. The native return type is unmodified
INTERVAL. The single full-arity declaration is also linked into the ordinary
function inventory, bringing that inventory to 92 declarations.

`ArgumentAssignments` is an inductive relation over the lexical name metadata
and supplied scalar inputs. Its positional constructor is available only before
any named argument and advances the positional counter. Its named constructor
requires an exact decoded-name match at a declared parameter index.
`ArgumentsBound` additionally requires unique assigned indices, so duplicate
names and a name colliding with the positional prefix cannot receive a proof.
`ArgumentSlot` distinguishes supplied inputs from absent inputs receiving an
actual registered default. `ArgumentSlots` constructs the full declaration-order
input list. Missing required arguments cannot manufacture a default.

The checker returns this independent binding evidence, then resolves the exact
seven-argument signature. INTEGER fields admit SMALLINT widening and INTEGER
identity, but not implicit BIGINT/numeric narrowing. Seconds admit the existing
numeric widenings to DOUBLE PRECISION. Unknown literals receive the selected
slot's input context; concrete TEXT, NAME, and BOOLEAN do not become numeric
implicitly. Explicit casts remain governed by their own existing rules.

Successful calls are strict: the output's conservative nullable flag is the OR
of supplied input flags. Defaults do not add nullable inputs, so a call with no
arguments returns nonnullable INTERVAL. Input conversion, floating-point
rounding, and interval arithmetic are value obligations. Invalid literal
conversion can fail during native analysis or execution. PostgreSQL 16 rejects
NaN/infinite seconds at execution; large integer field arithmetic need not
raise an overflow error. The certificate promises neither successful execution
nor mathematical overflow behavior.

## Syntax and parameter order

`Expr.call` remains the representation of ordinary positional calls, including
`make_interval()` and calls that omit a trailing positional suffix.
`Expr.namedCall` stores `CallArgument.positional` and `CallArgument.named` nodes
in source order. A named node retains its decoded identifier and its arrow or
assignment notation. `ExprValid.defaultCall` and `ExprValid.namedCall` share the
binding judgment while keeping the original AST and lexical expression proof.

Slot binding rearranges only typing evidence. It never moves AST expressions,
renumbers anonymous placeholders, or inserts defaults into the rendered SQL.
For example, `make_interval(secs => ?, days => ?)` keeps its FLOAT8 occurrence
before its INTEGER occurrence even though `days` precedes `secs` in declaration
order. Repeated numbered parameters retain their occurrences and declarations.
The query-wide parameter-notation rules still reject mixed styles and
out-of-order anonymous indexes in a hand-built AST.

Native grammar accepts some malformed binding arrangements before semantic
analysis. The strong checker rejects positional-after-named order, duplicate
bindings, unknown names, excess arity, and concrete incompatible input types.
Generic named routines without registered parameter metadata remain Unsupported;
exhausted operational resources remain Inconclusive.

## Proof and rendering guarantees

The independent specification does not call the checker or accept its success
as a premise. A successful query certificate retains the exact profile, catalog,
parameter environment, original AST, ordered output names/types/nullability, and
complete derivation. Function labels use their native strong final name, so
`make_interval` survives ordinary cast and CASE label inheritance.

The universal validity-transport proof preserves lexical expression types and
uses, then reuses the unchanged slot-binding derivation. Identity rendering
certifies parsing back to the original AST, while PostgreSQL rendering certifies
parsing back to the parameter-translated AST. General translation idempotence
and serialization relations are extended through named arguments. These proofs
are separate from runtime SQL execution and its value obligations.

The rendering domain requires a `namedCall` to contain at least one named
argument. Hand-built all-positional `namedCall` nodes must use `Expr.call`
instead; static argument binding alone does not establish representation
admissibility. SQLite's parser rejects named-call source syntax, and its
independent AST rendering domain explicitly excludes named arguments.

## Registered evidence

The factor fixtures are under `fixtures/named_arguments/`. Fifty authored
queries cover both notations, omission/default rules, every parameter name,
reversed names, mixed calls, quoted/qualified names, implicit numeric coercions,
NULL, numbered and anonymous bindings, and composition with existing constructs.
The exact signature fixture records all names, input types, default literals,
and the native output type; Lean tests link it to the normative declaration.

The focused test registry includes every one of the 128 default-omission
subsets in both lexical orders and both notations, a 147-case declared-input
matrix in both nullability states, malformed and unsupported boundaries, and
independent kernel derivation witnesses. The targeted `--wfail` build and replay
passed 842 focused contract checks, 50 authored complete-query certificates,
seven fixed authentic-query certificates, and 109 renderer checks. All fifty
authentic statements passed both checked rendering profiles. The existing
100 scalar-form corpus cases and 54 boundary checks also pass, including exact
linkage of the 92-declaration function inventory. The prior read-only native probe has
316 authored observations, including all 128 omission subsets and the complete
147-case input matrix; it supplies external evidence, not proof axioms.

The authentic corpus has fifty unchanged queries. Five fixed source-free
PostgreSQL `interval.sql` statements receive full certificates without bindings.
Two fixed SQLC statements receive certificates conditional on explicitly
registered nonnullable FLOAT8/INTEGER parameter environments. Their type premise
comes from pinned generated `float64`/`int32` interface declarations, whose source
hash and method identities are checked; no source parameter values are invented
or observed. The other 43 statements receive rendering certificates only.
All fifty sources retain their original SQL and lexical parameter occurrences.
Eligibility and exact output expectations are fixed before checking, not selected
by checker success. Original-source SQL is not executed.

Project-wide build, native integration, and compiled trust-audit results are
recorded by the integration workflow after the focused tests freeze. No custom
axioms, `sorry`, unsafe declarations, or native-evaluation proof shortcuts are
introduced. This bounded increment is not a complete PostgreSQL contract and
does not authorize a release.

The integrated native harness checks 356 value/type observations, 356 SQL NULL
flags, 376 exact descriptors, twelve expected runtime errors, 159 native
analysis outcomes and the exact seven-slot catalog declaration/defaults.
All 128 omission subsets also receive independent SELECT certificates.
SQLite checks retain eight ordinary-function exclusions and 42 earlier
named-syntax parser boundaries. The original industrial replay accepts
256 of 276 statements; its three newly parsed statements are DML and do not
receive whole-DML contracts from this SELECT increment.

## Primary references

- [PostgreSQL 16 function-call notation](https://www.postgresql.org/docs/16/sql-syntax-calling-funcs.html)
- [PostgreSQL 16 make_interval declaration](https://www.postgresql.org/docs/16/functions-datetime.html)
- Pinned PostgreSQL 16 `gram.y` productions `func_arg_expr` and `param_name`,
  plus `pg_proc.dat` and native catalog/default-expression checks.
