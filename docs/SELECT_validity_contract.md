# SQLean SELECT validity contract — initial draft v0.1

**This contract defines when a SELECT query is statically valid, independently of the executable validator.** It is a proposed specification, not a claim about what SQLeanParser currently proves.

I interpret **“universal SELECTs”** as the general SELECT family: projections, joins, grouping, subqueries, correlation, CTEs, and set operations—not merely a single-table fragment. Those query forms are already represented in your advanced AST. 

The contract below applies to **all finite compositions of the included constructs**, subject to the stated restrictions. It does not claim compatibility with every SQL dialect.

---

## 1. Purpose and central guarantee

Given a query AST, a catalog, a parameter environment, and a fixed SQL language profile, validation shall establish:

> Every relation and column reference is legally bound; every expression is well typed in its evaluation context; every query clause obeys its placement and dependency restrictions; and the query has a justified, ordered output schema.

A successful validation result shall identify:

- The exact query and environments being certified.
- The ordered output columns, their types, and their nullability.
- A derivation establishing the validity conditions in this contract.

For SELECT queries, the resulting catalog shall equal the input catalog.

**Successful validation shall not imply successful execution, termination, deterministic row selection, or equivalence between source SQL and rendered SQL.**

Those require separate contracts.

## 2. Language boundary

### Included query forms

The initial specification covers:

| Area | Included constructs |
|---|---|
| Projection | Expressions, aliases, `*`, qualified wildcards, `ALL`, ordinary `DISTINCT` |
| Sources | Catalog relations, derived queries, CTE references, source-free SELECT |
| Joins | `INNER`, `CROSS`, `LEFT`, `RIGHT`, `FULL`, with `ON`, `USING`, or `NATURAL` where appropriate |
| Expressions | Literals, parameters, columns, supported arithmetic and comparisons, Boolean operators, casts, null tests, `LIKE`, `IN`, and `BETWEEN` |
| Grouping | `GROUP BY`, `HAVING`, `COUNT`, `SUM`, `AVG`, `MIN`, `MAX`, aggregate `DISTINCT`, aggregate `FILTER` |
| Subqueries | Scalar subqueries, `EXISTS`, `IN` subqueries, correlation, and `LATERAL` derived queries |
| Composition | Nonrecursive CTEs, the restricted recursive CTE form defined below, `UNION`, `INTERSECT`, `EXCEPT`, and their `ALL` forms |
| Final clauses | `ORDER BY`, explicit null placement, nonnegative literal limits and offsets |

### Excluded from this initial version

Window functions, grouping sets, `ROLLUP`, `CUBE`, table-valued functions, arbitrary user-defined functions, arrays, composite values, and mutation-containing CTEs require separate specification extensions.

`DISTINCT ON` and `ILIKE` shall also be separate dialect extensions rather than silently included in the common core.

**An excluded construct is unsupported under this contract, not necessarily invalid SQL.**

A future extension must add explicit rules; it cannot inherit acceptance merely because the parser or checker already handles the syntax.

## 3. Fixed language profile

Validity shall be relative to a **versioned, independently specified language profile**.

The profile shall fix identifier comparison, supported scalar types, operator and aggregate signatures, implicit conversions, explicit casts, common-type selection, and any dialect-specific name-resolution rules.

The profile must be fixed before checking a query. It shall not be inferred from whichever behavior allows that query to pass.

In particular:

> “The implementation accepts these operands” is not an operator signature.

Concrete type distinctions shall be retained whenever they affect validity or output types. A coarse family such as “integer” or “real” may be reported as an abstraction, but shall not silently replace the underlying typing rules.

For example, PostgreSQL distinguishes the result types of `SUM(integer)` and `SUM(bigint)`, while `COUNT` produces `bigint`. A generic “numeric input produces the same numeric type” rule would therefore not establish PostgreSQL-compatible typing. [PostgreSQL](https://www.postgresql.org/docs/16/functions-aggregate.html)

**This contract is parameterized by the profile, but the profile is not an unrestricted implementation hook. Its tables and rules are part of the specification.**

## 4. Input assumptions and certificate identity

### Catalog

The catalog shall provide an ordered schema for each accessible relation. Every column shall have a name, a supported type, and declared nullability.

Catalog relation identifiers shall be unique within their namespace. Column identifiers shall be unique within a base relation. Invalid metadata shall be reported as an invalid environment, not repaired by choosing the first matching entry.

Any key or dependency metadata used to justify acceptance shall be explicit. The validator shall not assume that a column is unique, that a table is nonempty, or that a foreign key is enforced merely because its name suggests such a property.

### Parameters

Every referenced parameter shall have a declared identity and type. Repeated references to the same parameter shall denote the same binding.

Parameters represent values, not table names, column names, operators, or arbitrary SQL fragments.

### Query identity

The certificate shall apply to the exact AST, catalog, parameter environment, and profile.

Changing any of these invalidates the certificate unless a separate transport theorem justifies reuse. A serialized hash may identify an artifact, but shall not itself substitute for the equality obligations.

The primary contract concerns ASTs. Correct tokenization, parsing, identifier normalization, and correspondence to the original source string remain separate obligations.

## 5. Name resolution and scope

Every column reference shall resolve to **exactly one binding permitted at that syntactic position**.

An unqualified reference shall be resolved in the nearest visible query scope containing matching columns. Multiple matches in that scope make the reference ambiguous; the resolver shall not select one arbitrarily or continue outward looking for a convenient match.

For a qualified reference, the qualifier shall first identify a visible relation binding. The column must then belong to that binding. If an inner binding shadows an outer qualifier, a missing column in the inner binding shall not cause fallback to the outer one.

A relation alias replaces that occurrence’s exposed relation name. Self-joins create distinct bindings even when both occurrences refer to the same catalog table.

Clause-specific visibility shall be explicit. For the initial profile:

| Position | Visibility of SELECT-list aliases |
|---|---|
| Another expression in the same SELECT list | Not visible |
| `WHERE` or join `ON` | Not visible |
| `HAVING` | Not visible |
| Bare name in `GROUP BY` | Permitted; an input-column match takes precedence |
| Bare name in `ORDER BY` | Permitted; an output-name match takes precedence |
| Inside a larger expression | Not automatically substituted as a variable |

An ambiguous selected interpretation remains ambiguous; precedence is not permission to choose among duplicates.

**Correlation shall preserve binding identity across query levels.** Reusing the same spelling in an inner query shall not capture or alter an already resolved outer binding.

## 6. Expression typing and nullability

An expression shall be valid only if a specification rule justifies its operands, result type, and permitted context.

The initial rules shall require:

| Expression category | Required justification |
|---|---|
| Literal | A supported literal form and its specified type |
| Column | A unique legal binding and its effective type |
| Parameter | A declared parameter binding |
| Arithmetic | An applicable numeric operator signature |
| Comparison | An applicable comparison signature, including any permitted coercions |
| Boolean connective | Boolean operands |
| Pattern matching | Supported text operands and pattern operation |
| Cast | A supported source-to-target conversion |
| `IN` / `BETWEEN` | Compatible operand types under the profile’s rules |
| Subquery expression | The corresponding subquery rule in Section 11 |

A non-Boolean value shall not become a predicate merely because an implementation language treats it as truthy.

### NULL is not “any type”

An untyped `NULL` may acquire a type from an explicitly permitted contextual rule. It shall not act as an unrestricted wildcard that makes incompatible expressions acceptable.

The profile shall specify what happens when no type is determined, including any default for an unconstrained projected `NULL`. Defaulting, rejection, and contextual inference are distinct rules—not interchangeable checker conveniences.

### Nullability is conservative

A non-null annotation shall require a rule establishing that the expression cannot produce SQL NULL under the model.

A nullable annotation means NULL is possible or has not been excluded. It does not assert that NULL will occur.

Nullable Boolean expressions are valid predicates. The intended Boolean model has three truth values; logical negation and conjunction shall not be treated as ordinary two-valued Boolean operations when NULL is possible. [PostgreSQL](https://www.postgresql.org/docs/16/functions-logical.html)

For the initial contract, predicate-based nullability refinement is not assumed. For example, filtering with `x IS NOT NULL` does not automatically strengthen the reported type of every later occurrence of `x`.

## 7. FROM sources and joins

### Sources

A table reference shall resolve to a visible CTE or catalog relation according to the namespace rules.

A derived source shall itself satisfy this SELECT contract. Its exposed columns shall come from its certified output schema—not from independently reconstructed guesses about its SELECT list.

A SELECT without `FROM` has an empty local input-column scope. It may use constants, parameters, and legal outer bindings when nested in a correlated context. At top level, an unbound column or input wildcard is invalid.

### Join conditions

A `CROSS JOIN` has no matching predicate.

Other included join forms shall specify exactly one applicable condition form: `ON`, `USING`, or `NATURAL`.

An `ON` expression shall have Boolean type and shall reference only bindings visible at that join node. References to a later source are invalid.

### Outer-join nullability

Join output typing shall account for null extension:

- `LEFT JOIN` makes right-side output bindings nullable.
- `RIGHT JOIN` makes left-side output bindings nullable.
- `FULL JOIN` makes bindings from both sides nullable.

A column declared `NOT NULL` in its base table may therefore be nullable after an outer join. The specification shall distinguish the inputs used to check `ON` from the post-join bindings exposed to later clauses. [PostgreSQL](https://www.postgresql.org/docs/16/queries-table-expressions.html)

### USING and NATURAL

Every `USING` name shall occur unambiguously on both sides, and its two types shall support the required equality comparison and merged output type.

The unqualified join output shall contain one merged column for each `USING` name, followed by the remaining left columns and remaining right columns. Qualified references shall retain their distinct source identities and applicable null extension.

`NATURAL` shall determine its matching columns from the two exposed schemas. It shall not match unrelated columns merely because an implementation lookup returns them first.

The merged-column type and nullability shall have their own rules; copying either side’s annotation without justification is insufficient.

## 8. Derived sources, output names, and wildcards

The SELECT list shall be nonempty after wildcard expansion.

Every ordinary SELECT item contributes one output position. A wildcard contributes the ordered columns of its permitted source scope. `COUNT(*)` is a separate aggregate construct, not ordinary wildcard expansion.

Output position is fundamental: repeated expressions and repeated labels shall not collapse into one column.

An explicit alias supplies an output label. A simple column projection may inherit its column name.

For this initial profile, computed outputs used at a derived-table or CTE boundary shall receive explicit names, either through projection aliases or a complete boundary column list. Boundary names shall be unique.

This is a deliberate profile restriction, not a claim that every SQL engine requires unique derived-output names. At the top level, duplicate labels may remain valid, but an ambiguous later reference to such a label shall fail.

Column renaming shall preserve output order, types, nullability, and identity. It shall not change which expression produced a column.

## 9. WHERE, grouping, HAVING, and aggregates

### Row filtering

`WHERE` shall have Boolean type in the row-input scope.

An aggregate belonging to the current query level shall not occur in its `WHERE`, join condition, or grouping key.

### Grouped-query classification

A query is grouped when it contains grouping keys, a `HAVING` clause, or an aggregate belonging to that query level.

In a grouped query, projection, `HAVING`, and ordering expressions shall be justified from grouping keys, legal aggregate results, constants, parameters, and permitted outer bindings.

An ordinary local column cannot be projected merely because the implementation can assign it a scalar type. Its value must also be legal at group level. PostgreSQL likewise distinguishes row filtering from group filtering and restricts references to ungrouped columns. [PostgreSQL](https://www.postgresql.org/docs/16/sql-select.html)

### Group dependency

For v0.1, group dependency shall be established structurally after name resolution.

For example:

```sql
SELECT a + b FROM t GROUP BY a, b;
```

is permitted because both column dependencies are grouped.

```sql
SELECT a FROM t GROUP BY a + b;
```

is not justified merely because `a` occurs inside a grouping expression.

The specification shall not infer arbitrary algebraic equivalences. Functional-dependency exceptions, such as deriving other columns from a grouped primary key, require a separate explicit rule and trusted metadata.

### Aggregate rules

Every aggregate shall have an applicable signature. `COUNT(*)` and `COUNT(expression)` shall be distinct cases.

Aggregate arguments and `FILTER` predicates shall be checked in their proper row-input context. A filter must be Boolean and shall not contain a nested aggregate belonging to the same query level.

Aggregate results shall not inherit non-nullness from their arguments. In particular, the empty-input behavior distinguishes `COUNT` from aggregates such as `SUM` and `AVG`. [PostgreSQL](https://www.postgresql.org/docs/16/functions-aggregate.html)

For the initial profile, **cross-level aggregate ownership is excluded**: aggregate arguments and filters shall not directly depend on enclosing query bindings. Ordinary correlated subqueries remain included. More general SQL rules that assign an aggregate to an outer query level require a separate extension.

This restriction prevents a syntactically inner aggregate from being used to bypass an outer query’s grouping obligations.

## 10. Correlation and LATERAL

An expression subquery may access enclosing bindings that are visible at its location.

An ordinary derived query shall not access sibling sources of its containing `FROM` clause.

A `LATERAL` derived query may access the preceding sources or left-side join bindings explicitly made available to it. It shall not reference future sources or create a circular source dependency.

A lateral dependency across a `RIGHT` or `FULL` join shall not be accepted where the required source row is not available under that join’s binding rules. PostgreSQL explicitly distinguishes these restrictions from ordinary lateral references. [PostgreSQL](https://www.postgresql.org/docs/16/sql-select.html)

Correlation does not erase grouping restrictions: a captured column belonging to a grouped outer query must still satisfy that outer query’s group-dependency requirements.

Every captured reference shall retain its owning query level in the derivation.

## 11. Subquery expressions

### Scalar subquery

A scalar subquery shall have exactly one output column.

Its expression type shall be that column’s type, conservatively made nullable because the query may return no rows.

**Validation shall not require proof that it returns at most one row.** That is a separate cardinality-safety obligation. A multirow result can cause an execution error even when static validation succeeds; an empty result yields NULL under the reference SQL behavior. [PostgreSQL](https://www.postgresql.org/docs/16/sql-expressions.html)

### EXISTS

An `EXISTS` subquery shall be independently valid. Its expression result is non-null Boolean.

Its output width need not be one. Ignoring its output values does not permit unresolved names or otherwise invalid expressions inside it.

### IN subquery

For the scalar `IN` form included here, the subquery shall have exactly one output column. The left expression and that column shall support the required comparison.

Its Boolean result may be nullable. `NOT IN` shall not be treated as interchangeable with `NOT EXISTS`; NULL-bearing comparisons distinguish them. [PostgreSQL](https://www.postgresql.org/docs/16/functions-subquery.html)

## 12. CTEs and restricted recursion

### Nonrecursive CTEs

Bindings in an ordinary `WITH` list shall be checked sequentially. A binding may use earlier bindings and the otherwise visible environment, but not itself or a later sibling.

Duplicate CTE names within one list are invalid. A visible CTE may shadow an outer relation name according to the namespace rules.

A supplied CTE column list shall match the output arity and satisfy the boundary naming requirements.

Each CTE body shall be validated even when the main query does not reference it.

### Recursive CTEs

The initial recursive profile admits an anchor combined with a recursive step using `UNION` or `UNION ALL`.

The anchor shall not reference the CTE being defined. The step shall contain exactly one direct recursive source occurrence.

For v0.1, the recursive step may use projection, predicates, and inner or cross joins. Aggregation, outer joins involving the recursive occurrence, nested recursive references, and mutual recursion are outside this profile.

There shall exist a stable output schema under which both the anchor and the recursive step are well typed. The step shall be checked with the recursive name bound to that schema.

Its output nullability must cover both branches. Checking the step only against an overly strong anchor schema is insufficient.

**Recursive validity establishes a stable typing contract, not termination.** A well-typed recursive query can continue indefinitely; deduplication alone does not universally prevent that. [PostgreSQL](https://www.postgresql.org/docs/16/queries-with.html)

## 13. Set operations

Both operands of `UNION`, `INTERSECT`, or `EXCEPT` shall be independently valid.

Their output widths shall agree. Corresponding positions shall admit a common type according to the fixed profile.

Compatibility is positional, not based on matching output names. Output labels come from the left operand unless an enclosing naming boundary overrides them.

The result’s nullability shall conservatively cover possible values contributed by the operation. For a simple initial rule, `UNION` and `INTERSECT` may use the union of operand nullability possibilities; `EXCEPT` may retain the left operand’s nullability, subject to any conversion rule.

`ALL` changes multiplicity behavior, not the number or ordering of output columns.

Parentheses and AST nesting determine operand boundaries. An operand-local limit or ordering shall not migrate to the enclosing compound query. These distinctions also occur in the reference SQL set-operation rules. [PostgreSQL](https://www.postgresql.org/docs/16/queries-union.html)

## 14. DISTINCT, ordering, and pagination

`DISTINCT` shall require equality support for every output component.

For ordinary `SELECT DISTINCT`, ordering shall be restricted to projected values under this initial profile. A checker shall not silently introduce an unprojected ordering value that changes the intended distinction between rows.

For an ordinary SELECT, each sort item shall resolve to a permitted expression, output label, or one-based output position. Positions must be within the expanded output width.

For a compound query, ordering shall refer only to its exposed output names or positions, not to hidden operand bindings.

Every sort key shall support ordering. Direction and null placement shall be represented independently.

**The absence of an ordering clause is not invalid. Nor does a non-unique ordering imply deterministic tie-breaking.** Sorting rules do not by themselves establish a unique result sequence. [PostgreSQL](https://www.postgresql.org/docs/16/queries-order.html)

The initial pagination fragment accepts nonnegative literal limits and offsets. Zero is valid. These clauses do not alter the output schema.

Parameter-valued pagination requires an extension specifying its typing and runtime value constraints.

## 15. Validation outcomes and assurance boundary

The public result shall distinguish four cases:

| Outcome | Meaning |
|---|---|
| **Valid** | A derivation establishes this contract and the returned output schema |
| **Invalid** | A stated validity condition is violated |
| **Unsupported** | A required construct or profile rule lies outside the specified language |
| **Inconclusive** | Resource exhaustion or another operational limitation prevented a decision |

Fuel exhaustion, maximum recursion depth, and timeouts shall not constitute evidence that the SQL is invalid.

Likewise, a successful AST-level certificate does not establish:

> Correct parsing, correct rendering, database authorization, safe casts for actual values, absence of arithmetic errors, scalar-subquery cardinality safety, recursive termination, or successful execution against a live database.

Those exclusions apply even when test suites happen to cover examples of the corresponding behavior.

## 16. Required independence

The declarative specification shall not call the executable query checker, expression inference procedure, or implementation-specific acceptance predicates.

Sharing syntax types and immutable catalog representations is permissible. Sharing a normative signature table is permissible when that table is independently specified and explicitly part of the trusted specification.

A mismatch between implementation and specification shall produce one of three outcomes: an implementation defect, an explicitly reviewed specification revision, or an acknowledged coverage gap.

It shall not be resolved by silently weakening the specification.

The initial theorem obligation is:

\[
\boxed{
\begin{aligned}
&\text{WellFormedEnvironment}(C,P,\Pi)\\
{}\land{}&\text{IncludedQuery}_{\Pi}(q)\\
{}\land{}&\text{Check}(C,P,q)=\text{Success}(R)\\
\Longrightarrow{}&
\text{SelectValid}_{\Pi}(C,P,q,R).
\end{aligned}
}
\]

Here, `SelectValid` is defined by the rules above—not by checker success.

**The resulting claim is: every certified query has a justified static interpretation and output schema under a fixed language profile. It is not yet a claim that every certified query executes successfully or that SQLeanParser implements all of PostgreSQL.**
