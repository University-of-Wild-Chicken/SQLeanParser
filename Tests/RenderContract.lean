import SQLean.RenderContract
import Tests.Support

namespace SQLean.Tests
open Advanced

private def number (n : Nat) : Advanced.Expr := .literal (.int n)
private def one : Advanced.Expr := number 1
private def two : Advanced.Expr := number 2
private def truth : Advanced.Expr := .literal (.bool true)
private def column (name : String) : Advanced.Expr := .column none name
private def queryOf (expr : Advanced.Expr) : Advanced.Query :=
  {body := .select {items := [.expression expr]}}
private def projection (items : List Advanced.SelectItem) : Advanced.Query :=
  {body := .select {items}}
private def withSource (source : Advanced.From) : Advanced.Query :=
  {body := .select {items := [.all], source := some source}}
private def table (name : String := "t") : Advanced.From := .table name
private def repeated (n : Nat) (value : String) : String :=
  String.join (List.replicate n value)
private def zero : String := String.singleton (Char.ofNat 0)
private def nestedNegation : Nat → Advanced.Expr
  | 0 => one
  | n + 1 => .unary .neg (nestedNegation n)
private def anonymous (ordinal : Nat) : Advanced.Expr := .parameter (.anonymous ordinal)

/-- Constructive kernel-checked witnesses for the independent domain. The
parser-backed certificate boundary is tested separately below. -/
example : RenderContract.Admissible (queryOf one) := by
  refine ⟨{depth := 4}, ?_, ?_, ?_⟩
  · unfold queryOf one number RenderContract.inspectQuery
    dsimp
    unfold RenderContract.inspectSelect
    dsimp
    unfold RenderContract.inspectItem RenderContract.inspectExpr
    rfl
  · decide
  · decide

example : RenderContract.Admissible (queryOf (anonymous 1)) := by
  refine ⟨{depth := 4, parameters := [.anonymous 1]}, ?_, ?_, ?_⟩
  · unfold queryOf anonymous RenderContract.inspectQuery
    dsimp
    unfold RenderContract.inspectSelect
    dsimp
    unfold RenderContract.inspectItem RenderContract.inspectExpr
    rfl
  · decide
  · decide

/-- Constructed independently of the parser: syntax serialization does not need
a schema or a typing derivation, so unresolved names remain admissible. -/
private def positiveQueries : List (String × Advanced.Query) :=
  let q := queryOf one
  let left : Advanced.Query := {q with orderBy := [⟨one, true, some false⟩], limit := some 2}
  let right : Advanced.Query := {q with limit := some 3, offset := some 1}
  [
    ("source-free integer", q),
    ("NULL versus text", projection [.expression .null, .expression (.literal (.text "NULL"))]),
    ("Boolean values", projection [.expression truth, .expression (.literal (.bool false))]),
    ("empty text", queryOf (.literal (.text ""))),
    ("text lexical containment", queryOf (.literal (.text "'; SELECT 99; --\\\n\t\r界"))),
    ("unknown binding still renderable", withSource (.table "absent" (some "unknown"))),
    ("identifier punctuation", queryOf (.column (some "a.b") "q\"; --")),
    ("identifier case and Unicode", withSource (.table "界" (some "Select"))),
    ("single name containing period", queryOf (.column none "a.b")),
    ("qualified name", queryOf (.column (some "a") "b")),
    ("63 ASCII identifier bytes", withSource (table (repeated 63 "x"))),
    ("63 UTF8 identifier bytes", withSource (table (repeated 21 "界"))),
    ("Unicode is not normalized", projection [
      .expression one (some "é"), .expression two (some "e\u0301")]),
    ("repeated select items and aliases", projection [
      .expression one (some "same"), .expression one (some "same")]),
    ("qualified wildcard", {body := .select {
      items := [.all (some "t")], source := some (table)}}),
    ("table alias column names", withSource (.table "t" (some "alias") ["left", "right"])),
    ("derived alias columns", withSource (.derived q "q" ["number"])),
    ("lateral derived source", withSource (.join .cross (table)
      (.derived (queryOf (.column (some "t") "id")) "lat" ["value"] true) .none)),
    ("derived-first nested join",
      { body := .select {
          items := [.all]
          source := some (.join .left
            (.derived {q with orderBy := [⟨one, true, none⟩], limit := some 1} "a")
            (.join .inner (.derived right "b") (table "c") (.using ["id"])) (.on truth)) }
        orderBy := [⟨one, false, some true⟩]
        limit := some 2 }),
    ("grouped join of compound derived queries",
      withSource (.join .cross
        (.derived {body := .set .union true left right} "a")
        (.derived {q with ctes := [⟨"inner_cte", right, []⟩]} "b") .none)),
    ("nested subtraction", queryOf (.binary .sub one (.binary .sub two one))),
    ("nested division", queryOf (.binary .div one (.binary .div two one))),
    ("negated conjunction", queryOf (.unary .not (.binary .and truth truth))),
    ("adjacent unary negatives", queryOf (.unary .neg (.unary .neg one))),
    ("cast placement", queryOf (.cast (.unary .neg (.cast one ⟨.real, []⟩)) ⟨.numeric, [12, 3]⟩)),
    ("COUNT star FILTER", queryOf (.filteredAggregate .countAll truth)),
    ("aggregate FILTER and DISTINCT", queryOf (.filteredAggregate (.aggregate .sum one true) truth)),
    ("IS NULL", queryOf (.isNull .null)),
    ("IS NOT NULL", queryOf (.isNull one true)),
    ("LIKE", queryOf (.pattern (.literal (.text "a")) (.literal (.text "%")))),
    ("ILIKE", queryOf (.pattern (.literal (.text "a")) (.literal (.text "%")) true)),
    ("IN list", queryOf (.inList one [one, .null, two])),
    ("BETWEEN", queryOf (.between one two one)),
    ("NOT BETWEEN", queryOf (.between one two one true)),
    ("IN subquery", queryOf (.inQuery one q)),
    ("EXISTS", queryOf (.exists q)),
    ("scalar subquery", queryOf (.scalarQuery q)),
    ("scalar subquery begins arithmetic", queryOf (.binary .add (.scalarQuery q) two)),
    ("scalar subquery begins comparison", queryOf (.binary .eq (.scalarQuery q) one)),
    ("scalar subquery begins IN list", queryOf (.inList (.scalarQuery q) [one, two])),
    ("scalar subquery begins BETWEEN", queryOf (.between (.scalarQuery q) one two)),
    ("scalar subquery begins IS NULL", queryOf (.isNull (.scalarQuery q))),
    ("scalar subquery begins IN subquery", queryOf (.inQuery (.scalarQuery q) q)),
    ("scalar subquery first of multiple IN elements", queryOf (.inList one [.scalarQuery q, two])),
    ("nested scalar-query arithmetic", queryOf (.binary .div
      (.binary .add (.scalarQuery q) two) (.binary .sub two (.scalarQuery q)))),
    ("ON versus WHERE", {body := .select {
      items := [.all], source := some (.join .left (table "a") (table "b")
        (.on (.binary .eq (.column (some "a") "id") (.column (some "b") "id")))),
      whereClause := some (.isNull (.column (some "b") "id"))}}),
    ("grouping and HAVING", {body := .select {
      items := [.expression (column "x"), .expression (.aggregate .sum (column "y"))],
      source := some (table), groupBy := [column "x"],
      having := some (.binary .gt (.aggregate .sum (column "y")) one)}}),
    ("DISTINCT", {body := .select {items := [.expression one], distinct := true}}),
    ("DISTINCT ON",
      { body := .select {items := [.expression one], distinctOn := [one, two]}
        orderBy := [⟨one, false, some true⟩, ⟨two, true, some false⟩] }),
    ("zero pagination and order ordinal",
      {q with orderBy := [⟨one, false, none⟩], limit := some 0, offset := some 0}),
    ("CTE binding order", {q with ctes := [⟨"first", q, ["x"]⟩, ⟨"second", q, []⟩]}),
    ("recursive CTE marker",
      { body := .select {items := [.expression (column "n")], source := some (.table "r")}
        ctes := [⟨"r", {body := .set .union true q {body := .select {
          items := [.expression (.binary .add (column "n") one)]
          source := some (.table "r")
          whereClause := some (.binary .lt (column "n") (number 4))}}}, ["n"]⟩]
        recursive := true }),
    ("right-associated EXCEPT with operand limits",
      {body := .set .except false left {body := .set .except false q right}}),
    ("compound owns CTE and pagination",
      { body := .set .intersect false left right
        ctes := [⟨"outer", q, []⟩]
        orderBy := [⟨one, false, none⟩]
        limit := some 1
        offset := some 0 }),
    ("nested binding shadow", {body := .select {
      items := [.expression (.scalarQuery {body := .select {
        items := [.expression (.column (some "a") "id")],
        source := some (.table "inner" (some "a"))}})],
      source := some (.table "outer" (some "a"))}}),
    ("repeated numbered parameters", projection [
      .expression (.parameter (.numbered 2)), .expression (.parameter (.numbered 1)),
      .expression (.parameter (.numbered 2))]),
    ("anonymous BETWEEN identity", queryOf (.between (.parameter (.anonymous 1))
      (.parameter (.anonymous 2)) (.parameter (.anonymous 3)))),
    ("anonymous CTE and nested SELECT",
      { body := .select {
          items := [.expression (.parameter (.anonymous 2)),
            .expression (.scalarQuery (queryOf (.parameter (.anonymous 3))))]
          source := some (.derived (queryOf (.parameter (.anonymous 4))) "d")}
        ctes := [⟨"c", queryOf (.parameter (.anonymous 1)), ["x"]⟩]
        orderBy := [⟨.parameter (.anonymous 5), false, none⟩] }),
    ("anonymous traversal through every clause",
      { body := .select {
          items := [
            .expression (.filteredAggregate (.aggregate .sum (anonymous 3)) (anonymous 4)),
            .expression (.inQuery (anonymous 5) (queryOf (anonymous 6))),
            .expression (.exists (queryOf (anonymous 7)))]
          source := some (.join .inner
            (.derived (queryOf (anonymous 8)) "a")
            (.derived (queryOf (anonymous 9)) "b") (.on (anonymous 10)))
          whereClause := some (anonymous 11)
          groupBy := [anonymous 12]
          having := some (anonymous 13)
          distinctOn := [anonymous 2] }
        ctes := [⟨"c", queryOf (anonymous 1), []⟩]
        orderBy := [⟨anonymous 14, false, none⟩] }),
    ("deep expression retains every node", queryOf (nestedNegation 200))
  ] ++
  ([BinOp.eq, .ne, .lt, .le, .gt, .ge, .and, .or, .add, .sub, .mul, .div].map
    fun op => ("binary operator", queryOf (.binary op one two))) ++
  ([UnOp.pos, .neg, .not].map fun op => ("unary operator", queryOf (.unary op one))) ++
  ([AggregateFn.count, .sum, .avg, .min, .max].flatMap fun fn =>
    [("aggregate", queryOf (.aggregate fn one)), ("DISTINCT aggregate", queryOf (.aggregate fn one true))]) ++
  ([TypeName.int, .bigInt, .text, .varchar, .bool, .real, .doublePrecision, .numeric].map
    fun typeName => ("concrete cast target", queryOf (.cast one ⟨typeName, []⟩))) ++
  ([("VARCHAR length", DataType.mk .varchar [17]),
    ("NUMERIC precision", DataType.mk .numeric [9]),
    ("NUMERIC precision scale", DataType.mk .numeric [12, 4])].map fun (name, type) =>
      (name, queryOf (.cast one type))) ++
  ([".5", "1.", "01.00", "1e0", "1E+02", "1.2500e-3", "12345678901234567890.00000000001"].map
    fun raw => ("exact numeric lexeme", queryOf (.decimal raw))) ++
  ([JoinKind.inner, .left, .right, .full].flatMap fun kind =>
    [("JOIN ON", withSource (.join kind (table "a") (table "b") (.on truth))),
     ("JOIN USING", withSource (.join kind (table "a") (table "b") (.using ["id", "name"]))),
     ("NATURAL JOIN", withSource (.join kind (table "a") (table "b") .natural))]) ++
  ([SetOp.union, .intersect, .except].flatMap fun op =>
    [("set distinct", {body := .set op false left right}), ("set ALL", {body := .set op true left right})])

private def invalidQueries : List (String × Advanced.Query) :=
  let q := queryOf one
  [
    ("recursive marker without CTE", {q with recursive := true}),
    ("contradictory DISTINCT flags", {body := .select {
      items := [.expression one], distinct := true, distinctOn := [one]}}),
    ("empty projection", projection []),
    ("empty table name", withSource (table "")),
    ("empty qualifier", queryOf (.column (some "") "x")),
    ("empty column name", queryOf (.column none "")),
    ("empty projection alias", projection [.expression one (some "")]),
    ("empty wildcard qualifier", projection [.all (some "")]),
    ("empty table alias", withSource (.table "t" (some ""))),
    ("table columns without alias", withSource (.table "t" none ["x"])),
    ("empty table column alias", withSource (.table "t" (some "alias") [""])),
    ("empty derived alias", withSource (.derived q "")),
    ("empty derived column alias", withSource (.derived q "d" [""])),
    ("empty CTE name", {q with ctes := [⟨"", q, []⟩]}),
    ("empty CTE column alias", {q with ctes := [⟨"c", q, [""]⟩]}),
    ("64 ASCII identifier bytes", withSource (table (repeated 64 "x"))),
    ("66 UTF8 identifier bytes", withSource (table (repeated 22 "界"))),
    ("identifier NUL", withSource (table ("before" ++ zero ++ "after"))),
    ("text NUL", queryOf (.literal (.text ("before" ++ zero ++ "after")))),
    ("empty IN list", queryOf (.inList one [])),
    ("FILTER nonaggregate", queryOf (.filteredAggregate one truth)),
    ("nested FILTER", queryOf (.filteredAggregate (.filteredAggregate .countAll truth) truth)),
    ("CROSS JOIN ON", withSource (.join .cross (table "a") (table "b") (.on truth))),
    ("CROSS JOIN USING", withSource (.join .cross (table "a") (table "b") (.using ["x"]))),
    ("NATURAL CROSS JOIN", withSource (.join .cross (table "a") (table "b") .natural)),
    ("missing join condition", withSource (.join .inner (table "a") (table "b") .none)),
    ("empty USING", withSource (.join .inner (table "a") (table "b") (.using []))),
    ("empty USING name", withSource (.join .inner (table "a") (table "b") (.using [""]))),
    ("numbered zero", queryOf (.parameter (.numbered 0))),
    ("anonymous zero", queryOf (.parameter (.anonymous 0))),
    ("anonymous skipped ordinal", queryOf (.parameter (.anonymous 2))),
    ("anonymous duplicate ordinal", projection [
      .expression (.parameter (.anonymous 1)), .expression (.parameter (.anonymous 1))]),
    ("anonymous reordered ordinal", projection [
      .expression (.parameter (.anonymous 2)), .expression (.parameter (.anonymous 1))]),
    ("anonymous reset in subquery", projection [.expression (.parameter (.anonymous 1)),
      .expression (.scalarQuery (queryOf (.parameter (.anonymous 1))))]),
    ("anonymous CTE traversal reversal",
      { body := .select {items := [.expression (.parameter (.anonymous 1))]}
        ctes := [⟨"c", queryOf (.parameter (.anonymous 2)), []⟩] }),
    ("integer type modifiers", queryOf (.cast one ⟨.int, [1]⟩)),
    ("VARCHAR zero", queryOf (.cast one ⟨.varchar, [0]⟩)),
    ("VARCHAR oversized", queryOf (.cast one ⟨.varchar, [10485761]⟩)),
    ("VARCHAR two modifiers", queryOf (.cast one ⟨.varchar, [3, 2]⟩)),
    ("NUMERIC zero precision", queryOf (.cast one ⟨.numeric, [0]⟩)),
    ("NUMERIC oversized precision", queryOf (.cast one ⟨.numeric, [1001]⟩)),
    ("NUMERIC excess modifiers", queryOf (.cast one ⟨.numeric, [4, 2, 1]⟩))
  ] ++
  (["", "1", "01", ".", "e1", ".e1", "1e", "1e+", "1e-", "+1.0", "-1.0",
    "1.2.3", "1e2x", "1.0 ", " 1.0", "1.0; SELECT 99", "1.0--", "1.0/* */",
    "NaN", "Infinity", "１.０", "0x1", "1_000.0"].map
    fun raw => ("malformed decimal field: " ++ raw, queryOf (.decimal raw)))

private def checked (profile : RenderContract.Profile) (label : String) (query : Advanced.Query) : IO Unit := do
  let certificate ← match RenderContract.check profile query with
    | .ok certificate => pure certificate
    | .error failure => throw (IO.userError s!"render unexpectedly failed: {label}: {reprStr failure}\n{Advanced.render (.query query)}")
  let reconstructed ← expectOk label (RenderContract.parseRendered profile certificate.sql)
  SQLean.Tests.assert (decide (reconstructed = RenderContract.expectedQuery profile query))
    s!"render changed an AST field: {label}"
  let stable ← match RenderContract.check profile reconstructed with
    | .ok certificate => pure certificate
    | .error _ => throw (IO.userError s!"canonical rerender failed: {label}")
  SQLean.Tests.assert (certificate.sql == stable.sql) s!"unstable canonical rendering: {label}"
  SQLean.Tests.assert (certificate.sql.endsWith ";") s!"missing statement terminator: {label}"
  expectError "full parser rejects extra statement"
    (RenderContract.parseRendered profile (certificate.sql ++ " SELECT 99;"))

/-- Instance evidence for the renderer boundary. These tests make no universal
target-language or semantic-equivalence claim. -/
def renderContractTests : IO Nat := do
  for profile in [RenderContract.Profile.identityV01, .postgres16V01] do
    for (label, query) in positiveQueries do
      checked profile label query
    for (label, query) in invalidQueries do
      match RenderContract.check profile query with
      | .error (.invalid _) => pure ()
      | .error failure => throw (IO.userError s!"invalid representation misclassified: {label}: {reprStr failure}")
      | .ok _ => throw (IO.userError s!"invalid representation accepted: {label}")
    match RenderContract.check profile (queryOf one) 0 with
    | .error (.inconclusive _) => pure ()
    | _ => throw (IO.userError "zero render budget must be inconclusive")
    match RenderContract.check profile (queryOf (nestedNegation 20)) 5 with
    | .error (.inconclusive _) => pure ()
    | _ => throw (IO.userError "insufficient render depth must be inconclusive")
    checked profile "NUMERIC scale above precision"
      (queryOf (.cast one ⟨.numeric, [2, 3]⟩))
    match RenderContract.check profile (queryOf (.inList one [.scalarQuery (queryOf one)])) with
    | .error (.unsupported _) => pure ()
    | _ => throw (IO.userError "singleton scalar-subquery IN list needs an explicit representational gap")
    match RenderContract.check profile (projection [
      .expression (.parameter (.anonymous 1)), .expression (.parameter (.numbered 1))]) with
    | .error (.unsupported _) => pure ()
    | _ => throw (IO.userError "mixed parameter styles must be explicitly unsupported")
  checked .identityV01 "identity retains large numbered slot" (queryOf (.parameter (.numbered 65536)))
  match RenderContract.check .postgres16V01 (queryOf (.parameter (.numbered 65536))) with
  | .error (.unsupported _) => pure ()
  | _ => throw (IO.userError "PostgreSQL oversized parameter slot must be unsupported")
  checked .postgres16V01 "PostgreSQL maximum numbered slot" (queryOf (.parameter (.numbered 65535)))
  let environment : Parameter → String
    | .anonymous n => s!"anonymous-value-{n}"
    | .numbered n => s!"numbered-value-{n}"
  SQLean.Tests.assert (RenderContract.transport .anonymous environment 2 == "anonymous-value-2")
    "anonymous environment transport selected wrong binding"
  SQLean.Tests.assert (RenderContract.transport .numbered environment 2 == "numbered-value-2")
    "numbered environment transport selected wrong binding"
  -- The total low-level serializer has no fixed depth cap or replacement SQL.
  let deep := Advanced.render (.query (queryOf (nestedNegation 4096)))
  SQLean.Tests.assert (deep.toList.count '-' == 4096 && !deep.contains 'N')
    "deep rendering replaced or dropped part of the expression tree"
  let mut corpusQueries := 0
  for category in ["in_subqueries", "exists", "lateral", "using_joins", "natural_joins",
      "intersect", "except", "upsert", "insert_select", "nulls", "floating", "placeholders",
      "create_table", "alter_table", "drop_table"] do
    let source ← IO.FS.readFile s!"fixtures/advanced/{category}.sql"
    for line in source.splitOn "\n" do
      if line.trimAscii.toString.isEmpty then continue
      match ← expectOk category (Advanced.parse line) with
      | .query query =>
          for profile in [RenderContract.Profile.identityV01, .postgres16V01] do
            checked profile s!"{category}: {line}" query
          corpusQueries := corpusQueries + 1
      | _ => pure ()
  SQLean.Tests.assert (corpusQueries == 487) "advanced SELECT coverage count changed unexpectedly"
  pure (2 * (positiveQueries.length + invalidQueries.length + 5) + 6 + 2 * corpusQueries)

end SQLean.Tests
