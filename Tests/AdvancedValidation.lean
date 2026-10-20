import SQLean.AdvancedParser
import SQLean.AdvancedQueryValidation
import Tests.Support

namespace SQLean.Tests
open Advanced

private def advancedSchema : Schema := [
  ⟨"users", [⟨"id", .int⟩, ⟨"age", .int⟩, ⟨"name", .text⟩, ⟨"city", .text⟩]⟩,
  ⟨"orders", [⟨"id", .int⟩, ⟨"user_id", .int⟩, ⟨"amount", .int⟩, ⟨"status", .text⟩]⟩,
  ⟨"profiles", [⟨"id", .int⟩, ⟨"city", .text⟩, ⟨"rating", .nullable .real⟩]⟩]

private def typeCode : SqlType → String
  | .int => "i" | .text => "t" | .bool => "b" | .real => "r"
  | .opaque name => s!"[{name.name}]"
  | .array element => typeCode element ++ "[]"
  | .nullable type => (typeCode type).toUpper

private def acceptedAdvanced : List (String × String) := [
  ("WITH a AS(SELECT id FROM users),users AS(SELECT 'later'::TEXT id) SELECT id FROM a", "i"),
  ("WITH users AS(SELECT id FROM users) SELECT id FROM users", "i"),
  ("WITH RECURSIVE users AS(SELECT 'first'::TEXT id),a AS(SELECT id FROM users) SELECT id FROM a", "t"),
  ("SELECT SUM((SELECT u.id)) FROM users u", "I"),
  ("SELECT COUNT(*) FILTER(WHERE EXISTS(SELECT 1 WHERE u.id>0)) FROM users u", "i"),
  ("SELECT NULL IN(1,TRUE)", "B"),
  ("SELECT NULL BETWEEN 1 AND 2, 1 NOT BETWEEN NULL AND 2", "BB"),
  ("SELECT id BETWEEN 1 AND 2,COUNT(*) FROM users GROUP BY id BETWEEN 1 AND 2", "bi"),
  ("SELECT id,COUNT(*) FROM users GROUP BY - -1 ORDER BY - -1", "ii"),
  ("SELECT 1 AS n UNION SELECT 2 ORDER BY - -1", "i"),
  ("SELECT id FROM users ORDER BY +0.5", "i"),
  ("SELECT NULL", "T"),
  ("SELECT NULL::INTEGER, NULL::TEXT, NULL::BOOLEAN, NULL::REAL", "ITBR"),
  ("SELECT NULL + 1, 1 + NULL, NULL + 1.25, NULL = 1, NULL = NULL", "IIRBB"),
  ("SELECT NULL AND TRUE, NULL OR FALSE, NOT NULL, NULL IS NULL, NULL IS NOT NULL", "BBBbb"),
  ("SELECT NULL LIKE NULL, NULL ILIKE 'a%', MIN(NULL), MAX(NULL), COUNT(NULL), +NULL", "BBTTiR"),
  ("SELECT .5, 1., 1e3, 1.25e-3, -1.25E+4", "rrrrr"),
  ("SELECT id, EXISTS(SELECT NULL FROM orders o WHERE o.user_id=users.id) FROM users", "ib"),
  ("SELECT id, NOT EXISTS(SELECT 1 FROM orders o WHERE o.user_id=users.id) FROM users", "ib"),
  ("SELECT u.id IN (SELECT o.user_id FROM orders o WHERE o.amount>u.age) FROM users u", "b"),
  ("SELECT u.id NOT IN (SELECT o.user_id FROM orders o WHERE o.amount>u.age) FROM users u", "b"),
  ("SELECT NULL IN (SELECT id FROM users), NULL IN(1,NULL), 1 IN(NULL,2)", "BBB"),
  ("SELECT (SELECT id FROM users WHERE FALSE), (SELECT NULL)", "IT"),
  ("SELECT id, (SELECT COUNT(*) FROM orders o WHERE o.user_id=users.id) FROM users", "iI"),
  ("SELECT u.id, d.n FROM users u CROSS JOIN LATERAL (SELECT COUNT(*) n FROM orders o WHERE o.user_id=u.id) d", "ii"),
  ("SELECT u.id, d.n FROM users u LEFT JOIN LATERAL (SELECT COUNT(*) n FROM orders o WHERE o.user_id=u.id) d ON TRUE", "iI"),
  ("SELECT u.id, d.id FROM users u, LATERAL (SELECT u.id) d", "ii"),
  ("SELECT u.id, d.id FROM users u CROSS JOIN (SELECT id FROM profiles) d", "ii"),
  ("SELECT * FROM users u JOIN profiles p USING(id,city)", "ititR"),
  ("SELECT id,u.id,p.id,p.rating FROM users u LEFT JOIN profiles p USING(id)", "iiIR"),
  ("SELECT id,u.id,p.id,u.age FROM users u RIGHT JOIN profiles p USING(id)", "iIiI"),
  ("SELECT id,u.id,p.id,city FROM users u FULL JOIN profiles p USING(id,city)", "iIIt"),
  ("SELECT * FROM users NATURAL JOIN profiles", "ititR"),
  ("SELECT * FROM users NATURAL FULL JOIN profiles", "itITR"),
  ("SELECT id, COUNT(*) FROM users JOIN profiles USING(id) GROUP BY id", "ii"),
  ("SELECT users.id, COUNT(*) FROM users JOIN profiles USING(id) GROUP BY id", "ii"),
  ("SELECT u.id, COUNT(*) FROM users u CROSS JOIN profiles p GROUP BY u.id ORDER BY u.id", "ii"),
  ("SELECT u.id, EXISTS(SELECT 1 FROM orders o WHERE o.user_id=u.id) FROM users u GROUP BY u.id", "ib"),
  ("SELECT u.id, (SELECT COUNT(*) FROM orders o WHERE o.user_id=u.id) FROM users u GROUP BY u.id", "iI"),
  ("SELECT u.id + 1, COUNT(*) FROM users u GROUP BY u.id + 1", "ii"),
  ("SELECT u.id AS k, COUNT(*) FROM users u GROUP BY k ORDER BY 1", "ii"),
  ("SELECT COUNT(*) FROM users GROUP BY +1", "i"),
  ("SELECT COUNT(*) FILTER (WHERE age>1), SUM(age)::REAL FROM users", "iR"),
  ("SELECT DISTINCT ON(city) city,age FROM users ORDER BY city,age DESC NULLS LAST", "ti"),
  ("SELECT 1 AS x INTERSECT SELECT 2", "i"),
  ("SELECT 1 EXCEPT ALL SELECT 2", "i"),
  ("SELECT 1 AS x UNION SELECT NULL ORDER BY x", "I"),
  ("SELECT NULL INTERSECT SELECT 1", "I"),
  ("SELECT NULL EXCEPT SELECT NULL", "T"),
  ("SELECT 1.5 UNION SELECT 1", "r"),
  ("SELECT 1 AS x UNION (SELECT 2 INTERSECT SELECT 3) ORDER BY 1", "i"),
  ("WITH x AS(SELECT 1 n), y AS(SELECT n+1 n FROM x) SELECT n FROM y", "i"),
  ("WITH x(n) AS(SELECT 1) SELECT n FROM x", "i"),
  ("WITH x AS(SELECT NULL n) SELECT n FROM x", "T"),
  ("WITH RECURSIVE seq(n) AS(SELECT 1 UNION ALL SELECT n+1 FROM seq WHERE n<3) SELECT n FROM seq", "i"),
  ("WITH RECURSIVE seq(n) AS(SELECT NULL::INTEGER UNION ALL SELECT n FROM seq WHERE FALSE) SELECT n FROM seq", "I"),
  ("SELECT EXISTS(WITH x AS(SELECT users.id n) SELECT n FROM x) FROM users", "b"),
  ("SELECT x.a,x.city FROM users x(a)", "it"),
  ("SELECT d.a,d.b FROM (SELECT id,name FROM users) d(a,b)", "it"),
  ("SELECT 1 WHERE NULL", "i"),
  ("SELECT COUNT(*) FROM users HAVING NULL", "i"),
  ("SELECT u.id FROM users u JOIN profiles p ON NULL", "i"),
  ("SELECT COUNT(*) FILTER(WHERE NULL) FROM users", "i"),
  ("SELECT id IN (1.5, NULL), name IN (NULL, 'a') FROM users", "BB"),
  ("SELECT CAST(NULL AS NUMERIC(10,2)), CAST(1 AS BIGINT), CAST('x' AS VARCHAR(8))", "Rit"),
  ("SELECT users.* FROM users JOIN profiles USING(id)", "iitt"),
  ("SELECT profiles.* FROM users LEFT JOIN profiles USING(id)", "ITR"),
  ("SELECT 1 FROM users u WHERE EXISTS(SELECT 1 FROM profiles u WHERE u.id=1)", "i"),
  ("SELECT COUNT(*) FROM users WHERE EXISTS(SELECT COUNT(*) FROM profiles)", "i"),
  ("SELECT u.id FROM users u WHERE EXISTS(SELECT 1 FROM orders o WHERE EXISTS(SELECT 1 FROM profiles p WHERE p.id=u.id))", "i")]

private def rejectedAdvanced : List String := [
  "WITH RECURSIVE a AS(SELECT id FROM users),users AS(SELECT 'later'::TEXT id) SELECT id FROM a",
  "WITH RECURSIVE users AS(SELECT id FROM users) SELECT id FROM users",
  "WITH RECURSIVE a AS(SELECT id FROM profiles),profiles AS(SELECT 1 id) SELECT id FROM a",
  "SELECT u.age,EXISTS(SELECT COUNT(*) FILTER(WHERE EXISTS(SELECT 1 WHERE u.id>0))) FROM users u",
  "SELECT u.age,EXISTS(SELECT SUM((SELECT u.id))) FROM users u",
  "SELECT id,COUNT(*) FROM users GROUP BY id BETWEEN 1 AND 2",
  "SELECT id FROM users WHERE id BETWEEN 1 AND TRUE",
  "SELECT id FROM users ORDER BY -1",
  "SELECT id FROM users GROUP BY -1",
  "SELECT id FROM users ORDER BY 1.5",
  "SELECT id FROM users GROUP BY -1.5",
  "SELECT 1 UNION SELECT 2 ORDER BY -1",
  "SELECT id FROM missing",
  "SELECT missing FROM users",
  "SELECT u.missing FROM users u",
  "SELECT users.id FROM users u",
  "SELECT id FROM users u CROSS JOIN profiles p",
  "SELECT u.id FROM users u CROSS JOIN profiles u",
  "SELECT u.id FROM users u CROSS JOIN (SELECT u.id) d",
  "SELECT u.id FROM LATERAL (SELECT u.id) d CROSS JOIN users u",
  "SELECT u.id FROM users u RIGHT JOIN LATERAL (SELECT u.id) d ON TRUE",
  "SELECT u.id FROM users u FULL JOIN LATERAL (SELECT u.id) d ON TRUE",
  "SELECT EXISTS(SELECT u.age FROM profiles u) FROM users u",
  "SELECT id IN (SELECT id,amount FROM orders) FROM users",
  "SELECT name IN (SELECT amount FROM orders) FROM users",
  "SELECT 1 IN (SELECT NULL)",
  "SELECT (SELECT id,amount FROM orders)",
  "SELECT EXISTS(SELECT missing FROM orders)",
  "SELECT * FROM users JOIN profiles USING(missing)",
  "SELECT * FROM users JOIN profiles USING(id,id)",
  "SELECT * FROM users JOIN orders USING(name)",
  "SELECT * FROM users u JOIN (SELECT id::TEXT id FROM profiles) p USING(id)",
  "SELECT * FROM users u NATURAL JOIN (SELECT id::TEXT id FROM profiles) p",
  "SELECT * FROM users u JOIN (SELECT id,id FROM profiles) p USING(id)",
  "SELECT d.missing FROM (SELECT id FROM users) d",
  "SELECT * FROM users u(a,b,c,d,e)",
  "SELECT * FROM (SELECT 1) d(a,b)",
  "SELECT id,COUNT(*) FROM users",
  "SELECT city,COUNT(*) FROM users GROUP BY id",
  "SELECT COUNT(*) FROM users WHERE COUNT(*)>1",
  "SELECT id FROM users GROUP BY COUNT(*)",
  "SELECT SUM(COUNT(*)) FROM users",
  "SELECT u.id AS id,COUNT(*) FROM users u CROSS JOIN profiles p GROUP BY id",
  "SELECT u.id,EXISTS(SELECT 1 FROM orders o WHERE o.user_id=u.age) FROM users u GROUP BY u.id",
  "SELECT u.id,(SELECT COUNT(*) FROM orders o WHERE o.user_id=u.age) FROM users u GROUP BY u.id",
  "SELECT u.id+1,EXISTS(SELECT 1 FROM orders o WHERE o.user_id=u.id) FROM users u GROUP BY u.id+1",
  "SELECT u.age,EXISTS(SELECT SUM(u.id)) FROM users u",
  "SELECT u.age,EXISTS(SELECT COUNT(*) FILTER(WHERE u.id>0)) FROM users u",
  "SELECT id FROM users HAVING id>0",
  "SELECT COUNT(*) FROM users ORDER BY name",
  "SELECT DISTINCT city FROM users ORDER BY age",
  "SELECT DISTINCT ON(city) city FROM users ORDER BY age",
  "SELECT id FROM users GROUP BY 0",
  "SELECT id FROM users GROUP BY 2",
  "SELECT id FROM users GROUP BY TRUE",
  "SELECT id FROM users ORDER BY 0",
  "SELECT id FROM users ORDER BY 2",
  "SELECT id AS x,age AS x FROM users ORDER BY x",
  "SELECT 1 UNION SELECT 1,2",
  "SELECT 1 INTERSECT SELECT TRUE",
  "SELECT 1 EXCEPT SELECT 'x'",
  "SELECT NULL UNION SELECT NULL UNION SELECT 1",
  "SELECT 1 AS n UNION SELECT 2 ORDER BY n+1",
  "SELECT 1 AS n UNION SELECT 2 ORDER BY missing",
  "SELECT 1 AS n,1 AS n UNION SELECT 2,2 ORDER BY n",
  "WITH x AS(SELECT 1 n),x AS(SELECT 2 n) SELECT n FROM x",
  "WITH x AS(SELECT n FROM y),y AS(SELECT 1 n) SELECT n FROM x",
  "WITH x AS(SELECT 1 n,2 n) SELECT n FROM x",
  "WITH x(a,b) AS(SELECT 1) SELECT a FROM x",
  "WITH RECURSIVE seq(n) AS(SELECT n FROM seq) SELECT n FROM seq",
  "WITH RECURSIVE seq(n) AS(SELECT n FROM seq UNION ALL SELECT 1) SELECT n FROM seq",
  "WITH RECURSIVE seq(n) AS(SELECT 1 UNION ALL SELECT s.n FROM seq s CROSS JOIN seq t) SELECT n FROM seq",
  "WITH RECURSIVE seq(n) AS(SELECT 1 UNION ALL SELECT SUM(n) FROM seq) SELECT n FROM seq",
  "WITH RECURSIVE seq(n) AS(SELECT 1 UNION ALL SELECT n FROM seq GROUP BY n) SELECT n FROM seq",
  "WITH RECURSIVE seq(n) AS(SELECT 1 UNION ALL SELECT n::TEXT FROM seq) SELECT n FROM seq",
  "WITH RECURSIVE seq(n) AS(SELECT 1 UNION ALL SELECT NULL::INT FROM seq) SELECT n FROM seq",
  "WITH RECURSIVE seq(a,b) AS(SELECT 1,2 UNION ALL SELECT NULL::INT,a FROM seq) SELECT b FROM seq",
  "SELECT NULL+NULL",
  "SELECT -NULL",
  "SELECT SUM(NULL)",
  "SELECT AVG(NULL)",
  "SELECT NULL+TRUE",
  "SELECT 1 AND NULL",
  "SELECT NOT 1",
  "SELECT TRUE LIKE NULL",
  "SELECT 1 IN(TRUE,NULL)",
  "SELECT 1 WHERE 1",
  "SELECT 1 FROM users JOIN profiles ON 1",
  "SELECT COUNT(*) FILTER(WHERE 1) FROM users",
  "SELECT id FROM users WHERE SUM(age)>1",
  "SELECT TRUE::REAL",
  "SELECT $1",
  "SELECT ?",
  "SELECT $2+1"]

private def parameterCases : List (String × ParameterEnv × String) := [
  ("SELECT ? BETWEEN ? AND ?", [(1,.int),(2,.int),(3,.int)], "b"),
  ("SELECT $1", [(1, .int)], "i"),
  ("SELECT $1 + $1", [(1, .real)], "r"),
  ("SELECT $2, $1", [(1, .text), (2, .bool)], "bt"),
  ("SELECT $3", [(3, .nullable .int)], "I"),
  ("SELECT ?, ?", [(1, .int), (2, .text)], "it"),
  ("SELECT ? IN (SELECT id FROM users), ? IS NULL", [(1, .int), (2, .nullable .text)], "bb"),
  ("SELECT $1 + 1, $1 IN(NULL,1)", [(1, .nullable .int)], "IB"),
  ("SELECT EXISTS(SELECT 1 FROM users WHERE id=$1)", [(1, .int)], "b"),
  ("WITH x AS(SELECT ? n) SELECT n FROM x WHERE n>?", [(1, .int), (2, .int)], "i"),
  ("SELECT u.id,d.n FROM users u CROSS JOIN LATERAL (SELECT u.id+? n) d", [(1, .int)], "ii")]

private def manualAdvancedTests : IO Nat := do
  let nullQuery : Advanced.Query := { body := .select { items := [.expression .null] } }
  let intQuery : Advanced.Query := { body := .select { items := [.expression (.literal (.int 1))] } }
  let mixed : Advanced.Query := { body := .select { items := [
    .expression (.parameter (.numbered 1)), .expression (.parameter (.anonymous 2))] } }
  expectError "mixed parameter AST styles" (Advanced.checkQuery [] [(1,.int),(2,.int)] mixed)
  expectError "duplicate declared parameter" (Advanced.checkQuery [] [(1,.int),(1,.text)] intQuery)
  expectError "zero declared parameter" (Advanced.checkQuery [] [(0,.int)] intQuery)
  expectError "nested nullable parameter" (Advanced.checkQuery [] [(1,.nullable (.nullable .int))] intQuery)
  expectError "invalid schema" (Advanced.checkQuery [⟨"users",[]⟩] [] intQuery)
  expectError "fuel exhaustion" (checkQueryFuel 0 [] [] [] intQuery)
  expectError "recursive modifier without WITH" (Advanced.checkQuery [] [] { intQuery with recursive := true })
  expectError "conflicting distinct modes" (Advanced.checkQuery [] [] { body := .select {
    items := [.expression (.literal (.int 1))], distinct := true, distinctOn := [.literal (.int 1)] } })
  let _ ← expectOk "NULL contextual INSERT SELECT" (checkQueryAgainst [] [] nullQuery [.nullable .int])
  expectError "NULL cannot target nonnull" (checkQueryAgainst [] [] nullQuery [.int])
  let _ ← expectOk "numeric assignment" (checkQueryAgainst [] [] intQuery [.real])
  expectError "assignment arity" (checkQueryAgainst [] [] intQuery [.int,.int])
  expectError "assignment type" (checkQueryAgainst [] [] intQuery [.bool])
  expectError "invalid VARCHAR modifier AST" (inferExpr 20 [] [] [] false (.cast .null ⟨.varchar,[0]⟩))
  expectError "invalid INT modifier AST" (inferExpr 20 [] [] [] false (.cast .null ⟨.int,[5]⟩))
  expectError "repeated anonymous ordinal" (checkParameterUses [.anonymous 1,.anonymous 1])
  expectError "gapped anonymous ordinal" (checkParameterUses [.anonymous 2])
  expectError "reordered anonymous ordinals" (checkParameterUses [.anonymous 2,.anonymous 1])
  let badDecimals := ["", ".", "1", "-1.0", "+1.0", "1e", "1e+", "1e-", ".e1", "1.2.3", "1e2x", "nan", "Infinity", " 1.0"]
  for lexeme in badDecimals do
    expectError s!"malformed decimal AST {lexeme}" (inferExpr 20 [] [] [] false (.decimal lexeme))
  let goodDecimals := [".5", "0.", "1.25", "1e3", "1e-3", "1.2E+3", "000.125", "0e0"]
  for lexeme in goodDecimals do
    let type ← expectOk s!"decimal AST {lexeme}" (inferExpr 20 [] [] [] false (.decimal lexeme))
    SQLean.Tests.assert (type == some .real) "decimal must have real family"
  let parameterQuery ← expectOk "parameter query parsing" (Advanced.parseQuery "SELECT $1+1")
  expectError "parameter operator signature" (Advanced.checkQuery [] [(1,.text)] parameterQuery)
  let inferred ← expectOk "bare NULL stays unknown in expression API" (inferExpr 20 [] [] [] false .null)
  SQLean.Tests.assert inferred.isNone "NULL should not prematurely become text"
  SQLean.Tests.assert (assignmentCompatible none (.nullable .int)) "unknown NULL accepts nullable target"
  SQLean.Tests.assert (!assignmentCompatible (some (.nullable .int)) .int) "nullable cannot target nonnull"
  let scope := Scope.ofTable advancedSchema.head!
  let resolved ← expectOk "public scope helper" (resolveColumn [scope] (some "users") "id")
  SQLean.Tests.assert (resolved.1.type == .int && resolved.2 == 0) "scope helper resolves local binding"
  let proof ← expectOk "query certificate" (Advanced.certifyQuery [] [] intQuery)
  SQLean.Tests.assert (proof.val == [⟨"?column?",.int⟩]) "certificate exposes checked output"
  pure (24 + badDecimals.length + goodDecimals.length)

def advancedValidationTests : IO Nat := do
  for (sql, expected) in acceptedAdvanced do
    let query ← expectOk sql (Advanced.parseQuery sql)
    let columns ← expectOk sql (Advanced.checkQuery advancedSchema [] query)
    let actual := String.join (columns.map (fun c => typeCode c.type))
    SQLean.Tests.assert (actual == expected) s!"{sql}: expected {expected}, found {actual}"
  for sql in rejectedAdvanced do
    let query ← expectOk s!"negative syntax: {sql}" (Advanced.parseQuery sql)
    expectError sql (Advanced.checkQuery advancedSchema [] query)
  for (sql, params, expected) in parameterCases do
    let query ← expectOk sql (Advanced.parseQuery sql)
    let columns ← expectOk sql (Advanced.checkQuery advancedSchema params query)
    let actual := String.join (columns.map (fun c => typeCode c.type))
    SQLean.Tests.assert (actual == expected) s!"{sql}: expected {expected}, found {actual}"
  let manual ← manualAdvancedTests
  pure (acceptedAdvanced.length + rejectedAdvanced.length + parameterCases.length + manual)

example (schema : Schema) (params : ParameterEnv) (query : Advanced.Query) (columns : List ColumnDef)
    (checked : Advanced.checkQuery schema params query = .ok columns) :
    QueryValid schema params query columns := Advanced.checkQuery_sound checked

example : Advanced.QueryValid [] []
    { body := .select { items := [.expression (.binary .add .null (.literal (.int 1)))] } }
    [⟨"?column?", .nullable .int⟩] := by rfl

end SQLean.Tests
