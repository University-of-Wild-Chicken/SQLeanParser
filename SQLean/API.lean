import SQLean.Parser
import SQLean.Validation
import SQLean.CRUDValidation

namespace SQLean

inductive QueryError where
  | parse (error : ParseError)
  | validation (error : ValidationError)
  deriving Repr

instance : ToString QueryError where
  toString
    | .parse error => s!"parse error: {error}"
    | .validation error => s!"validation error: {error}"

/-- A parsed AST packaged with its schema-dependent validity certificate. -/
structure CheckedQuery (schema : Schema) where
  query : Query
  certificate : CertifiedQuery schema query

/-- Parse a single query and certify its static validity against a supplied schema. -/
def parseAndValidate (schema : Schema) (source : String) :
    Except QueryError (CheckedQuery schema) := do
  let query ← (parseQuery source).mapError QueryError.parse
  let certificate ← (certifyQuery schema query).mapError QueryError.validation
  pure ⟨query, certificate⟩

/-- A parsed SQL statement and its certificate against the exact supplied schema. -/
structure CheckedStatement (schema : Schema) where
  statement : Statement
  certificate : CertifiedStatement schema statement

/-- Parse and certify SELECT, INSERT, UPDATE, or DELETE, including RETURNING. The original
`parseAndValidate` function retains its strict SELECT-only grammar.
-/
def parseAndValidateStatement (schema : Schema) (source : String) :
    Except QueryError (CheckedStatement schema) := do
  let statement ← (parseStatement source).mapError QueryError.parse
  let certificate ← (certifyStatement schema statement).mapError QueryError.validation
  pure ⟨statement, certificate⟩

/-- A relational AST with named result types and its static validity derivation. -/
structure CheckedRelQuery (schema : Schema) where
  query : RelQuery
  certificate : CertifiedRelQuery schema query

/-- Parse and certify a SELECT using the uniform relational AST, including WITH,
recursive CTEs, and UNION. The certificate concerns static validity, not execution
termination or the contents of the database. -/
def parseAndValidateRelQuery (schema : Schema) (source : String) :
    Except QueryError (CheckedRelQuery schema) := do
  let query ← (parseRelQuery source).mapError QueryError.parse
  let certificate ← (certifyRelQuery schema query).mapError QueryError.validation
  pure ⟨query, certificate⟩

/-- The uniform advanced interface carries catalog effects and an explicit
parameter environment. Its proof attests the bounded executable static check. -/
structure CheckedAdvancedStatement (catalog : Advanced.Catalog) (params : Advanced.ParameterEnv) where
  statement : Advanced.Statement
  result : Advanced.StatementResult
  checked : Advanced.checkStatementDetailed catalog params statement = .ok result

def parseAndValidateAdvanced (catalog : Advanced.Catalog) (params : Advanced.ParameterEnv)
    (source : String) : Except QueryError (CheckedAdvancedStatement catalog params) := do
  let statement ← (Advanced.parse source).mapError QueryError.parse
  match h : Advanced.checkStatementDetailed catalog params statement with
  | .error error => .error (.validation error)
  | .ok result => .ok ⟨statement, result, h⟩

end SQLean
