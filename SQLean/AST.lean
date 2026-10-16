import SQLean.SyntaxBase
import SQLean.AdvancedSyntax

namespace SQLean

inductive Statement where
  | select (query : SelectQuery)
  | insert (query : InsertQuery)
  | update (query : UpdateQuery)
  | delete (query : DeleteQuery)
  | relational (query : RelQuery)
  | returning (mutation : Mutation) (items : List SelectItem)
  | extended (statement : Advanced.Statement)
  deriving Repr, BEq, Inhabited

def Mutation.toStatement : Mutation → Statement
  | .insert query => .insert query
  | .update query => .update query
  | .delete query => .delete query

end SQLean
