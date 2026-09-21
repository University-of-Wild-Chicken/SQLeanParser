import SQLean

/-! Small, kernel-checked examples clients can adapt to their own queries. -/
namespace SQLean.Tests

def proofSchema : Schema := [⟨"users", [⟨"id", .int⟩, ⟨"name", .text⟩]⟩]

def proofQuery : Query := ⟨"users",
  [.column "name", .binary .add (.column "id") (.literal (.int 1))],
  some (.binary .ge (.column "id") (.literal (.int 18)))⟩

example : ValidQuery proofSchema proofQuery [.text, .int] :=
  checkQuery_sound proofSchema proofQuery [.text, .int] rfl

example (schema : Schema) (query : Query) (certificate : CertifiedQuery schema query) :
    query.selectList.length = certificate.outputTypes.length :=
  certificate.valid.output_arity

example (schema : Schema) (query : Query) (types : List SqlType) :
    checkQuery schema query = .ok types ↔ ValidQuery schema query types :=
  checkQuery_iff schema query types

end SQLean.Tests
