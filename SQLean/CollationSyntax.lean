import SQLean.SyntaxBase

/-! Immutable collation snapshot data shared by catalog metadata and the
independent SELECT contract. Object identities are distinct from SQL names,
locale names, and claims about locale-dependent evaluation. -/
namespace SQLean

inductive CollationId where
  | databaseDefault
  | c
  | posix
  | custom (token : String)
  deriving Repr, BEq, DecidableEq, Inhabited

def CollationId.label : CollationId → String
  | .databaseDefault => "default"
  | .c => "C"
  | .posix => "POSIX"
  | .custom token => "custom:" ++ token

structure CollationEntry where
  id : CollationId
  schema : Name
  name : Name
  encoding : Option String := none
  deterministic : Bool := true
  exposeUnqualified : Bool := false
  deriving Repr, BEq, DecidableEq, Inhabited

/-- Visibility is supplied by the caller's native catalog snapshot. It is not
an implementation of search_path; in particular, temporary namespace aliases
are not silently resolved. The default profile asserts a UTF8 connection. -/
structure CollationEnv where
  encoding : String := "UTF8"
  entries : List CollationEntry := [
    ⟨.databaseDefault, "pg_catalog", "default", none, true, true⟩,
    ⟨.c, "pg_catalog", "C", none, true, true⟩,
    ⟨.posix, "pg_catalog", "POSIX", none, true, true⟩]
  deriving Repr, BEq, DecidableEq, Inhabited

def CollationEnv.builtin : CollationEnv := {}

def CollationEntry.eligible (entry : CollationEntry) (encoding : String) : Bool :=
  entry.encoding.isNone || entry.encoding == some encoding

def CollationEnv.lookup (env : CollationEnv) (name : List Name) : Option CollationEntry :=
  let named := fun entry : CollationEntry => match name with
    | [name] => entry.exposeUnqualified && entry.name == name
    | [schema, name] => entry.schema == schema && entry.name == name
    | _ => false
  (env.entries.find? fun entry => named entry && entry.encoding == some env.encoding).orElse
    (fun _ => env.entries.find? fun entry => named entry && entry.encoding.isNone)

def CollationEnv.lookupId (env : CollationEnv) (id : CollationId) : Option CollationEntry :=
  env.entries.find? fun entry => entry.id == id && entry.eligible env.encoding

def CollationEntry.WellFormed (entry : CollationEntry) : Prop :=
  entry.schema ≠ "" ∧ entry.name ≠ "" ∧
  (∀ encoding ∈ entry.encoding, encoding ≠ "") ∧
  (match entry.id with
    | .databaseDefault => entry.schema = "pg_catalog" ∧ entry.name = "default"
    | .c => entry.schema = "pg_catalog" ∧ entry.name = "C" ∧ entry.deterministic = true
    | .posix => entry.schema = "pg_catalog" ∧ entry.name = "POSIX" ∧ entry.deterministic = true
    | .custom token => token ≠ "")

instance (entry : CollationEntry) : Decidable entry.WellFormed := by
  unfold CollationEntry.WellFormed
  cases entry.id <;> infer_instance

/-- Distinct encoding-specific objects may share a SQL name. Uniqueness is
required separately at each encoding; lookup prefers the current encoding over
the encoding-independent fallback, as PostgreSQL's namespace lookup does. -/
def CollationEnv.WellFormed (env : CollationEnv) : Prop :=
  env.encoding ≠ "" ∧
  (env.entries.map CollationEntry.id).Nodup ∧
  (env.entries.map (fun entry => (entry.schema, entry.name, entry.encoding))).Nodup ∧
  ((env.entries.filter (·.exposeUnqualified)).map
    (fun entry => (entry.name, entry.encoding))).Nodup ∧
  (∀ entry ∈ env.entries, entry.WellFormed) ∧
  (∃ entry ∈ env.entries, entry.id = .databaseDefault ∧ entry.eligible env.encoding = true) ∧
  (∃ entry ∈ env.entries, entry.id = .c ∧ entry.eligible env.encoding = true) ∧
  (∃ entry ∈ env.entries, entry.id = .posix ∧ entry.eligible env.encoding = true)

instance (env : CollationEnv) : Decidable env.WellFormed := by
  unfold CollationEnv.WellFormed
  infer_instance

/-- Native derivation strength is lost at a query boundary. `none` and
`conflict` are different: an indeterminate stored column re-enters as `none`. -/
inductive CollationDerivation where
  | none
  | implicit (id : CollationId)
  | explicit (id : CollationId)
  | conflict (left right : CollationId)
  deriving Repr, BEq, DecidableEq, Inhabited

def CollationDerivation.identity : CollationDerivation → Option CollationId
  | .implicit id | .explicit id => some id
  | .none | .conflict .. => Option.none

def CollationDerivation.stored : Option CollationId → CollationDerivation
  | Option.none => .none
  | some id => .implicit id

/-- `none` here denotes incompatible explicit identities (an analysis error).
An implicit conflict is a successful derivation with indeterminate identity. -/
def CollationDerivation.merge : CollationDerivation → CollationDerivation →
    Option CollationDerivation
  | .explicit a, .explicit b => if a = b then some (.explicit a) else Option.none
  | .explicit a, _ | _, .explicit a => some (.explicit a)
  | .conflict a b, _ | _, .conflict a b => some (.conflict a b)
  | .none, other | other, .none => some other
  | .implicit a, .implicit b =>
      if a = b then some (.implicit a)
      else if a = .databaseDefault then some (.implicit b)
      else if b = .databaseDefault then some (.implicit a)
      else some (.conflict a b)

def CollationDerivation.mergeList : List CollationDerivation → Option CollationDerivation
  | [] => some .none
  | head :: tail => tail.foldlM CollationDerivation.merge head

def CollationDerivation.determinate : CollationDerivation → Bool
  | .conflict .. => false
  | _ => true

end SQLean
