import SQLean.SelectContract.ScalarSignatures

/-! Normative PostgreSQL collation coercions. These local rules do not infer
expression types, consult executable query checkers, or evaluate locale rules. -/
namespace SQLean.SelectContract
open Advanced

/-- Unknown literals receive the target's typcollation when converted. A
COLLATE wrapper remains explicit through a collatable conversion and disappears
through conversion to a noncollatable target. Known inputs preserve provenance
through collatable casts, including TEXT-to-NAME and NAME-to-TEXT. -/
def coercedCollation (expr : Advanced.Expr) (input : ExprType) (target : ScalarType)
    (derivation : CollationDerivation) : CollationDerivation :=
  match expr with
  | .collate arg _ =>
      if target.collatable then derivation
      else coercedCollation arg input target .none
  | _ => match scalarInput expr input with
    | .unknown _ => .stored target.defaultCollation
    | .known source =>
      if source.base = target then derivation
      else target.collationResult derivation

def coercedCollations : List Advanced.Expr → List ExprType → List CollationDerivation →
    List ScalarType → Option (List CollationDerivation)
  | [], [], [], [] => some []
  | expr :: exprs, type :: types, derivation :: derivations, target :: targets =>
      (coercedCollations exprs types derivations targets).map
        (coercedCollation expr type target derivation :: ·)
  | _, _, _, _ => none

def contextualCollations : List Advanced.Expr → List ExprType → List CollationDerivation →
    List (Option ScalarType) → Option (List CollationDerivation)
  | [], [], [], [] => some []
  | expr :: exprs, type :: types, derivation :: derivations, target :: targets =>
      (contextualCollations exprs types derivations targets).map
        ((match target with
          | none => derivation
          | some target => coercedCollation expr type target derivation) :: ·)
  | _, _, _, _ => none

def ownCollationTargets (types : List ExprType) : List (Option ScalarType) :=
  types.map (fun type => type.map ExactType.base)

def concreteCollationTargets (types : List ScalarType) : List (Option ScalarType) :=
  types.map some

def resultCollation (type : ExprType) (input : CollationDerivation) : CollationDerivation :=
  match type with
  | none => .none
  | some type => type.base.collationResult input

def projectedCollation (expr : Advanced.Expr) (type : ExprType)
    (derivation : CollationDerivation) : Option CollationId :=
  (coercedCollation expr type (projectedType type).base derivation).identity

/-- Unknown expressions that PostgreSQL can identify during SQL99 ordering.
The literal payload and every COLLATE wrapper remain distinct; resolved object
identities normalize qualified and unqualified spellings of the same object. -/
abbrev UnknownSortValue := Option String × List CollationId

def unknownCollationSortKey (profile : Profile) : Advanced.Expr → Option UnknownSortValue
  | .null => some (none, [])
  | .literal (.text value) => some (some value, [])
  | .collate arg name => do
      let key ← unknownCollationSortKey profile arg
      let entry ← profile.collations.lookup name
      some (key.1, entry.id :: key.2)
  | _ => none

/-- Query metadata remembers UNKNOWN wrappers because native set analysis
coerces raw Const/Param unknowns, but does not replace a CollateExpr operand. -/
inductive PendingOrigin where
  | known | unknownConstant | unknownWrapper
  deriving Repr, BEq, DecidableEq, Inhabited

def pendingOrigin (expr : Advanced.Expr) (type : ExprType) : PendingOrigin :=
  match scalarInput expr type with
  | .known _ => .known
  | .unknown _ => match expr with
    | .null | .literal (.text _) => .unknownConstant
    | _ => .unknownWrapper

def pendingCoercion (origin : PendingOrigin) (input : ScalarInput)
    (derivation : CollationDerivation) (target : ScalarType) : CollationDerivation :=
  match origin, input with
  | .unknownWrapper, .unknown _ => derivation
  | _, .unknown _ => .stored target.defaultCollation
  | _, .known source =>
      if source.base = target then derivation else target.collationResult derivation

def caseOperandType (type : ExprType) (expr : Advanced.Expr) : ExactType :=
  match scalarInput expr type with
  | .unknown nullable => ⟨.text, nullable⟩
  | .known type => type

def knownCoercedCollation (source target : ScalarType)
    (derivation : CollationDerivation) : CollationDerivation :=
  if source = target then derivation else target.collationResult derivation

def substringCollationTargets (form : SubstringForm) (inputs : List ScalarType) :
    Option (List ScalarType) :=
  match form, inputs with
  | .from, [a, b] => some [a, b]
  | .fromFor, [a, b, c] | .similar, [a, b, c] => some [a, b, c]
  | .forFrom, [a, b, c] => some [a, c, b]
  | .forOnly, [a, .int32, .int32] => some [a, .int32]
  | _, _ => none

def substringCollationOrder (form : SubstringForm) (inputs : List CollationDerivation) :
    List CollationDerivation :=
  match form, inputs with
  | .forFrom, [a, b, c] => [a, c, b]
  | .forOnly, [a, b] => [a, .none, b]
  | _, inputs => inputs

def tableColumnCollation (table : CatalogTable) (column : Advanced.Column)
    (base : ScalarType) : Option CollationId :=
  match table.columnCollations.find? (fun entry => entry.1 == column.name) with
  | some entry => some entry.2
  | none => base.defaultCollation

/-- JOIN/USING chooses an uncoerced Var for an inner join when possible.
Outer one-sided joins choose that side; FULL constructs COALESCE. -/
def mergedKeyCollation (kind : JoinKind) (left right : OutputColumn) (base : ScalarType) :
    Option (Option CollationId) :=
  let ld := knownCoercedCollation left.type.base base (.stored left.collation)
  let rd := knownCoercedCollation right.type.base base (.stored right.collation)
  match kind with
  | .left => some ld.identity
  | .right => some rd.identity
  | .full => (CollationDerivation.merge ld rd).map (fun d => (base.collationResult d).identity)
  | _ => some (if left.type.base = base then ld.identity
      else if right.type.base = base then rd.identity else ld.identity)

def CollationEnvironment (profile : Profile) (catalog : Catalog) : Prop :=
  profile.collations.WellFormed ∧
  (∀ table ∈ catalog,
    (table.columnCollations.map Prod.fst).Nodup ∧
    (∀ entry ∈ table.columnCollations,
      (∃ column ∈ table.columns, column.name = entry.1 ∧
        (concreteType column.type).any ScalarType.collatable = true) ∧
      profile.collations.lookupId entry.2 ≠ none))

instance (profile : Profile) (catalog : Catalog) : Decidable (CollationEnvironment profile catalog) := by
  unfold CollationEnvironment
  infer_instance

/- Level-zero Var-free expressions form the scalar-array subset of IN.
Uncorrelated SubLinks have no parent-level Vars; their test expression is
still visited for scalar IN. -/
mutual
  def collationNoVarExpr (expr : Advanced.Expr) : Bool :=
    match expr with
    | .literal _ | .null | .decimal _ | .parameter _ => true
    | .column .. => false
    | .contextValue _ => true
    | .collate arg _ => collationNoVarExpr arg
    | .cast arg _ => collationNoVarExpr arg
    | .binary _ left right | .concat left right | .distinctFrom left right _
    | .pattern left right _ | .regex left right _ _ | .jsonAccess _ left right
    | .jsonExistence _ left right | .containment left right _ | .overlap left right
    | .quantifiedComparison _ _ left right | .nullIf left right
    | .filteredAggregate left right => collationNoVarExpr left && collationNoVarExpr right
    | .unary _ arg | .aggregate _ arg _ | .isNull arg _ | .extract _ arg => collationNoVarExpr arg
    | .array args | .row args | .substring _ args | .coalesce args | .greatest args | .least args =>
      collationNoVarExprs args
    | .call _ args => collationNoVarExprs args
    | .namedCall _ args => collationNoVarArguments args
    | .subscript base indices => collationNoVarExpr base && collationNoVarSubscripts indices
    | .caseExpr operand branches otherwise =>
      (match operand with | none => true | some value => collationNoVarExpr value) &&
      collationNoVarBranches branches &&
      (match otherwise with | none => true | some value => collationNoVarExpr value)
    | .inList arg values => collationNoVarExpr arg && collationNoVarExprs values
    | .between arg lower upper _ => collationNoVarExpr arg && collationNoVarExpr lower && collationNoVarExpr upper
    | .countAll => true
    | .exists _ | .scalarQuery _ => true
    | .inQuery arg _ => collationNoVarExpr arg
  termination_by sizeOf expr
  decreasing_by all_goals (simp_all <;> omega)

  def collationNoVarExprs (exprs : List Advanced.Expr) : Bool :=
    match exprs with
    | [] => true
    | head :: tail => collationNoVarExpr head && collationNoVarExprs tail
  termination_by sizeOf exprs
  decreasing_by all_goals (simp_all <;> omega)

  def collationNoVarArguments (args : List CallArgument) : Bool :=
    match args with
    | [] => true
    | .positional value :: tail | .named _ value _ :: tail =>
      collationNoVarExpr value && collationNoVarArguments tail
  termination_by sizeOf args
  decreasing_by all_goals (simp_all <;> omega)

  def collationNoVarSubscripts (indices : List Subscript) : Bool :=
    match indices with
    | [] => true
    | .index value :: tail => collationNoVarExpr value && collationNoVarSubscripts tail
    | .slice lower upper :: tail =>
      (match lower with | none => true | some value => collationNoVarExpr value) &&
      (match upper with | none => true | some value => collationNoVarExpr value) && collationNoVarSubscripts tail
  termination_by sizeOf indices
  decreasing_by all_goals (simp_all <;> omega)

  def collationNoVarBranches (branches : List (Advanced.Expr × Advanced.Expr)) : Bool :=
    match branches with
    | [] => true
    | (condition, value) :: tail => collationNoVarExpr condition && collationNoVarExpr value && collationNoVarBranches tail
  termination_by sizeOf branches
  decreasing_by all_goals (simp_all <;> omega)
end

def inCollationArguments (exprs : List Advanced.Expr) (types : List ExprType)
    (derivations : List CollationDerivation) : List (Advanced.Expr × ExprType × CollationDerivation) :=
  exprs.zip (types.zip derivations)

def inConstantArguments (exprs : List Advanced.Expr) (types : List ExprType)
    (derivations : List CollationDerivation) :=
  (inCollationArguments exprs types derivations).filter (fun row => collationNoVarExpr row.1)

def inVariableArguments (exprs : List Advanced.Expr) (types : List ExprType)
    (derivations : List CollationDerivation) :=
  (inCollationArguments exprs types derivations).filter (fun row => !collationNoVarExpr row.1)

end SQLean.SelectContract
