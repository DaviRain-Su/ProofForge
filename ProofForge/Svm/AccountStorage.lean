import ProofForge.Core.Ops

namespace ProofForge.Svm.AccountStorage

/-- Persistent container indexes are explicit. Sokoban nodes are one-based and reserve zero as
the null sentinel; ordinary vectors use zero-based indexes. -/
inductive IndexBase where
  | zero
  | one
  deriving BEq, Repr, Inhabited

/-- Static authorization attached to an account-resident region. Persistent container writes must
target a writable account owned by the current program. -/
structure Access where
  writable : Bool := false
  currentProgramOwned : Bool := false
  deriving BEq, Repr, Inhabited

/-- A fixed-capacity, fixed-stride account-data region. No runtime offset, capacity, allocation,
or pointer is represented by this descriptor. -/
structure Region where
  account : Nat
  baseWord : Nat
  strideWords : Nat
  capacity : Nat
  indexBase : IndexBase := .zero
  access : Access := {}
  deriving BEq, Repr, Inhabited

/-- One statically selected field inside every element of a region. Multiword keys and values are
represented by adjacent fields rather than copied nodes. -/
structure Field where
  region : Region
  offsetWords : Nat := 0
  widthWords : Nat := 1
  deriving BEq, Repr, Inhabited

/-- The final byte of a selected u64 word must fit in a u64 account `data_len`. -/
def maxDataWord : Nat := 2305843009213693951

def Region.wellFormed (region : Region) (accountLimit : Nat := 64) : Bool :=
  region.account < accountLimit && region.capacity > 0 && region.strideWords > 0 &&
    region.baseWord < maxDataWord &&
    region.baseWord + region.strideWords * (region.capacity - 1) < maxDataWord

def Field.wellFormed (field : Field) (accountLimit : Nat := 64) : Bool :=
  field.region.wellFormed accountLimit && field.widthWords > 0 &&
    field.offsetWords + field.widthWords ≤ field.region.strideWords &&
    field.region.baseWord + field.offsetWords +
      field.region.strideWords * (field.region.capacity - 1) + field.widthWords - 1 < maxDataWord

def Field.firstWord (field : Field) : Nat :=
  field.region.baseWord + field.offsetWords

/-- Transitive account effects are data, not an emitter-side list of operation constructors. -/
structure EffectSummary where
  reads : Array Nat := #[]
  writes : Array Nat := #[]
  deriving BEq, Repr, Inhabited

private def pushUnique (items : Array Nat) (item : Nat) : Array Nat :=
  if items.contains item then items else items.push item

def EffectSummary.merge (left right : EffectSummary) : EffectSummary :=
  { reads := right.reads.foldl pushUnique left.reads
    writes := right.writes.foldl pushUnique left.writes }

def EffectSummary.forField (field : Field) : EffectSummary :=
  let account := field.region.account
  { reads := #[account]
    writes := if field.region.access.writable then #[account] else #[] }

/-- Two fixed-stride one-based fields traversed as a bounded parent path. The fields may begin at
different static words but must describe the same account, stride, capacity, indexing, and access
requirements. -/
structure ParentPath where
  links : Field
  parentColor : Field
  maxDepth : Nat
  deriving BEq, Repr, Inhabited

private def Region.sameShape (left right : Region) : Bool :=
  left.account == right.account && left.strideWords == right.strideWords &&
    left.capacity == right.capacity && left.indexBase == right.indexBase &&
    left.access == right.access

def ParentPath.wellFormed (path : ParentPath) (accountLimit : Nat := 64) : Bool :=
  path.links.wellFormed accountLimit && path.parentColor.wellFormed accountLimit &&
    path.links.widthWords == 1 && path.parentColor.widthWords == 1 &&
    path.links.region.sameShape path.parentColor.region &&
    path.links.region.strideWords < maxDataWord &&
    path.links.region.indexBase == .one && !path.links.region.access.writable &&
    !path.links.region.access.currentProgramOwned &&
    path.maxDepth > 0 && path.maxDepth ≤ 64

/-- Account-resident routines that return one scalar. Dynamic operands remain ordinary Core
operands; this target-owned descriptor contains only static bounded geometry. -/
inductive Query where
  | parentPathValid (path : ParentPath)
  deriving BEq, Repr, Inhabited

def Query.arity : Query → Nat
  | .parentPathValid .. => 3

def Query.effects : Query → EffectSummary
  | .parentPathValid path =>
      (EffectSummary.forField path.links).merge (EffectSummary.forField path.parentColor)

def Query.wellFormed (accountLimit : Nat := 64) : Query → Bool
  | .parentPathValid path => path.wellFormed accountLimit

def Query.needsWalk (query : Query) : Bool :=
  query.effects.reads.any (· ≥ 1)

def Query.minAccounts (measure : V → Nat) (operands : Array V) (query : Query) : Nat :=
  let fromRegions := query.effects.reads.foldl (init := 0) fun current account =>
    Nat.max current (account + 1)
  operands.foldl (init := fromRegions) fun current value => Nat.max current (measure value)

/-- Stable target-IR spelling. The compatibility constructor below preserves the original
`accDataParentPathValid` digest. -/
def Query.canonical (renderValue : V → String) (operands : Array V) : Query → String
  | .parentPathValid path =>
      let region := path.links.region
      s!"dpp.{region.account}.{path.links.firstWord}.{path.parentColor.firstWord}." ++
        s!"{region.strideWords}.{region.capacity}.{path.maxDepth}" ++
        s!"({String.intercalate "," (operands.map renderValue).toList})"

def Query.parentPathValidOneBased
    (account linksBaseWord parentBaseWord strideWords capacity maxDepth : Nat) : Query :=
  let access : Access := {}
  .parentPathValid
    { links :=
        { region :=
            { account, baseWord := linksBaseWord, strideWords, capacity
              indexBase := .one, access } }
      parentColor :=
        { region :=
            { account, baseWord := parentBaseWord, strideWords, capacity
              indexBase := .one, access } }
      maxDepth }

/-- Stable SVM-to-storage bridge. New bounded allocators, trees, maps, and queues extend this
target-owned call vocabulary instead of adding another top-level SVM IR constructor and another
case to the main emitter. -/
inductive Call (V : Type) where
  | writeWord (field : Field) (index value : V)
  deriving BEq, Repr, Inhabited

def Call.mapValues (mapValue : α → β) : Call α → Call β
  | .writeWord field index value => .writeWord field (mapValue index) (mapValue value)

def Call.mapValuesM [Monad m] (mapValue : α → m β) : Call α → m (Call β)
  | .writeWord field index value =>
      return .writeWord field (← mapValue index) (← mapValue value)

def Call.values : Call V → Array V
  | .writeWord _ index value => #[index, value]

def Call.anyValue (predicate : V → Bool) (call : Call V) : Bool :=
  call.values.any predicate

def Call.allValues (predicate : V → Bool) (call : Call V) : Bool :=
  call.values.all predicate

def Call.foldValues (initial : Nat) (measure : V → Nat) (call : Call V) : Nat :=
  call.values.foldl (init := initial) fun current value => Nat.max current (measure value)

def Call.effects : Call V → EffectSummary
  | .writeWord field _ _ => EffectSummary.forField field

def Call.minAccounts (measure : V → Nat) (call : Call V) : Nat :=
  let fromRegions := call.effects.reads.foldl (init := 0) fun current account =>
    Nat.max current (account + 1)
  call.foldValues fromRegions measure

def Call.wellFormed (valueWellFormed : V → Bool) (accountLimit : Nat := 64) : Call V → Bool
  | .writeWord field index value =>
      field.wellFormed accountLimit && field.widthWords == 1 &&
        field.region.account > 0 && field.region.access.writable &&
        field.region.access.currentProgramOwned &&
        valueWellFormed index && valueWellFormed value

/-- Stable target-IR spelling. Storage routine details stay behind this API so generic target
plumbing does not need to know the `Call` constructors. -/
def Call.canonical (renderValue : V → String) : Call V → String
  | .writeWord field index value =>
      let opcode := match field.region.indexBase with | .zero => "dws" | .one => "dws1"
      s!"{opcode}.{field.region.account}.{field.firstWord}.{field.region.strideWords}." ++
        s!"{field.region.capacity}({renderValue index},{renderValue value})"

def Call.writeWordZeroBased (account baseWord strideWords capacity : Nat)
    (index value : V) : Call V :=
  .writeWord
    { region :=
        { account, baseWord, strideWords, capacity
          indexBase := .zero
          access := { writable := true, currentProgramOwned := true } } }
    index value

end ProofForge.Svm.AccountStorage
