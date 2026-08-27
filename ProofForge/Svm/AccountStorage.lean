import ProofForge.Core.Ops
import ProofForge.Attr

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

/-- Standard write authorization for account data owned by the executing program. -/
@[pf_inline] def Access.programOwnedMutable : Access :=
  { writable := true, currentProgramOwned := true }

/-- One scalar account word. Protocol layouts supply the account and word, while the SDK owns the
fixed-region descriptor shape. -/
@[pf_inline] def Field.scalar (account word : Nat)
    (access : Access := Access.programOwnedMutable) : Field :=
  { region := { account, baseWord := word, strideWords := 1, capacity := 1, access } }

/-- One word in every slot of a fixed-capacity one-based account-resident record array. -/
@[pf_inline] def Field.oneBased (account word stride capacity : Nat)
    (access : Access := Access.programOwnedMutable) : Field :=
  { region :=
      { account, baseWord := word, strideWords := stride, capacity
        indexBase := .one, access } }

/-- The final byte of a selected u64 word must fit in a u64 account `data_len`. -/
def maxDataWord : Nat := 2305843009213693951

def Region.wellFormed (region : Region) (accountLimit : Nat := 64) : Bool :=
  region.account < accountLimit && region.capacity > 0 && region.strideWords > 0 &&
    region.strideWords < maxDataWord && region.baseWord < maxDataWord &&
    region.baseWord + region.strideWords * (region.capacity - 1) < maxDataWord

def Field.wellFormed (field : Field) (accountLimit : Nat := 64) : Bool :=
  field.region.wellFormed accountLimit && field.widthWords > 0 &&
    field.offsetWords + field.widthWords ≤ field.region.strideWords &&
    field.region.baseWord + field.offsetWords +
      field.region.strideWords * (field.region.capacity - 1) + field.widthWords - 1 < maxDataWord

@[pf_inline] def Field.firstWord (field : Field) : Nat :=
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

def Region.sameShape (left right : Region) : Bool :=
  left.account == right.account && left.strideWords == right.strideWords &&
    left.capacity == right.capacity && left.indexBase == right.indexBase &&
    left.access == right.access

/-- A mutable scalar field in a one-based fixed record array. Higher-level SDK structures use this
predicate to validate their own record schemas without reimplementing region checks. -/
def Field.mutableOneBasedWord (field : Field) (accountLimit : Nat := 64) : Bool :=
  field.wellFormed accountLimit && field.widthWords == 1 &&
    field.region.indexBase == .one && field.region.access == Access.programOwnedMutable

def ParentPath.wellFormed (path : ParentPath) (accountLimit : Nat := 64) : Bool :=
  path.links.wellFormed accountLimit && path.parentColor.wellFormed accountLimit &&
    path.links.widthWords == 1 && path.parentColor.widthWords == 1 &&
    path.links.region.sameShape path.parentColor.region &&
    path.links.region.strideWords < maxDataWord &&
    path.links.region.indexBase == .one && !path.links.region.access.writable &&
    !path.links.region.access.currentProgramOwned &&
    path.maxDepth > 0 && path.maxDepth ≤ 64

/-- Shared account-resident red-black-tree topology. Links and packed parent/color fields use the
same one-based fixed-capacity region; key shape and traversal policy are supplied by a query. -/
structure RbTree where
  links : Field
  parentColor : Field
  deriving BEq, Repr, Inhabited

/-- Fixed traversal bound shared by account-resident RB search and validation routines. -/
def rbTreeTraversalDepth : Nat := 64

def RbTree.wellFormed (tree : RbTree) (maxCapacity : Nat) (accountLimit : Nat := 64) : Bool :=
  tree.links.wellFormed accountLimit && tree.parentColor.wellFormed accountLimit &&
    tree.links.widthWords == 1 && tree.parentColor.widthWords == 1 &&
    tree.links.region.sameShape tree.parentColor.region &&
    tree.links.region.strideWords < maxDataWord &&
    tree.links.region.indexBase == .one && tree.links.region.capacity ≤ maxCapacity &&
    tree.links.firstWord ≤ tree.parentColor.firstWord &&
    tree.parentColor.firstWord < tree.links.firstWord + tree.links.region.strideWords

def RbTree.hasAccess (tree : RbTree) (access : Access) : Bool :=
  tree.links.region.access == access

/-- Static fields of a fixed-capacity Phoenix FIFO red-black tree. The validator traverses live
nodes in place and then follows the allocator free list; neither phase allocates or copies nodes. -/
structure FifoRbTree where
  topology : RbTree
  price : Field
  sequence : Field
  bid : Bool
  deriving BEq, Repr, Inhabited

@[pf_inline] def FifoRbTree.links (tree : FifoRbTree) : Field := tree.topology.links
@[pf_inline] def FifoRbTree.parentColor (tree : FifoRbTree) : Field := tree.topology.parentColor

def FifoRbTree.wellFormed (tree : FifoRbTree) (accountLimit : Nat := 64) : Bool :=
  tree.topology.wellFormed 4096 accountLimit && tree.price.wellFormed accountLimit &&
    tree.sequence.wellFormed accountLimit &&
    tree.price.widthWords == 1 && tree.sequence.widthWords == 1 &&
    tree.links.region.sameShape tree.price.region &&
    tree.links.region.sameShape tree.sequence.region

@[pf_inline] def FifoRbTree.oneBased
    (account linksBaseWord parentBaseWord priceBaseWord sequenceBaseWord strideWords capacity : Nat)
    (bid : Bool) (access : Access := {}) : FifoRbTree :=
  { topology :=
      { links :=
          { region :=
              { account, baseWord := linksBaseWord, strideWords, capacity
                indexBase := .one, access } }
        parentColor :=
          { region :=
              { account, baseWord := parentBaseWord, strideWords, capacity
                indexBase := .one, access } } }
    price :=
      { region :=
          { account, baseWord := priceBaseWord, strideWords, capacity
            indexBase := .one, access } }
    sequence :=
      { region :=
          { account, baseWord := sequenceBaseWord, strideWords, capacity
            indexBase := .one, access } }
    bid }

/-- Static fields of a fixed-capacity red-black tree ordered by four consecutive account words. -/
structure Key4RbTree where
  topology : RbTree
  key : Field
  lastKey : Field
  deriving BEq, Repr, Inhabited

@[pf_inline] def Key4RbTree.links (tree : Key4RbTree) : Field := tree.topology.links
@[pf_inline] def Key4RbTree.parentColor (tree : Key4RbTree) : Field := tree.topology.parentColor

def Key4RbTree.wellFormed (tree : Key4RbTree) (accountLimit : Nat := 64) : Bool :=
  tree.topology.wellFormed 8321 accountLimit && tree.key.wellFormed accountLimit &&
    tree.lastKey.wellFormed accountLimit && tree.key.widthWords == 1 &&
    tree.lastKey.widthWords == 1 && tree.links.region.sameShape tree.key.region &&
    tree.links.region.sameShape tree.lastKey.region && tree.key.firstWord + 3 == tree.lastKey.firstWord &&
    tree.links.firstWord ≤ tree.key.firstWord &&
    tree.lastKey.firstWord < tree.links.firstWord + tree.links.region.strideWords

@[pf_inline] def Key4RbTree.oneBased
    (account linksBaseWord parentBaseWord keyBaseWord strideWords capacity : Nat)
    (access : Access := {}) : Key4RbTree :=
  { topology :=
      { links :=
          { region :=
              { account, baseWord := linksBaseWord, strideWords, capacity
                indexBase := .one, access } }
        parentColor :=
          { region :=
              { account, baseWord := parentBaseWord, strideWords, capacity
                indexBase := .one, access } } }
    key :=
      { region :=
          { account, baseWord := keyBaseWord, strideWords, capacity
            indexBase := .one, access } }
    lastKey :=
      { region :=
          { account, baseWord := keyBaseWord + 3, strideWords, capacity
            indexBase := .one, access } } }

private def rootBeforeTree (rootWord : Nat) (links : Field) : Bool :=
  rootWord < links.firstWord && rootWord < maxDataWord

/-- Account-resident routines that return one scalar. Dynamic operands remain ordinary Core
operands; this target-owned descriptor contains only static bounded geometry. -/
inductive Query where
  | readWord (field : Field)
  | parentPathValid (path : ParentPath)
  | fifoFind (rootWord : Nat) (tree : FifoRbTree)
  | fifoCursor (rootWord : Nat) (tree : FifoRbTree)
  | key4Find (rootWord : Nat) (tree : Key4RbTree)
  | fifoRbTreeValid (tree : FifoRbTree)
  | key4RbTreeValid (tree : Key4RbTree)
  deriving BEq, Repr, Inhabited

def Query.arity : Query → Nat
  | .readWord .. => 1
  | .parentPathValid .. => 3
  | .fifoFind .. => 2
  | .fifoCursor .. => 3
  | .key4Find .. => 4
  | .fifoRbTreeValid .. => 4
  | .key4RbTreeValid .. => 4

def Query.effects : Query → EffectSummary
  | .readWord field => EffectSummary.forField field
  | .parentPathValid path =>
      (EffectSummary.forField path.links).merge (EffectSummary.forField path.parentColor)
  | .fifoFind _ tree =>
      (EffectSummary.forField tree.links).merge
        ((EffectSummary.forField tree.price).merge (EffectSummary.forField tree.sequence))
  | .fifoCursor _ tree =>
      (EffectSummary.forField tree.links).merge
        ((EffectSummary.forField tree.price).merge (EffectSummary.forField tree.sequence))
  | .key4Find _ tree =>
      (EffectSummary.forField tree.links).merge
        ((EffectSummary.forField tree.key).merge (EffectSummary.forField tree.lastKey))
  | .fifoRbTreeValid tree =>
      ((EffectSummary.forField tree.links).merge (EffectSummary.forField tree.parentColor)).merge
        ((EffectSummary.forField tree.price).merge (EffectSummary.forField tree.sequence))
  | .key4RbTreeValid tree =>
      ((EffectSummary.forField tree.links).merge (EffectSummary.forField tree.parentColor)).merge
        ((EffectSummary.forField tree.key).merge (EffectSummary.forField tree.lastKey))

def Query.wellFormed (accountLimit : Nat := 64) : Query → Bool
  | .readWord field =>
      field.wellFormed accountLimit && field.widthWords == 1 &&
        field.region.access == {}
  | .parentPathValid path => path.wellFormed accountLimit
  | .fifoFind rootWord tree =>
      rootBeforeTree rootWord tree.links && tree.wellFormed accountLimit &&
        tree.topology.hasAccess {}
  | .fifoCursor rootWord tree =>
      rootBeforeTree rootWord tree.links && tree.wellFormed accountLimit &&
        tree.topology.hasAccess {}
  | .key4Find rootWord tree =>
      rootBeforeTree rootWord tree.links && tree.wellFormed accountLimit &&
        tree.topology.hasAccess {}
  | .fifoRbTreeValid tree => tree.wellFormed accountLimit && tree.topology.hasAccess {}
  | .key4RbTreeValid tree => tree.wellFormed accountLimit && tree.topology.hasAccess {}

def Query.needsWalk (query : Query) : Bool :=
  query.effects.reads.any (· ≥ 1)

def Query.minAccounts (measure : V → Nat) (operands : Array V) (query : Query) : Nat :=
  let fromRegions := query.effects.reads.foldl (init := 0) fun current account =>
    Nat.max current (account + 1)
  operands.foldl (init := fromRegions) fun current value => Nat.max current (measure value)

/-- Stable target-IR spelling. The compatibility constructor below preserves the original
`accDataParentPathValid` digest. -/
def Query.canonical (renderValue : V → String) (operands : Array V) : Query → String
  | .readWord field =>
      let region := field.region
      let opcode := match region.indexBase with | .zero => "dwi" | .one => "dwi1"
      s!"{opcode}.{region.account}.{field.firstWord}.{region.strideWords}.{region.capacity}" ++
        s!"({String.intercalate "," (operands.map renderValue).toList})"
  | .parentPathValid path =>
      let region := path.links.region
      s!"dpp.{region.account}.{path.links.firstWord}.{path.parentColor.firstWord}." ++
        s!"{region.strideWords}.{region.capacity}.{path.maxDepth}" ++
        s!"({String.intercalate "," (operands.map renderValue).toList})"
  | .fifoFind rootWord tree =>
      let region := tree.links.region
      s!"rbof.{region.account}.{rootWord}.{tree.links.firstWord}." ++
        s!"{tree.price.firstWord}.{tree.sequence.firstWord}.{region.strideWords}." ++
        s!"{region.capacity}.{tree.bid}" ++
        s!"({String.intercalate "," (operands.map renderValue).toList})"
  | .fifoCursor rootWord tree =>
      let region := tree.links.region
      s!"rboc.{region.account}.{rootWord}.{tree.links.firstWord}." ++
        s!"{tree.price.firstWord}.{tree.sequence.firstWord}.{region.strideWords}." ++
        s!"{region.capacity}.{tree.bid}" ++
        s!"({String.intercalate "," (operands.map renderValue).toList})"
  | .key4Find rootWord tree =>
      let region := tree.links.region
      s!"rb4f.{region.account}.{rootWord}.{tree.links.firstWord}.{tree.key.firstWord}." ++
        s!"{region.strideWords}.{region.capacity}" ++
        s!"({String.intercalate "," (operands.map renderValue).toList})"
  | .fifoRbTreeValid tree =>
      let region := tree.links.region
      s!"drb.{region.account}.{tree.links.firstWord}.{tree.parentColor.firstWord}." ++
        s!"{tree.price.firstWord}.{tree.sequence.firstWord}." ++
        s!"{region.strideWords}.{region.capacity}.{tree.bid}" ++
        s!"({String.intercalate "," (operands.map renderValue).toList})"
  | .key4RbTreeValid tree =>
      let region := tree.links.region
      s!"drb4.{region.account}.{tree.links.firstWord}.{tree.parentColor.firstWord}." ++
        s!"{tree.key.firstWord}.{region.strideWords}.{region.capacity}" ++
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

def Query.fifoRbTreeValidOneBased
    (account linksBaseWord parentBaseWord priceBaseWord sequenceBaseWord strideWords capacity : Nat)
    (bid : Bool) : Query :=
  .fifoRbTreeValid
    (.oneBased account linksBaseWord parentBaseWord priceBaseWord sequenceBaseWord strideWords
      capacity bid)

def Query.key4RbTreeValidOneBased
    (account linksBaseWord parentBaseWord keyBaseWord strideWords capacity : Nat) : Query :=
  .key4RbTreeValid
    (.oneBased account linksBaseWord parentBaseWord keyBaseWord strideWords capacity)

def Query.fifoFindOneBased
    (account rootWord linksBaseWord parentBaseWord priceBaseWord sequenceBaseWord strideWords
      capacity : Nat) (bid : Bool) : Query :=
  .fifoFind rootWord
    (.oneBased account linksBaseWord parentBaseWord priceBaseWord sequenceBaseWord strideWords
      capacity bid)

def Query.fifoCursorOneBased
    (account rootWord linksBaseWord parentBaseWord priceBaseWord sequenceBaseWord strideWords
      capacity : Nat) (bid : Bool) : Query :=
  .fifoCursor rootWord
    (.oneBased account linksBaseWord parentBaseWord priceBaseWord sequenceBaseWord strideWords
      capacity bid)

def Query.key4FindOneBased
    (account rootWord linksBaseWord parentBaseWord keyBaseWord strideWords capacity : Nat) : Query :=
  .key4Find rootWord
    (.oneBased account linksBaseWord parentBaseWord keyBaseWord strideWords capacity)

def Query.readWordZeroBased
    (account baseWord strideWords capacity : Nat) : Query :=
  .readWord
    { region :=
        { account, baseWord, strideWords, capacity
          indexBase := .zero } }

def Query.readWordOneBased
    (account baseWord strideWords capacity : Nat) : Query :=
  .readWord
    { region :=
        { account, baseWord, strideWords, capacity
          indexBase := .one } }

/-- Compile-time key ordering for a fixed-capacity account-resident map. Both variants use the
same allocator and RB topology; only key fields and comparison policy differ. -/
inductive RbMap where
  | key4 (rootWord : Nat) (tree : Key4RbTree)
  | fifo (rootWord : Nat) (tree : FifoRbTree)
  deriving BEq, Repr, Inhabited

def RbMap.rootWord : RbMap → Nat
  | .key4 rootWord _ | .fifo rootWord _ => rootWord

def RbMap.links : RbMap → Field
  | .key4 _ tree => tree.links
  | .fifo _ tree => tree.links

def RbMap.parentColor : RbMap → Field
  | .key4 _ tree => tree.parentColor
  | .fifo _ tree => tree.parentColor

def RbMap.account (map : RbMap) : Nat := map.links.region.account
def RbMap.strideWords (map : RbMap) : Nat := map.links.region.strideWords
def RbMap.capacity (map : RbMap) : Nat := map.links.region.capacity

private def mutableAccess : Access :=
  Access.programOwnedMutable

def RbMap.wellFormed (map : RbMap) (accountLimit : Nat := 64) : Bool :=
  let region := map.links.region
  let wholeNodeFits :=
    region.baseWord + region.strideWords * (region.capacity - 1) + region.strideWords - 1 <
      maxDataWord
  let headerFits := map.rootWord + 3 < map.links.firstWord && map.rootWord + 3 < maxDataWord
  map.account > 0 && headerFits && wholeNodeFits &&
    match map with
    | .key4 _ tree =>
        tree.wellFormed accountLimit && tree.topology.hasAccess mutableAccess &&
          region.strideWords ≤ 256
    | .fifo _ tree =>
        tree.wellFormed accountLimit && tree.topology.hasAccess mutableAccess &&
          region.strideWords == 8 && tree.links.firstWord + 1 == tree.parentColor.firstWord &&
          tree.parentColor.firstWord + 1 == tree.price.firstWord &&
          tree.price.firstWord + 1 == tree.sequence.firstWord

@[pf_inline] def RbMap.key4OneBased
    (account rootWord linksBaseWord parentBaseWord keyBaseWord strideWords capacity : Nat) : RbMap :=
  .key4 rootWord
    (.oneBased account linksBaseWord parentBaseWord keyBaseWord strideWords capacity mutableAccess)

@[pf_inline] def RbMap.fifoOneBased
    (account rootWord linksBaseWord parentBaseWord keyBaseWord sequenceBaseWord strideWords
      capacity : Nat) (bid : Bool) : RbMap :=
  .fifo rootWord
    (.oneBased account linksBaseWord parentBaseWord keyBaseWord sequenceBaseWord strideWords capacity
      bid mutableAccess)

/-- Protocol-neutral source constructor for a two-word lexicographic ordered map. `descending`
selects descending order for both words; the legacy FIFO spelling remains as a compatibility alias
for the same target-owned representation. -/
@[pf_inline] def RbMap.orderedPairOneBased
    (account rootWord linksBaseWord parentBaseWord key0BaseWord key1BaseWord strideWords
      capacity : Nat) (descending : Bool) : RbMap :=
  .fifoOneBased account rootWord linksBaseWord parentBaseWord key0BaseWord key1BaseWord
    strideWords capacity descending

/-- Header and slot regions of a one-based bounded allocator. The packed cursor stores
`(bumpIndex, freeListHead)`; neither scalar is a VM pointer. -/
structure OneBasedAllocator where
  slots : Region
  liveCount : Field
  cursor : Field
  deriving BEq, Repr, Inhabited

attribute [pf_inline] OneBasedAllocator.slots OneBasedAllocator.liveCount OneBasedAllocator.cursor

def OneBasedAllocator.wellFormed (allocator : OneBasedAllocator)
    (accountLimit : Nat := 64) : Bool :=
  allocator.slots.wellFormed accountLimit && allocator.slots.indexBase == .one &&
    allocator.slots.access == Access.programOwnedMutable &&
    allocator.liveCount.wellFormed accountLimit && allocator.cursor.wellFormed accountLimit &&
    allocator.liveCount.widthWords == 1 && allocator.cursor.widthWords == 1 &&
    allocator.liveCount.region.account == allocator.slots.account &&
    allocator.cursor.region.account == allocator.slots.account &&
    allocator.liveCount.region.strideWords == 1 && allocator.cursor.region.strideWords == 1 &&
    allocator.liveCount.region.capacity == 1 && allocator.cursor.region.capacity == 1 &&
    allocator.liveCount.region.indexBase == .zero && allocator.cursor.region.indexBase == .zero &&
    allocator.liveCount.region.access == allocator.slots.access &&
    allocator.cursor.region.access == allocator.slots.access &&
    allocator.liveCount.firstWord + 1 == allocator.cursor.firstWord

/-- Recover the allocator descriptor from either supported ordered-map key schema. Header geometry
is owned by this SDK projection instead of being repeated by upper-level books or registries. -/
@[pf_inline] def RbMap.allocator (map : RbMap) : OneBasedAllocator :=
  let rootWord := map.rootWord
  let slots := map.links.region
  { slots
    liveCount := Field.scalar slots.account (rootWord + 2) slots.access
    cursor := Field.scalar slots.account (rootWord + 3) slots.access }

/-- Existing-key behavior is an explicit map policy rather than a new SVM operation kind. -/
inductive ExistingValuePolicy where
  | reject
  | replace
  deriving BEq, Repr, Inhabited

/-- Stable SVM-to-storage bridge. New bounded allocators, trees, maps, and queues extend this
target-owned call vocabulary instead of adding another top-level SVM IR constructor and another
case to the main emitter. -/
inductive Call (V : Type) where
  | writeWord (field : Field) (index value : V)
  | rbMapInsert (map : RbMap) (key value : Array V) (existing : ExistingValuePolicy)
  | rbMapRemove (map : RbMap) (key : Array V)
  | rbMapCheckedAdd (map : RbMap) (key delta : Array V)
  deriving BEq, Repr, Inhabited

def Call.mapValues (mapValue : α → β) : Call α → Call β
  | .writeWord field index value => .writeWord field (mapValue index) (mapValue value)
  | .rbMapInsert map key value existing =>
      .rbMapInsert map (key.map mapValue) (value.map mapValue) existing
  | .rbMapRemove map key => .rbMapRemove map (key.map mapValue)
  | .rbMapCheckedAdd map key delta =>
      .rbMapCheckedAdd map (key.map mapValue) (delta.map mapValue)

def Call.mapValuesM [Monad m] (mapValue : α → m β) : Call α → m (Call β)
  | .writeWord field index value =>
      return .writeWord field (← mapValue index) (← mapValue value)
  | .rbMapInsert map key value existing =>
      return .rbMapInsert map (← key.mapM mapValue) (← value.mapM mapValue) existing
  | .rbMapRemove map key => return .rbMapRemove map (← key.mapM mapValue)
  | .rbMapCheckedAdd map key delta =>
      return .rbMapCheckedAdd map (← key.mapM mapValue) (← delta.mapM mapValue)

def Call.values : Call V → Array V
  | .writeWord _ index value => #[index, value]
  | .rbMapInsert _ key value _ => key ++ value
  | .rbMapRemove _ key => key
  | .rbMapCheckedAdd _ key delta => key ++ delta

def Call.anyValue (predicate : V → Bool) (call : Call V) : Bool :=
  call.values.any predicate

def Call.allValues (predicate : V → Bool) (call : Call V) : Bool :=
  call.values.all predicate

def Call.foldValues (initial : Nat) (measure : V → Nat) (call : Call V) : Nat :=
  call.values.foldl (init := initial) fun current value => Nat.max current (measure value)

def Call.effects : Call V → EffectSummary
  | .writeWord field _ _ => EffectSummary.forField field
  | .rbMapInsert map _ _ _ | .rbMapRemove map _ | .rbMapCheckedAdd map _ _ =>
      EffectSummary.forField map.links

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
  | .rbMapInsert map key value existing =>
      map.wellFormed accountLimit && key.all valueWellFormed && value.all valueWellFormed &&
        match map, existing with
        | .key4 .., .reject => key.size == 4 && value.isEmpty
        | .fifo .., .replace => key.size == 2 && value.size == 4
        | _, _ => false
  | .rbMapRemove map key =>
      map.wellFormed accountLimit && key.all valueWellFormed &&
        match map with
        | .key4 .. => key.size == 4
        | .fifo .. => key.size == 2
  | .rbMapCheckedAdd map key delta =>
      map.wellFormed accountLimit && key.size == 4 && delta.size == 2 &&
        key.all valueWellFormed && delta.all valueWellFormed &&
        match map with
        | .key4 _ tree =>
            map.strideWords == 18 && tree.links.firstWord + 1 == tree.parentColor.firstWord &&
              tree.links.firstWord + 2 == tree.key.firstWord &&
              tree.key.firstWord + 15 < tree.links.firstWord + map.strideWords
        | .fifo .. => false

/-- Stable target-IR spelling. Storage routine details stay behind this API so generic target
plumbing does not need to know the `Call` constructors. -/
def Call.canonical (renderValue : V → String) : Call V → String
  | .writeWord field index value =>
      let opcode := match field.region.indexBase with | .zero => "dws" | .one => "dws1"
      s!"{opcode}.{field.region.account}.{field.firstWord}.{field.region.strideWords}." ++
        s!"{field.region.capacity}({renderValue index},{renderValue value})"
  | .rbMapInsert (.key4 rootWord tree) key _ .reject =>
      let region := tree.links.region
      s!"rb4i.{region.account}.{rootWord}.{tree.links.firstWord}.{tree.parentColor.firstWord}." ++
        s!"{tree.key.firstWord}.{region.strideWords}.{region.capacity}" ++
        s!"({String.intercalate "," (key.map renderValue).toList})"
  | .rbMapInsert (.fifo rootWord tree) key value .replace =>
      let region := tree.links.region
      let operands := key ++ value
      s!"rboi.{region.account}.{rootWord}.{tree.links.firstWord}.{tree.parentColor.firstWord}." ++
        s!"{tree.price.firstWord}.{tree.sequence.firstWord}.{region.strideWords}." ++
        s!"{region.capacity}.{tree.bid}" ++
        s!"({String.intercalate "," (operands.map renderValue).toList})"
  | .rbMapRemove (.key4 rootWord tree) key =>
      let region := tree.links.region
      s!"rb4r.{region.account}.{rootWord}.{tree.links.firstWord}.{tree.parentColor.firstWord}." ++
        s!"{tree.key.firstWord}.{region.strideWords}.{region.capacity}" ++
        s!"({String.intercalate "," (key.map renderValue).toList})"
  | .rbMapRemove (.fifo rootWord tree) key =>
      let region := tree.links.region
      s!"rbor.{region.account}.{rootWord}.{tree.links.firstWord}.{tree.parentColor.firstWord}." ++
        s!"{tree.price.firstWord}.{tree.sequence.firstWord}.{region.strideWords}." ++
        s!"{region.capacity}.{tree.bid}" ++
        s!"({String.intercalate "," (key.map renderValue).toList})"
  | .rbMapCheckedAdd (.key4 rootWord tree) key delta =>
      let region := tree.links.region
      let operands := key ++ delta
      s!"rbtd.{region.account}.{rootWord}.{tree.links.firstWord}.{tree.parentColor.firstWord}." ++
        s!"{tree.key.firstWord}.{region.strideWords}.{region.capacity}" ++
        s!"({String.intercalate "," (operands.map renderValue).toList})"
  | .rbMapCheckedAdd (.fifo ..) _ _ | .rbMapInsert (.key4 ..) _ _ .replace
  | .rbMapInsert (.fifo ..) _ _ .reject => "invalid-account-storage-call"

def Call.writeWordZeroBased (account baseWord strideWords capacity : Nat)
    (index value : V) : Call V :=
  .writeWord
    { region :=
        { account, baseWord, strideWords, capacity
          indexBase := .zero
          access := { writable := true, currentProgramOwned := true } } }
    index value

def Call.writeWordOneBased (account baseWord strideWords capacity : Nat)
    (index value : V) : Call V :=
  .writeWord
    { region :=
        { account, baseWord, strideWords, capacity
          indexBase := .one
          access := { writable := true, currentProgramOwned := true } } }
    index value

def Call.rbMapInsertKey4OneBased
    (account rootWord linksBaseWord parentBaseWord keyBaseWord strideWords capacity : Nat)
    (key0 key1 key2 key3 : V) : Call V :=
  .rbMapInsert
    (.key4OneBased account rootWord linksBaseWord parentBaseWord keyBaseWord strideWords capacity)
    #[key0, key1, key2, key3] #[] .reject

def Call.rbMapRemoveKey4OneBased
    (account rootWord linksBaseWord parentBaseWord keyBaseWord strideWords capacity : Nat)
    (key0 key1 key2 key3 : V) : Call V :=
  .rbMapRemove
    (.key4OneBased account rootWord linksBaseWord parentBaseWord keyBaseWord strideWords capacity)
    #[key0, key1, key2, key3]

def Call.rbMapCheckedAddKey4OneBased
    (account rootWord linksBaseWord parentBaseWord keyBaseWord strideWords capacity : Nat)
    (key0 key1 key2 key3 delta0 delta1 : V) : Call V :=
  .rbMapCheckedAdd
    (.key4OneBased account rootWord linksBaseWord parentBaseWord keyBaseWord strideWords capacity)
    #[key0, key1, key2, key3] #[delta0, delta1]

def Call.rbMapInsertFifoOneBased
    (account rootWord linksBaseWord parentBaseWord keyBaseWord sequenceBaseWord strideWords
      capacity : Nat) (bid : Bool)
    (price sequence value0 value1 value2 value3 : V) : Call V :=
  .rbMapInsert
    (.fifoOneBased account rootWord linksBaseWord parentBaseWord keyBaseWord sequenceBaseWord
      strideWords capacity bid)
    #[price, sequence] #[value0, value1, value2, value3] .replace

def Call.rbMapRemoveFifoOneBased
    (account rootWord linksBaseWord parentBaseWord keyBaseWord sequenceBaseWord strideWords
      capacity : Nat) (bid : Bool) (price sequence : V) : Call V :=
  .rbMapRemove
    (.fifoOneBased account rootWord linksBaseWord parentBaseWord keyBaseWord sequenceBaseWord
      strideWords capacity bid)
    #[price, sequence]

end ProofForge.Svm.AccountStorage
