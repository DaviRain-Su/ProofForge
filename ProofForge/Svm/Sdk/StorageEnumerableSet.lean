import ProofForge.Attr
import ProofForge.Core.Collections
import ProofForge.Svm.Sdk.Storage

/-!
# SVM SDK persistent bounded enumerable UInt64 set

This account-resident binding composes the existing `OrderedMap`, allocator, checked `PodField`
access, and one shared target-neutral position+1/swap-remove policy. A descriptor derives the
complete compact layout from only `(account, baseWord, capacity)`: callers do not repeat root,
tree-field, stride, payload, or allocator offsets.

The active values prefix is one-based and fixed-capacity. The key4 tree maps `(value, 0, 0, 0)` to
a stable node slot, and one payload word in that node stores the value's enumeration position.
`0` is absent position evidence, not an absent key, so value `0` remains a valid member. Removal
moves the final active value into a removed middle position and repairs only that moved node.

No pointer, heap collection, runtime-selected geometry, bulk scan, new Runtime leaf, operation,
IR constructor, component, or emitter case is introduced. Every operation is bounded by the
existing fixed account tree and touches a constant number of extra account words.
-/

namespace ProofForge.Svm.Sdk.StorageEnumerableSet

open ProofForge.Svm.AccountStorage
open ProofForge.Svm.AccountStorage.Source
open ProofForge.Svm.Sdk.Storage

/-- Compact key4 nodes use one links word, one parent/color word, four key words, and one
enumeration-position payload word. -/
@[pf_inline] def nodeStrideWords : Nat := 7

/-- One persistent enumerable set. Every field is compile-time descriptor data erased during
extraction; only checked account reads/writes and ordered-map operations remain. -/
structure Descriptor where
  values : Field
  index : RbMap
  positions : Field
  deriving BEq, Repr, Inhabited

attribute [pf_inline] Descriptor.values Descriptor.index Descriptor.positions

/-- Derive a complete compact layout from one base word. Values occupy `capacity` consecutive
words, followed by four map headers and `capacity` seven-word key4 nodes. -/
@[pf_inline] def Descriptor.oneBased
    (account baseWord capacity : Nat) : Descriptor :=
  let rootWord := baseWord + capacity
  let nodesWord := rootWord + 4
  { values := Field.oneBased account baseWord 1 capacity
    index := RbMap.key4OneBased account rootWord nodesWord (nodesWord + 1) (nodesWord + 2)
      nodeStrideWords capacity
    positions := Field.oneBased account (nodesWord + 6) nodeStrideWords capacity }

/-- Validate the exact compact layout and all delegated storage/map contracts. The predicate is
for compile-time guards; checked target stubs continue to enforce actual account length,
writability, ownership, indexes, and tree traversal at runtime. -/
def Descriptor.wellFormed (set : Descriptor) (accountLimit : Nat := 64) : Bool :=
  set.values.mutableOneBasedWord accountLimit && set.index.wellFormed accountLimit &&
    set.positions.mutableOneBasedWord accountLimit &&
    match set.index with
    | .fifo .. => false
    | .key4 rootWord tree =>
        let values := set.values
        let positions := set.positions
        values.region.account == tree.links.region.account &&
          values.region.account > 0 && values.region.strideWords == 1 &&
          values.region.capacity == tree.links.region.capacity &&
          values.firstWord + values.region.capacity == rootWord &&
          rootWord + 4 == tree.links.firstWord &&
          tree.links.firstWord + 1 == tree.parentColor.firstWord &&
          tree.links.firstWord + 2 == tree.key.firstWord &&
          tree.links.region.strideWords == nodeStrideWords &&
          positions.region.sameShape tree.links.region &&
          positions.firstWord == tree.links.firstWord + 6

@[pf_inline] def Descriptor.capacity (set : Descriptor) : UInt64 :=
  UInt64.ofNat set.values.region.capacity

@[pf_inline] def Descriptor.size (set : Descriptor) : UInt64 :=
  Source.liveCount set.index

@[pf_inline] def Descriptor.findNode (set : Descriptor) (value : UInt64) : UInt64 :=
  Source.findKey4 set.index value 0 0 0

@[pf_inline] def Descriptor.positionOfNode (set : Descriptor) (node : UInt64) : UInt64 :=
  Source.read set.positions node

@[pf_inline] def Descriptor.valueAtPosition (set : Descriptor) (position : UInt64) : UInt64 :=
  Source.read set.values position

/-! ## Shared position policy -/

@[pf_inline] def countWellFormed (capacity count : UInt64) : Bool :=
  Core.Collections.BoundedSet.countWellFormed capacity count

@[pf_inline] def positionLive (position count : UInt64) : Bool :=
  Core.Collections.BoundedSet.positionLive position count

@[pf_inline] def isPresentAt (position count stored key : UInt64) : Bool :=
  Core.Collections.BoundedSet.isPresentAt position count stored key

@[pf_inline] def canValueAt (capacity count index : UInt64) : Bool :=
  Core.Collections.BoundedSet.canValueAt capacity count index

/-! ## Account-resident operations -/

/-- Canonically reset the tree/allocator headers. Stale values and node payload bytes remain
unreachable behind the empty headers. -/
@[pf_inline] def Descriptor.initialize (set : Descriptor) : UInt64 :=
  OrderedMap.initialize { map := set.index }

/-- Return true iff the map's node, stored position, and active-prefix value agree. -/
@[pf_inline] def Descriptor.contains (set : Descriptor) (value : UInt64) : Bool :=
  match set with
  | ⟨values, index, positions⟩ =>
    let node := Source.findKey4 index value 0 0 0
    if node = 0 then false
    else
      let count := Source.liveCount index
      let capacity := UInt64.ofNat values.region.capacity
      if !Core.Collections.BoundedSet.countWellFormed capacity count then false
      else
        let position := Source.read positions node
        if !Core.Collections.BoundedSet.positionLive position count then false
        else Source.read values position == value

/-- Insert one absent value. Returns `1` when inserted, `2` for an already-present value, and `0`
for full capacity or malformed metadata. Non-insert outcomes do not change the active set. -/
@[pf_inline] def Descriptor.insert (set : Descriptor) (value : UInt64) : UInt64 :=
  match set with
  | ⟨values, index, positions⟩ =>
    let existing := Source.findKey4 index value 0 0 0
    if existing != 0 then
      let count := Source.liveCount index
      let capacity := UInt64.ofNat values.region.capacity
      if !Core.Collections.BoundedSet.countWellFormed capacity count then 0
      else
        let position := Source.read positions existing
        if Core.Collections.BoundedSet.isPresentAt position count
            (Source.read values position) value then 2 else 0
    else
      let count := Source.liveCount index
      let capacity := UInt64.ofNat values.region.capacity
      if !Core.Collections.BoundedSet.countWellFormed capacity count then 0
      else if capacity ≤ count then 0
      else
        let _ := Source.insertKey4 index value 0 0 0
        let node := Source.findKey4 index value 0 0 0
        if node = 0 then 0
        else
          let position := count + 1
          let _ := Source.write values position value
          let _ := Source.write positions node position
          1

/-- Remove one present value with unordered swap-remove. All position/backing evidence, including
the moved final value's reverse position, is checked before mutation. Success returns `1`; absence
or malformed metadata returns `0` without an SDK write. -/
@[pf_inline] def Descriptor.remove (set : Descriptor) (value : UInt64) : UInt64 :=
  match set with
  | ⟨values, index, positions⟩ =>
    let node := Source.findKey4 index value 0 0 0
    if node = 0 then 0
    else
      let count := Source.liveCount index
      let capacity := UInt64.ofNat values.region.capacity
      let position := Source.read positions node
      if !Core.Collections.BoundedSet.countWellFormed capacity count then 0
      else if !Core.Collections.BoundedSet.positionLive position count then 0
      else if Source.read values position != value then 0
      else
        let lastValue := Source.read values count
        if position = count then
          let _ := Source.removeKey4 index value 0 0 0
          if Source.findKey4 index value 0 0 0 = 0 then 1 else 0
        else
          let lastNode := Source.findKey4 index lastValue 0 0 0
          if lastNode = 0 || Source.read positions lastNode != count then 0
          else
            let _ := Source.removeKey4 index value 0 0 0
            if Source.findKey4 index value 0 0 0 != 0 then 0
            else
              let _ := Source.write values position lastValue
              let _ := Source.write positions lastNode position
              1

/-- Zero-based bounded enumeration over the live prefix. OOB or malformed count returns `0` and
performs no account read beyond the map count header. Value `0` is valid; callers needing to
distinguish it from fallback pair this view with `index < size`. -/
@[pf_inline] def Descriptor.valueAt (set : Descriptor) (index : UInt64) : UInt64 :=
  match set with
  | ⟨values, map, _⟩ =>
    let count := Source.liveCount map
    let capacity := UInt64.ofNat values.region.capacity
    if canValueAt capacity count index then
      Source.read values (index + 1)
    else 0

/-- True iff `index` is a live zero-based enumeration slot under the shared position policy. -/
@[pf_inline] def Descriptor.canIndex (set : Descriptor) (index : UInt64) : Bool :=
  match set with
  | ⟨values, map, _⟩ =>
    canValueAt (UInt64.ofNat values.region.capacity) (Source.liveCount map) index

/-- Remove the member currently at zero-based `index` via the existing swap-remove path.
OOB or malformed count returns `0` with no write. After success, only reverse (or fresh
`size`) scans remain valid — forward indexes past the hole are not stable. -/
@[pf_inline] def Descriptor.removeAt (set : Descriptor) (index : UInt64) : UInt64 :=
  match set with
  | ⟨values, map, _⟩ =>
    let count := Source.liveCount map
    let capacity := UInt64.ofNat values.region.capacity
    if !canValueAt capacity count index then 0
    else Descriptor.remove set (Source.read values (index + 1))

/-- Alias of `initialize`: reset tree/allocator headers. Stale payload words stay unreachable. -/
@[pf_inline] def Descriptor.clear (set : Descriptor) : UInt64 :=
  Descriptor.initialize set

end ProofForge.Svm.Sdk.StorageEnumerableSet
