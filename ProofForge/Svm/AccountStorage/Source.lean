import ProofForge.Attr
import ProofForge.Svm.AccountStorage
import ProofForge.Svm.Runtime

namespace ProofForge.Svm.AccountStorage.Source

open ProofForge.Svm.Runtime

/--
Source-facing handles for fixed account storage. A contract names a static `Field` or `RbMap` once
and calls these operations with only dynamic keys and values. `@[pf_inline]` erases the handle at
extraction, leaving the existing target-owned component plan; no runtime geometry, pointer, or new
SVM operation is introduced.
-/

@[pf_inline] def read (field : Field) (index : UInt64) : UInt64 :=
  let region := field.region
  let baseWord := UInt64.ofNat (region.baseWord + field.offsetWords)
  let strideWords := UInt64.ofNat region.strideWords
  let capacity := UInt64.ofNat region.capacity
  match region.indexBase with
  | .zero => accDataWordAt (UInt64.ofNat region.account) baseWord strideWords capacity index
  | .one => accDataWordAtOneBased (UInt64.ofNat region.account) baseWord strideWords capacity index

@[pf_inline] def write (field : Field) (index value : UInt64) : UInt64 :=
  let region := field.region
  let baseWord := UInt64.ofNat (region.baseWord + field.offsetWords)
  let strideWords := UInt64.ofNat region.strideWords
  let capacity := UInt64.ofNat region.capacity
  match region.indexBase with
  | .zero =>
      accDataWordSetAt (UInt64.ofNat region.account) baseWord strideWords capacity index value
  | .one =>
      accDataWordSetAtOneBased (UInt64.ofNat region.account) baseWord strideWords capacity index value

@[pf_inline] def findKey4 (map : RbMap) (key0 key1 key2 key3 : UInt64) : UInt64 :=
  match map with
  | .key4 rootWord tree =>
      let region := tree.links.region
      accDataRbTreeKey4Find (UInt64.ofNat region.account) (UInt64.ofNat rootWord)
        (UInt64.ofNat tree.links.firstWord) (UInt64.ofNat tree.parentColor.firstWord)
        (UInt64.ofNat tree.key.firstWord) (UInt64.ofNat region.strideWords)
        (UInt64.ofNat region.capacity) key0 key1 key2 key3
  | .fifo .. => 0

@[pf_inline] def findFifo (map : RbMap) (price sequence : UInt64) : UInt64 :=
  match map with
  | .key4 .. => 0
  | .fifo rootWord tree =>
      let region := tree.links.region
      accDataRbTreeOrderFind (UInt64.ofNat region.account) (UInt64.ofNat rootWord)
        (UInt64.ofNat tree.links.firstWord) (UInt64.ofNat tree.parentColor.firstWord)
        (UInt64.ofNat tree.price.firstWord) (UInt64.ofNat tree.sequence.firstWord)
        (UInt64.ofNat region.strideWords) (UInt64.ofNat region.capacity)
        (if tree.bid then 1 else 0) price sequence

@[pf_inline] def cursorFifo (map : RbMap) (hasCursor price sequence : UInt64) : UInt64 :=
  match map with
  | .key4 .. => 0
  | .fifo rootWord tree =>
      let region := tree.links.region
      accDataRbTreeOrderCursor (UInt64.ofNat region.account) (UInt64.ofNat rootWord)
        (UInt64.ofNat tree.links.firstWord) (UInt64.ofNat tree.parentColor.firstWord)
        (UInt64.ofNat tree.price.firstWord) (UInt64.ofNat tree.sequence.firstWord)
        (UInt64.ofNat region.strideWords) (UInt64.ofNat region.capacity)
        (if tree.bid then 1 else 0) hasCursor price sequence

@[pf_inline] private def mapRoot (map : RbMap) : UInt64 :=
  match map with
  | .key4 rootWord tree | .fifo rootWord tree =>
      accDataWord (UInt64.ofNat tree.links.region.account) (UInt64.ofNat rootWord)

@[pf_inline] private def mapSize (map : RbMap) : UInt64 :=
  match map with
  | .key4 rootWord tree | .fifo rootWord tree =>
      accDataWord (UInt64.ofNat tree.links.region.account) (UInt64.ofNat (rootWord + 2))

@[pf_inline] private def mapCursor (map : RbMap) : UInt64 :=
  match map with
  | .key4 rootWord tree | .fifo rootWord tree =>
      accDataWord (UInt64.ofNat tree.links.region.account) (UInt64.ofNat (rootWord + 3))

/-- Validate the tree and its exact live/free allocator partition from the static map handle. The
allocator-header encoding remains internal to this facade; contracts do not pass root, size, bump,
free-list, stride, or capacity geometry. -/
@[pf_inline] def validate (map : RbMap) : UInt64 :=
  let root := mapRoot map
  let size := mapSize map
  let cursor := mapCursor map
  match map with
  | .key4 _ tree =>
      let region := tree.links.region
      accDataRbTreeKey4Valid (UInt64.ofNat region.account) (UInt64.ofNat tree.links.firstWord)
        (UInt64.ofNat tree.parentColor.firstWord) (UInt64.ofNat tree.key.firstWord)
        (UInt64.ofNat region.strideWords) (UInt64.ofNat region.capacity)
        (root &&& 0xffffffff) size (cursor &&& 0xffffffff) (cursor >>> 32)
  | .fifo _ tree =>
      let region := tree.links.region
      accDataRbTreeValid (UInt64.ofNat region.account) (UInt64.ofNat tree.links.firstWord)
        (UInt64.ofNat tree.parentColor.firstWord) (UInt64.ofNat tree.price.firstWord)
        (UInt64.ofNat tree.sequence.firstWord) (UInt64.ofNat region.strideWords)
        (UInt64.ofNat region.capacity) (if tree.bid then 1 else 0)
        (root &&& 0xffffffff) size (cursor &&& 0xffffffff) (cursor >>> 32)

@[pf_inline] def insertKey4 (map : RbMap) (key0 key1 key2 key3 : UInt64) : UInt64 :=
  match map with
  | .key4 rootWord tree =>
      let region := tree.links.region
      accDataRbTreeKey4Insert (UInt64.ofNat region.account) (UInt64.ofNat rootWord)
        (UInt64.ofNat tree.links.firstWord) (UInt64.ofNat tree.parentColor.firstWord)
        (UInt64.ofNat tree.key.firstWord) (UInt64.ofNat region.strideWords)
        (UInt64.ofNat region.capacity) key0 key1 key2 key3
  | .fifo .. => 0

@[pf_inline] def checkedAddKey4 (map : RbMap) (key0 key1 key2 key3 delta0 delta1 : UInt64) :
    UInt64 :=
  match map with
  | .key4 rootWord tree =>
      let region := tree.links.region
      accDataRbTreeTraderDeposit (UInt64.ofNat region.account) (UInt64.ofNat rootWord)
        (UInt64.ofNat tree.links.firstWord) (UInt64.ofNat tree.parentColor.firstWord)
        (UInt64.ofNat tree.key.firstWord) (UInt64.ofNat region.strideWords)
        (UInt64.ofNat region.capacity) key0 key1 key2 key3 delta0 delta1
  | .fifo .. => 0

@[pf_inline] def insertFifo (map : RbMap) (price sequence owner size lastSlot lastTime : UInt64) :
    UInt64 :=
  match map with
  | .key4 .. => 0
  | .fifo rootWord tree =>
      let region := tree.links.region
      accDataRbTreeOrderInsert (UInt64.ofNat region.account) (UInt64.ofNat rootWord)
        (UInt64.ofNat tree.links.firstWord) (UInt64.ofNat tree.parentColor.firstWord)
        (UInt64.ofNat tree.price.firstWord) (UInt64.ofNat tree.sequence.firstWord)
        (UInt64.ofNat region.strideWords) (UInt64.ofNat region.capacity)
        (if tree.bid then 1 else 0) price sequence owner size lastSlot lastTime

@[pf_inline] def removeKey4 (map : RbMap) (key0 key1 key2 key3 : UInt64) : UInt64 :=
  match map with
  | .key4 rootWord tree =>
      let region := tree.links.region
      accDataRbTreeKey4Remove (UInt64.ofNat region.account) (UInt64.ofNat rootWord)
        (UInt64.ofNat tree.links.firstWord) (UInt64.ofNat tree.parentColor.firstWord)
        (UInt64.ofNat tree.key.firstWord) (UInt64.ofNat region.strideWords)
        (UInt64.ofNat region.capacity) key0 key1 key2 key3
  | .fifo .. => 0

@[pf_inline] def removeFifo (map : RbMap) (price sequence : UInt64) : UInt64 :=
  match map with
  | .key4 .. => 0
  | .fifo rootWord tree =>
      let region := tree.links.region
      accDataRbTreeOrderRemove (UInt64.ofNat region.account) (UInt64.ofNat rootWord)
        (UInt64.ofNat tree.links.firstWord) (UInt64.ofNat tree.parentColor.firstWord)
        (UInt64.ofNat tree.price.firstWord) (UInt64.ofNat tree.sequence.firstWord)
        (UInt64.ofNat region.strideWords) (UInt64.ofNat region.capacity)
        (if tree.bid then 1 else 0) price sequence

end ProofForge.Svm.AccountStorage.Source
