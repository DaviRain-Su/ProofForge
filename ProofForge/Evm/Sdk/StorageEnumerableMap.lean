import ProofForge.Attr
import ProofForge.Evm.Sdk.StorageEnumerableSet

namespace ProofForge.Evm.Sdk.StorageEnumerableMap

/-!
# EVM SDK persistent bounded enumerable UInt64 map (R5-019)

`StorageEnumerableMap` composes the existing bounded enumerable-set index with one independent
hashed value namespace. Its physical state is:

- a compile-time fixed `Vector UInt64 capacity` of keys plus an adjacent live count;
- a key → position+1 `Storage.U64Map`, owned by `StorageEnumerableSet`;
- a distinct key → value `Storage.U64Map`.

The position map is the sole presence authority, so key `0` and value `0` are both ordinary data.
Insert, update, lookup, indexed enumeration, and swap-remove are O(1). Removal clears both the
position and value entries; middle removal additionally repairs only the moved key's position.
There is no runtime slot allocator, pointer, heap object, capacity scan, or new Runtime/Ops/IR/
Component/Emit vocabulary. As with `StorageEnumerableSet`, applications keep literal State vector
and count writes visible while this module owns reusable geometry and fail-closed decisions.
-/

/-- Compile-time geometry of one bounded enumerable UInt64 → UInt64 map. Descriptor data is erased
before extraction. `index.positions` and `entries` must be distinct hashed namespaces. -/
structure Descriptor (capacity : Nat) where
  index : StorageEnumerableSet.Descriptor capacity
  entries : Storage.U64Map
  deriving Repr

/-- Declare the fixed key vector/count pair and bind two caller-allocated hashed namespaces. -/
@[pf_inline] def declare (layout : Storage.Static.Layout) (keysName countName : String)
    (positions entries : Storage.U64Map) (capacity : Nat) :
    Storage.Static.Allocated (Descriptor capacity) :=
  let index := StorageEnumerableSet.declare layout keysName countName positions capacity
  { handle := { index := index.handle, entries }, next := index.next }

/-- Exact static geometry plus disjoint position/value namespaces. -/
def Descriptor.wellFormed {capacity : Nat} (map : Descriptor capacity) : Bool :=
  map.index.wellFormed && map.index.positions.base != map.entries.base

/-! ## Runtime policy

All predicates consume already-observed scalars. The consumer reads `positions.get key` once per
logical decision path and loads the selected backing key only after the position is known live.
Malformed count, forged position, or backing mismatch must return before every physical write.
-/

/-- Canonical count under the fixed capacity. -/
@[pf_inline] def wellFormed (capacity count : UInt64) : Bool :=
  StorageEnumerableSet.wellFormed capacity count

/-- Exact zero position means absent. -/
@[pf_inline] def absent (position : UInt64) : Bool :=
  StorageEnumerableSet.absent position

/-- Nonzero position outside the active prefix is forged metadata. -/
@[pf_inline] def forged (position count : UInt64) : Bool :=
  StorageEnumerableSet.forged position count

/-- Position and backing-key evidence establish presence independently of the stored value. -/
@[pf_inline] def isPresent (position count storedKey key : UInt64) : Bool :=
  StorageEnumerableSet.isPresent position count storedKey key

/-- Insert requires canonical free capacity and exact absence. -/
@[pf_inline] def canInsert (capacity count position : UInt64) : Bool :=
  StorageEnumerableSet.canInsert capacity count position

/-- Update requires a canonical count and matching live key evidence. Values, including zero, do
not participate in membership. -/
@[pf_inline] def canUpdate (capacity count position storedKey key : UInt64) : Bool :=
  wellFormed capacity count && isPresent position count storedKey key

/-- Remove uses the same strict evidence as update. Exact absence remains a separate no-write
consumer outcome. -/
@[pf_inline] def canRemove (capacity count position storedKey key : UInt64) : Bool :=
  StorageEnumerableSet.canRemove capacity count position && storedKey == key

/-- Indexed enumeration addresses only the canonical active key prefix. -/
@[pf_inline] def canEntryAt (capacity count index : UInt64) : Bool :=
  StorageEnumerableSet.canValueAt capacity count index

@[pf_inline] def isFull (capacity count : UInt64) : Bool :=
  StorageEnumerableSet.isFull capacity count

@[pf_inline] def insertPosition (count : UInt64) : UInt64 :=
  StorageEnumerableSet.insertPosition count

@[pf_inline] def removedCount (count : UInt64) : UInt64 :=
  StorageEnumerableSet.removedCount count

@[pf_inline] def movesLast (position count : UInt64) : Bool :=
  StorageEnumerableSet.movesLast position count

/-- Canonical fallback for absent/OOB/malformed views. It is not an absence marker: a present key
may map to value zero. -/
@[pf_inline] def emptyValue : UInt64 := 0

end ProofForge.Evm.Sdk.StorageEnumerableMap
