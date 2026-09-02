import ProofForge.Attr
import ProofForge.Core.Value
import ProofForge.Wasm.Near.Codec
import ProofForge.Wasm.Near.Sdk.Store.Codec

/-!
# Bounded direct NEAR IterableMap and IterableSet storage

This module implements the fixed-width `UInt64` subset of current near-sdk-rs `store::IterableMap`
and `store::IterableSet` with the explicit `Identity` key policy. A three-byte base prefix `P`
derives the exact Rust namespaces `P || 'v'` and `P || 'm'`:

* vector key: `P || 'v' || u32_le(index)`;
* vector value: standalone Borsh `UInt64` key/member;
* map lookup key: `P || 'm' || u64_le(key)`;
* map lookup value: `u64_le(value) || u32_le(index)`;
* set lookup key: `P || 'm' || u64_le(member)`;
* set lookup value: `u32_le(index)`.

The caller owns logical length as ordinary ProofForge state and composes the exposed primitives
into append, replacement, and swap-remove entries. All effects are immediate; only eventual
durable bytes match Rust. Default Sha256 lookup keys, cache/flush/Drop timing, generic values,
iterators, entries, drains, and serialized collection metadata are outside this bounded slice.

Every base prefix must be unique across collection instances and disjoint from raw and compiler
state-field keys. Callers must validate length and lookup index codes before constructing mutation
effects. An absent lookup returns `capacity`; malformed bytes return `capacity + 1`, preserving
index zero as a valid record and allowing fail-closed mutation plans.
-/

namespace ProofForge.Wasm.Near.Sdk.Store

open ProofForge.Core.Value
open ProofForge.Wasm.Near.Sdk.Storage

/-- Three-byte base namespace, represented as a little-endian compile-time literal. -/
abbrev Prefix3 := Nat

def Prefix3.wellFormed (tag : Prefix3) : Bool :=
  tag ≤ 0xffffff

@[pf_inline] def Prefix3.bounded (tag : Nat) : Prefix3 :=
  tag

/-- Exact near-sdk-rs iterable vector namespace `P || 'v'`. -/
@[pf_inline] def Prefix3.vectorTag (tag : Prefix3) : Prefix4 :=
  tag + 0x76000000

/-- Exact near-sdk-rs iterable lookup namespace `P || 'm'`. -/
@[pf_inline] def Prefix3.lookupTag (tag : Prefix3) : Prefix4 :=
  tag + 0x6d000000

@[pf_inline] def iterableCapacityValid (capacity : Nat) (length : UInt64) : Bool :=
  let bound := UInt64.ofNat capacity
  if bound = 0 then false else if bound ≤ 64 then length ≤ bound else false

@[pf_inline] def iterableMapValue
    (value index : UInt64) : BoundedBytes 12 :=
  { length := 12
    values := #v[
      (value &&& 0xff).toUInt8,
      ((value >>> 8) &&& 0xff).toUInt8,
      ((value >>> 16) &&& 0xff).toUInt8,
      ((value >>> 24) &&& 0xff).toUInt8,
      ((value >>> 32) &&& 0xff).toUInt8,
      ((value >>> 40) &&& 0xff).toUInt8,
      ((value >>> 48) &&& 0xff).toUInt8,
      ((value >>> 56) &&& 0xff).toUInt8,
      (index &&& 0xff).toUInt8,
      ((index >>> 8) &&& 0xff).toUInt8,
      ((index >>> 16) &&& 0xff).toUInt8,
      ((index >>> 24) &&& 0xff).toUInt8
    ] }

@[pf_inline] def iterableSetValue (index : UInt64) : BoundedBytes 4 :=
  { length := 4
    values := #v[
      (index &&& 0xff).toUInt8,
      ((index >>> 8) &&& 0xff).toUInt8,
      ((index >>> 16) &&& 0xff).toUInt8,
      ((index >>> 24) &&& 0xff).toUInt8
    ] }

@[pf_inline] def resultUInt32At
    (result : ResultBuffer) (offset : UInt64) : UInt64 :=
  (result.byte offset).toUInt64 |||
    ((result.byte (offset + 1)).toUInt64 <<< 8) |||
    ((result.byte (offset + 2)).toUInt64 <<< 16) |||
    ((result.byte (offset + 3)).toUInt64 <<< 24)

@[pf_inline] def resultUInt64At
    (result : ResultBuffer) (offset : UInt64) : UInt64 :=
  (result.byte offset).toUInt64 |||
    ((result.byte (offset + 1)).toUInt64 <<< 8) |||
    ((result.byte (offset + 2)).toUInt64 <<< 16) |||
    ((result.byte (offset + 3)).toUInt64 <<< 24) |||
    ((result.byte (offset + 4)).toUInt64 <<< 32) |||
    ((result.byte (offset + 5)).toUInt64 <<< 40) |||
    ((result.byte (offset + 6)).toUInt64 <<< 48) |||
    ((result.byte (offset + 7)).toUInt64 <<< 56)

/-- Compile-time bound for a direct `UInt64` Identity `IterableMap`. -/
abbrev DirectIterableMap64 := Nat

def DirectIterableMap64.wellFormed (map : DirectIterableMap64) : Bool :=
  Codec.storageCapacityValid map

@[pf_inline] def DirectIterableMap64.bounded (capacity : Nat) : DirectIterableMap64 :=
  capacity

@[pf_inline] def DirectIterableMap64.validLength
    (map : DirectIterableMap64) (length : UInt64) : Bool :=
  iterableCapacityValid map length

@[pf_inline] def DirectIterableMap64.canInsert
    (map : DirectIterableMap64) (length : UInt64) : Bool :=
  if map.validLength length then length < UInt64.ofNat map else false

@[pf_inline] def DirectIterableMap64.containsIndex
    (map : DirectIterableMap64) (length index : UInt64) : Bool :=
  if map.validLength length then index < length else false

@[pf_inline] def DirectIterableMap64.vectorKey
    (_map : DirectIterableMap64) (vectorTag : Prefix4) (index : UInt64) : BoundedBytes 8 :=
  vectorTag.keyUInt32 index

@[pf_inline] def DirectIterableMap64.lookupKey
    (_map : DirectIterableMap64) (lookupTag : Prefix4) (key : UInt64) : BoundedBytes 12 :=
  lookupTag.keyUInt64 key

@[pf_inline] def DirectIterableMap64.vectorValue
    (_map : DirectIterableMap64) (key : UInt64) : BoundedBytes 8 :=
  borshUInt64 key

@[pf_inline] def DirectIterableMap64.lookupValue
    (_map : DirectIterableMap64) (value index : UInt64) : BoundedBytes 12 :=
  iterableMapValue value index

/-- Read a lookup record index. Absence is `capacity`; malformed bytes are `capacity + 1`. -/
@[pf_inline] def DirectIterableMap64.indexCode
    (map : DirectIterableMap64) (lookupTag : Prefix4) (key : UInt64) : UInt64 :=
  let result : ResultBuffer := 12
  let _ := result.read (map.lookupKey lookupTag key)
  if result.status = 0 then UInt64.ofNat map
  else if result.fits then
    if result.length = 12 then
      let index := resultUInt32At result 8
      if index < UInt64.ofNat map then index else UInt64.ofNat map + 1
    else UInt64.ofNat map + 1
  else UInt64.ofNat map + 1

/-- Read the value field of an exact map record, or return `fallback`. -/
@[pf_inline] def DirectIterableMap64.getD
    (map : DirectIterableMap64) (lookupTag : Prefix4) (key fallback : UInt64) : UInt64 :=
  let result : ResultBuffer := 12
  let _ := result.read (map.lookupKey lookupTag key)
  if result.status = 1 then
    if result.fits then
      if result.length = 12 then resultUInt64At result 0 else fallback
    else fallback
  else fallback

@[pf_inline] def DirectIterableMap64.keyAtD
    (map : DirectIterableMap64) (vectorTag : Prefix4)
    (length index fallback : UInt64) : UInt64 :=
  if map.containsIndex length index then
    let result : ResultBuffer := 8
    let _ := result.read (map.vectorKey vectorTag index)
    resultUInt64D fallback
  else fallback

@[pf_inline] def DirectIterableMap64.hasKeyAt
    (map : DirectIterableMap64) (vectorTag : Prefix4) (length index : UInt64) : UInt64 :=
  if map.containsIndex length index then
    let result : ResultBuffer := 8
    let _ := result.hasKey (map.vectorKey vectorTag index)
    result.status
  else 0

/-- Source-level IterableMap handle: compile-time capacity + derived vector/lookup namespaces.
Length stays in STATE (N9); tags are stored directly (like `DirectVector64.Handle.tag`) so
Extract erases projections to literals. Methods are thin `@[pf_inline]` facades. -/
structure DirectIterableMap64.Handle where
  capacity : DirectIterableMap64
  vectorTag : Prefix4
  lookupTag : Prefix4
  deriving Repr

@[pf_inline] def DirectIterableMap64.handle
    (capacity : Nat) (vectorTag lookupTag : Prefix4) : DirectIterableMap64.Handle :=
  { capacity := capacity, vectorTag := vectorTag, lookupTag := lookupTag }

@[pf_inline] def DirectIterableMap64.handleFromBase
    (capacity : Nat) (base : Prefix3) : DirectIterableMap64.Handle :=
  handle capacity base.vectorTag base.lookupTag

@[pf_inline] def DirectIterableMap64.Handle.validLength
    (h : DirectIterableMap64.Handle) (length : UInt64) : Bool :=
  DirectIterableMap64.validLength h.capacity length

@[pf_inline] def DirectIterableMap64.Handle.canInsert
    (h : DirectIterableMap64.Handle) (length : UInt64) : Bool :=
  DirectIterableMap64.canInsert h.capacity length

@[pf_inline] def DirectIterableMap64.Handle.containsIndex
    (h : DirectIterableMap64.Handle) (length index : UInt64) : Bool :=
  DirectIterableMap64.containsIndex h.capacity length index

@[pf_inline] def DirectIterableMap64.Handle.vectorKey
    (h : DirectIterableMap64.Handle) (index : UInt64) : BoundedBytes 8 :=
  DirectIterableMap64.vectorKey h.capacity h.vectorTag index

@[pf_inline] def DirectIterableMap64.Handle.lookupKey
    (h : DirectIterableMap64.Handle) (key : UInt64) : BoundedBytes 12 :=
  DirectIterableMap64.lookupKey h.capacity h.lookupTag key

@[pf_inline] def DirectIterableMap64.Handle.vectorValue
    (h : DirectIterableMap64.Handle) (key : UInt64) : BoundedBytes 8 :=
  DirectIterableMap64.vectorValue h.capacity key

@[pf_inline] def DirectIterableMap64.Handle.lookupValue
    (h : DirectIterableMap64.Handle) (value index : UInt64) : BoundedBytes 12 :=
  DirectIterableMap64.lookupValue h.capacity value index

@[pf_inline] def DirectIterableMap64.Handle.indexCode
    (h : DirectIterableMap64.Handle) (key : UInt64) : UInt64 :=
  DirectIterableMap64.indexCode h.capacity h.lookupTag key

@[pf_inline] def DirectIterableMap64.Handle.getD
    (h : DirectIterableMap64.Handle) (key fallback : UInt64) : UInt64 :=
  DirectIterableMap64.getD h.capacity h.lookupTag key fallback

@[pf_inline] def DirectIterableMap64.Handle.keyAtD
    (h : DirectIterableMap64.Handle) (length index fallback : UInt64) : UInt64 :=
  DirectIterableMap64.keyAtD h.capacity h.vectorTag length index fallback

@[pf_inline] def DirectIterableMap64.Handle.hasKeyAt
    (h : DirectIterableMap64.Handle) (length index : UInt64) : UInt64 :=
  DirectIterableMap64.hasKeyAt h.capacity h.vectorTag length index

/-- Compile-time bound for a direct `UInt64` Identity `IterableSet`. -/
abbrev DirectIterableSet64 := Nat

def DirectIterableSet64.wellFormed (set : DirectIterableSet64) : Bool :=
  Codec.storageCapacityValid set

@[pf_inline] def DirectIterableSet64.bounded (capacity : Nat) : DirectIterableSet64 :=
  capacity

@[pf_inline] def DirectIterableSet64.validLength
    (set : DirectIterableSet64) (length : UInt64) : Bool :=
  iterableCapacityValid set length

@[pf_inline] def DirectIterableSet64.canInsert
    (set : DirectIterableSet64) (length : UInt64) : Bool :=
  if set.validLength length then length < UInt64.ofNat set else false

@[pf_inline] def DirectIterableSet64.containsIndex
    (set : DirectIterableSet64) (length index : UInt64) : Bool :=
  if set.validLength length then index < length else false

@[pf_inline] def DirectIterableSet64.vectorKey
    (_set : DirectIterableSet64) (vectorTag : Prefix4) (index : UInt64) : BoundedBytes 8 :=
  vectorTag.keyUInt32 index

@[pf_inline] def DirectIterableSet64.lookupKey
    (_set : DirectIterableSet64) (lookupTag : Prefix4) (value : UInt64) : BoundedBytes 12 :=
  lookupTag.keyUInt64 value

@[pf_inline] def DirectIterableSet64.vectorValue
    (_set : DirectIterableSet64) (value : UInt64) : BoundedBytes 8 :=
  borshUInt64 value

@[pf_inline] def DirectIterableSet64.lookupValue
    (_set : DirectIterableSet64) (index : UInt64) : BoundedBytes 4 :=
  iterableSetValue index

/-- Read a lookup record index. Absence is `capacity`; malformed bytes are `capacity + 1`. -/
@[pf_inline] def DirectIterableSet64.indexCode
    (set : DirectIterableSet64) (lookupTag : Prefix4) (value : UInt64) : UInt64 :=
  let result : ResultBuffer := 4
  let _ := result.read (set.lookupKey lookupTag value)
  if result.status = 0 then UInt64.ofNat set
  else if result.fits then
    if result.length = 4 then
      let index := resultUInt32At result 0
      if index < UInt64.ofNat set then index else UInt64.ofNat set + 1
    else UInt64.ofNat set + 1
  else UInt64.ofNat set + 1

@[pf_inline] def DirectIterableSet64.keyAtD
    (set : DirectIterableSet64) (vectorTag : Prefix4)
    (length index fallback : UInt64) : UInt64 :=
  if set.containsIndex length index then
    let result : ResultBuffer := 8
    let _ := result.read (set.vectorKey vectorTag index)
    resultUInt64D fallback
  else fallback

@[pf_inline] def DirectIterableSet64.hasKeyAt
    (set : DirectIterableSet64) (vectorTag : Prefix4) (length index : UInt64) : UInt64 :=
  if set.containsIndex length index then
    let result : ResultBuffer := 8
    let _ := result.hasKey (set.vectorKey vectorTag index)
    result.status
  else 0

/-- Source-level IterableSet handle: compile-time capacity + derived vector/lookup namespaces.
Length stays in STATE (N9); tags are stored directly so Extract erases projections to literals.
Methods are thin `@[pf_inline]` facades. -/
structure DirectIterableSet64.Handle where
  capacity : DirectIterableSet64
  vectorTag : Prefix4
  lookupTag : Prefix4
  deriving Repr

@[pf_inline] def DirectIterableSet64.handle
    (capacity : Nat) (vectorTag lookupTag : Prefix4) : DirectIterableSet64.Handle :=
  { capacity := capacity, vectorTag := vectorTag, lookupTag := lookupTag }

@[pf_inline] def DirectIterableSet64.handleFromBase
    (capacity : Nat) (base : Prefix3) : DirectIterableSet64.Handle :=
  handle capacity base.vectorTag base.lookupTag

@[pf_inline] def DirectIterableSet64.Handle.validLength
    (h : DirectIterableSet64.Handle) (length : UInt64) : Bool :=
  DirectIterableSet64.validLength h.capacity length

@[pf_inline] def DirectIterableSet64.Handle.canInsert
    (h : DirectIterableSet64.Handle) (length : UInt64) : Bool :=
  DirectIterableSet64.canInsert h.capacity length

@[pf_inline] def DirectIterableSet64.Handle.containsIndex
    (h : DirectIterableSet64.Handle) (length index : UInt64) : Bool :=
  DirectIterableSet64.containsIndex h.capacity length index

@[pf_inline] def DirectIterableSet64.Handle.vectorKey
    (h : DirectIterableSet64.Handle) (index : UInt64) : BoundedBytes 8 :=
  DirectIterableSet64.vectorKey h.capacity h.vectorTag index

@[pf_inline] def DirectIterableSet64.Handle.lookupKey
    (h : DirectIterableSet64.Handle) (value : UInt64) : BoundedBytes 12 :=
  DirectIterableSet64.lookupKey h.capacity h.lookupTag value

@[pf_inline] def DirectIterableSet64.Handle.vectorValue
    (h : DirectIterableSet64.Handle) (value : UInt64) : BoundedBytes 8 :=
  DirectIterableSet64.vectorValue h.capacity value

@[pf_inline] def DirectIterableSet64.Handle.lookupValue
    (h : DirectIterableSet64.Handle) (index : UInt64) : BoundedBytes 4 :=
  DirectIterableSet64.lookupValue h.capacity index

@[pf_inline] def DirectIterableSet64.Handle.indexCode
    (h : DirectIterableSet64.Handle) (value : UInt64) : UInt64 :=
  DirectIterableSet64.indexCode h.capacity h.lookupTag value

@[pf_inline] def DirectIterableSet64.Handle.keyAtD
    (h : DirectIterableSet64.Handle) (length index fallback : UInt64) : UInt64 :=
  DirectIterableSet64.keyAtD h.capacity h.vectorTag length index fallback

@[pf_inline] def DirectIterableSet64.Handle.hasKeyAt
    (h : DirectIterableSet64.Handle) (length index : UInt64) : UInt64 :=
  DirectIterableSet64.hasKeyAt h.capacity h.vectorTag length index

end ProofForge.Wasm.Near.Sdk.Store
