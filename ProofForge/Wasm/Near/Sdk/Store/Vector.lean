import ProofForge.Attr
import ProofForge.Core.Value
import ProofForge.Wasm.Near.Codec
import ProofForge.Wasm.Near.Sdk.Store.Codec

/-!
# Bounded direct-write NEAR Vector storage

`DirectVector64` is a compiler-bounded, immediate-write foundation for persistent `UInt64`
vectors. Its element layout matches current `near_sdk::store::Vector<UInt64>` for a bare four-byte
prefix:

* key: `prefix || u32_le(index)`;
* value: the standalone eight-byte little-endian Borsh encoding of `UInt64`.

The capacity and `Prefix4` are compile-time `Nat` carriers and never become persistent metadata or
guest pointers. Distinct valid `Prefix4` values have disjoint element keyspaces within this
collection family because every prefix and index suffix has the same fixed width. Callers must
also keep these eight-byte keys disjoint from raw-storage keys and compiler state-field names.

This is intentionally not the complete Rust SDK collection. The caller owns the logical length in
ordinary ProofForge state until the NEAR `STATE` lifecycle lands; writes are immediate instead of
using an `IndexMap` cache/`Drop` flush; values are `UInt64`; and malformed or missing in-range slots
are returned as the explicit default by the `*D` readers. Immediate writes remain transaction
atomic under nearcore rollback, but differ in gas and same-invocation raw-read visibility.
-/

namespace ProofForge.Wasm.Near.Sdk.Store

open ProofForge.Core.Value
open ProofForge.Wasm.Near.Sdk.Storage

/-- Compile-time logical element bound. The current bounded collection profile accepts 1..64. -/
abbrev DirectVector64 := Nat

def DirectVector64.wellFormed (vector : DirectVector64) : Bool :=
  Codec.storageCapacityValid vector

@[pf_inline] def DirectVector64.bounded (capacity : Nat) : DirectVector64 :=
  capacity

@[pf_inline] def DirectVector64.validLength
    (vector : DirectVector64) (length : UInt64) : Bool :=
  length ≤ UInt64.ofNat vector

@[pf_inline] def DirectVector64.contains
    (vector : DirectVector64) (length index : UInt64) : Bool :=
  if vector.validLength length then index < length else false

@[pf_inline] def DirectVector64.canPush
    (vector : DirectVector64) (length : UInt64) : Bool :=
  if vector.validLength length then length < UInt64.ofNat vector else false

/-- Exact current `store::Vector` bare-prefix key recipe. The caller must first establish the
bounded index precondition with `contains` or `canPush`; only then is the low 32-bit suffix used. -/
@[pf_inline] def DirectVector64.elementKey
    (_vector : DirectVector64) (tag : Prefix4) (index : UInt64) : BoundedBytes 8 :=
  tag.keyUInt32 index

/-- Standalone Borsh `UInt64`: exactly eight little-endian bytes, with no length tag. -/
@[pf_inline] def DirectVector64.elementValue
    (_vector : DirectVector64) (value : UInt64) : BoundedBytes 8 :=
  borshUInt64 value

/-- Decode the active exact-width raw-storage result, or return `fallback` for absent,
oversized, or malformed slots. This consumes no storage operation by itself. -/
@[pf_inline] def DirectVector64.resultValueD
    (_vector : DirectVector64) (fallback : UInt64) : UInt64 :=
  resultUInt64D fallback

/-- Read an in-range element and decode it, or return `fallback`. Out-of-range access performs no
host read. -/
@[pf_inline] def DirectVector64.getD
    (vector : DirectVector64) (tag : Prefix4) (length index fallback : UInt64) : UInt64 :=
  if length ≤ UInt64.ofNat vector then
    if index < length then
      let result : ResultBuffer := 8
      let _ := result.read (vector.elementKey tag index)
      vector.resultValueD fallback
    else fallback
  else fallback

/-- Source-level collection handle: compile-time capacity + `Prefix4`. Length stays in STATE
(N9); this type never persists metadata or invents a second length key. Methods are thin
`@[pf_inline]` facades over `DirectVector64` so Extract sees the same shapes as raw calls. -/
structure DirectVector64.Handle where
  capacity : DirectVector64
  tag : Prefix4
  deriving Repr

@[pf_inline] def DirectVector64.handle (capacity : Nat) (tag : Prefix4) : DirectVector64.Handle :=
  { capacity := capacity, tag := tag }

@[pf_inline] def DirectVector64.Handle.validLength
    (h : DirectVector64.Handle) (length : UInt64) : Bool :=
  DirectVector64.validLength h.capacity length

@[pf_inline] def DirectVector64.Handle.contains
    (h : DirectVector64.Handle) (length index : UInt64) : Bool :=
  DirectVector64.contains h.capacity length index

@[pf_inline] def DirectVector64.Handle.canPush
    (h : DirectVector64.Handle) (length : UInt64) : Bool :=
  DirectVector64.canPush h.capacity length

@[pf_inline] def DirectVector64.Handle.elementKey
    (h : DirectVector64.Handle) (index : UInt64) : BoundedBytes 8 :=
  DirectVector64.elementKey h.capacity h.tag index

@[pf_inline] def DirectVector64.Handle.elementValue
    (h : DirectVector64.Handle) (value : UInt64) : BoundedBytes 8 :=
  DirectVector64.elementValue h.capacity value

@[pf_inline] def DirectVector64.Handle.getD
    (h : DirectVector64.Handle) (length index fallback : UInt64) : UInt64 :=
  DirectVector64.getD h.capacity h.tag length index fallback

end ProofForge.Wasm.Near.Sdk.Store
