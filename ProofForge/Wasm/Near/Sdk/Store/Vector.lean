import ProofForge.Attr
import ProofForge.Core.Value
import ProofForge.Wasm.Near.Codec
import ProofForge.Wasm.Near.Sdk.Storage

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

/-- Compile-time four-byte namespace, represented as a little-endian `UInt32` literal. -/
abbrev Prefix4 := Nat

def Prefix4.wellFormed (tag : Prefix4) : Bool :=
  tag ≤ 0xffffffff

@[pf_inline] def Prefix4.bounded (tag : Nat) : Prefix4 :=
  tag

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
  let p := UInt64.ofNat tag
  { length := 8
    values := #v[
      (p &&& 0xff).toUInt8,
      ((p >>> 8) &&& 0xff).toUInt8,
      ((p >>> 16) &&& 0xff).toUInt8,
      ((p >>> 24) &&& 0xff).toUInt8,
      (index &&& 0xff).toUInt8,
      ((index >>> 8) &&& 0xff).toUInt8,
      ((index >>> 16) &&& 0xff).toUInt8,
      ((index >>> 24) &&& 0xff).toUInt8
    ] }

/-- Standalone Borsh `UInt64`: exactly eight little-endian bytes, with no length tag. -/
@[pf_inline] def DirectVector64.elementValue
    (_vector : DirectVector64) (value : UInt64) : BoundedBytes 8 :=
  { length := 8
    values := #v[
      (value &&& 0xff).toUInt8,
      ((value >>> 8) &&& 0xff).toUInt8,
      ((value >>> 16) &&& 0xff).toUInt8,
      ((value >>> 24) &&& 0xff).toUInt8,
      ((value >>> 32) &&& 0xff).toUInt8,
      ((value >>> 40) &&& 0xff).toUInt8,
      ((value >>> 48) &&& 0xff).toUInt8,
      ((value >>> 56) &&& 0xff).toUInt8
    ] }

/-- Decode the active exact-width raw-storage result, or return `fallback` for absent,
oversized, or malformed slots. This consumes no storage operation by itself. -/
@[pf_inline] def DirectVector64.resultValueD
    (_vector : DirectVector64) (fallback : UInt64) : UInt64 :=
  let result : ResultBuffer := 8
  if result.status = 1 then
    if result.fits then
      if result.length = 8 then
        (result.byte 0).toUInt64 |||
          ((result.byte 1).toUInt64 <<< 8) |||
          ((result.byte 2).toUInt64 <<< 16) |||
          ((result.byte 3).toUInt64 <<< 24) |||
          ((result.byte 4).toUInt64 <<< 32) |||
          ((result.byte 5).toUInt64 <<< 40) |||
          ((result.byte 6).toUInt64 <<< 48) |||
          ((result.byte 7).toUInt64 <<< 56)
      else fallback
    else fallback
  else fallback

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

end ProofForge.Wasm.Near.Sdk.Store
