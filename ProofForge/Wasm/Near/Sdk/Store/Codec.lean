import ProofForge.Attr
import ProofForge.Core.Value
import ProofForge.Wasm.Near.Sdk.Storage

/-!
# Shared bounded NEAR store codecs

These recipes model the fixed-width subset shared by the direct collection foundations. `Prefix4`
is a compile-time four-byte namespace. It is intentionally narrower than near-sdk-rs
`IntoStorageKey`, which accepts arbitrary byte prefixes.
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

/-- Four-byte prefix followed by a little-endian `UInt32` suffix. -/
@[pf_inline] def Prefix4.keyUInt32 (tag : Prefix4) (suffix : UInt64) : BoundedBytes 8 :=
  let p := UInt64.ofNat tag
  { length := 8
    values := #v[
      (p &&& 0xff).toUInt8,
      ((p >>> 8) &&& 0xff).toUInt8,
      ((p >>> 16) &&& 0xff).toUInt8,
      ((p >>> 24) &&& 0xff).toUInt8,
      (suffix &&& 0xff).toUInt8,
      ((suffix >>> 8) &&& 0xff).toUInt8,
      ((suffix >>> 16) &&& 0xff).toUInt8,
      ((suffix >>> 24) &&& 0xff).toUInt8
    ] }

/-- Four-byte prefix followed by a standalone little-endian Borsh `UInt64`. -/
@[pf_inline] def Prefix4.keyUInt64 (tag : Prefix4) (suffix : UInt64) : BoundedBytes 12 :=
  let p := UInt64.ofNat tag
  { length := 12
    values := #v[
      (p &&& 0xff).toUInt8,
      ((p >>> 8) &&& 0xff).toUInt8,
      ((p >>> 16) &&& 0xff).toUInt8,
      ((p >>> 24) &&& 0xff).toUInt8,
      (suffix &&& 0xff).toUInt8,
      ((suffix >>> 8) &&& 0xff).toUInt8,
      ((suffix >>> 16) &&& 0xff).toUInt8,
      ((suffix >>> 24) &&& 0xff).toUInt8,
      ((suffix >>> 32) &&& 0xff).toUInt8,
      ((suffix >>> 40) &&& 0xff).toUInt8,
      ((suffix >>> 48) &&& 0xff).toUInt8,
      ((suffix >>> 56) &&& 0xff).toUInt8
    ] }

/-- Standalone Borsh `UInt64`: exactly eight little-endian bytes, with no length tag. -/
@[pf_inline] def borshUInt64 (value : UInt64) : BoundedBytes 8 :=
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

/-- Standalone Borsh `u128`: exactly 16 little-endian bytes, low limb first. -/
@[pf_inline] def borshNearToken (value : UInt128) : BoundedBytes 16 :=
  { length := 16
    values := #v[
      (value.w0 &&& 0xff).toUInt8,
      ((value.w0 >>> 8) &&& 0xff).toUInt8,
      ((value.w0 >>> 16) &&& 0xff).toUInt8,
      ((value.w0 >>> 24) &&& 0xff).toUInt8,
      ((value.w0 >>> 32) &&& 0xff).toUInt8,
      ((value.w0 >>> 40) &&& 0xff).toUInt8,
      ((value.w0 >>> 48) &&& 0xff).toUInt8,
      ((value.w0 >>> 56) &&& 0xff).toUInt8,
      (value.w1 &&& 0xff).toUInt8,
      ((value.w1 >>> 8) &&& 0xff).toUInt8,
      ((value.w1 >>> 16) &&& 0xff).toUInt8,
      ((value.w1 >>> 24) &&& 0xff).toUInt8,
      ((value.w1 >>> 32) &&& 0xff).toUInt8,
      ((value.w1 >>> 40) &&& 0xff).toUInt8,
      ((value.w1 >>> 48) &&& 0xff).toUInt8,
      ((value.w1 >>> 56) &&& 0xff).toUInt8
    ] }

/-- Decode the active exact-width raw-storage result, or return `fallback` for absent,
oversized, or malformed values. This consumes no storage operation by itself. -/
@[pf_inline] def resultUInt64D (fallback : UInt64) : UInt64 :=
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

/-- Decode the low limb of one exact 16-byte Borsh `u128` from the active storage result. -/
@[pf_inline] def resultNearTokenW0D (fallback : UInt64) : UInt64 :=
  let result : ResultBuffer := 16
  if result.status = 1 then
    if result.fits then
      if result.length = 16 then
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

/-- Decode the high limb of one exact 16-byte Borsh `u128` from the active storage result. Both
limb decoders apply the same status/fits/exact-length gate before observing any result byte. -/
@[pf_inline] def resultNearTokenW1D (fallback : UInt64) : UInt64 :=
  let result : ResultBuffer := 16
  if result.status = 1 then
    if result.fits then
      if result.length = 16 then
        (result.byte 8).toUInt64 |||
          ((result.byte 9).toUInt64 <<< 8) |||
          ((result.byte 10).toUInt64 <<< 16) |||
          ((result.byte 11).toUInt64 <<< 24) |||
          ((result.byte 12).toUInt64 <<< 32) |||
          ((result.byte 13).toUInt64 <<< 40) |||
          ((result.byte 14).toUInt64 <<< 48) |||
          ((result.byte 15).toUInt64 <<< 56)
      else fallback
    else fallback
  else fallback

end ProofForge.Wasm.Near.Sdk.Store
