import ProofForge.Attr
import ProofForge.Core.Value
import ProofForge.Wasm.Near.Sdk.Store.Codec

/-!
# Bounded direct NEAR LookupMap and LookupSet storage

This is the fixed-width default-Identity subset of current near-sdk-rs `store::LookupMap` and
`store::LookupSet`:

* map key: four-byte prefix followed by standalone Borsh `UInt64` key;
* map value: standalone Borsh `UInt64` value;
* set key: the same prefix/key recipe;
* set value: the empty byte string.

Prefixes are compile-time `Prefix4` values. The caller owns namespace separation between every
map, set, vector, raw key, and compiler state-field key. SHA-256/Keccak key policies are absent.

`DirectLookupMap64` writes immediately. Its durable key/value bytes match the Rust Identity
layout, but its mutation timing does not model Rust `LookupMap` cache/flush/Drop behavior.
`DirectLookupSet64` immediate writes match the current Rust set policy. Neither type provides
generic codecs, borrowed keys, references, entry APIs, iteration, or collection cardinality.
-/

namespace ProofForge.Wasm.Near.Sdk.Store

open ProofForge.Core.Value
open ProofForge.Wasm.Near.Sdk.Storage

/-- Compile-time four-byte Identity namespace for UInt64-to-UInt64 lookup entries. -/
abbrev DirectLookupMap64 := Prefix4

def DirectLookupMap64.wellFormed (map : DirectLookupMap64) : Bool :=
  Prefix4.wellFormed map

@[pf_inline] def DirectLookupMap64.bounded (tag : Nat) : DirectLookupMap64 :=
  tag

@[pf_inline] def DirectLookupMap64.elementKey
    (map : DirectLookupMap64) (key : UInt64) : BoundedBytes 12 :=
  (map : Prefix4).keyUInt64 key

@[pf_inline] def DirectLookupMap64.elementValue
    (_map : DirectLookupMap64) (value : UInt64) : BoundedBytes 8 :=
  borshUInt64 value

/-- Read and decode a value, or return `fallback` for absence or malformed storage. -/
@[pf_inline] def DirectLookupMap64.getD
    (map : DirectLookupMap64) (key fallback : UInt64) : UInt64 :=
  let result : ResultBuffer := 8
  let _ := result.read (map.elementKey key)
  resultUInt64D fallback

@[pf_inline] def DirectLookupMap64.has
    (map : DirectLookupMap64) (key : UInt64) : UInt64 :=
  let result : ResultBuffer := 8
  let _ := result.hasKey (map.elementKey key)
  result.status

/-- Immediately write `value`, returning nearcore status 0 for insert or 1 for replacement.
Unlike Rust `LookupMap.insert`, this does not load and return the old value. -/
@[pf_inline] def DirectLookupMap64.put
    (map : DirectLookupMap64) (key value : UInt64) : UInt64 :=
  let result : ResultBuffer := 8
  let _ := result.write (map.elementKey key) (map.elementValue value)
  result.status

/-- Immediately remove an entry, returning nearcore status 0 for absent or 1 for present. Unlike
Rust `LookupMap.remove`, this does not deserialize and return the old value. -/
@[pf_inline] def DirectLookupMap64.remove
    (map : DirectLookupMap64) (key : UInt64) : UInt64 :=
  let result : ResultBuffer := 8
  let _ := result.remove (map.elementKey key)
  result.status

/-- Compile-time four-byte Identity namespace for UInt64 set members. -/
abbrev DirectLookupSet64 := Prefix4

def DirectLookupSet64.wellFormed (set : DirectLookupSet64) : Bool :=
  Prefix4.wellFormed set

@[pf_inline] def DirectLookupSet64.bounded (tag : Nat) : DirectLookupSet64 :=
  tag

@[pf_inline] def DirectLookupSet64.elementKey
    (set : DirectLookupSet64) (value : UInt64) : BoundedBytes 12 :=
  (set : Prefix4).keyUInt64 value

/-- near-sdk-rs `store::LookupSet` stores an empty byte string, not a Borsh unit marker. -/
@[pf_inline] def DirectLookupSet64.elementValue
    (_set : DirectLookupSet64) : BoundedBytes 1 :=
  { length := 0, values := #v[0] }

@[pf_inline] def DirectLookupSet64.has
    (set : DirectLookupSet64) (value : UInt64) : UInt64 :=
  let result : ResultBuffer := 1
  let _ := result.hasKey (set.elementKey value)
  result.status

/-- Immediately insert a member, returning raw storage status 0 when newly inserted and 1 when
already present. This is the inverse of the Boolean returned by Rust `LookupSet.insert`. -/
@[pf_inline] def DirectLookupSet64.insert
    (set : DirectLookupSet64) (value : UInt64) : UInt64 :=
  let result : ResultBuffer := 1
  let _ := result.write (set.elementKey value) set.elementValue
  result.status

/-- Immediately remove a member; returns 1 when present and 0 when absent. -/
@[pf_inline] def DirectLookupSet64.remove
    (set : DirectLookupSet64) (value : UInt64) : UInt64 :=
  let result : ResultBuffer := 1
  let _ := result.remove (set.elementKey value)
  result.status

/-- Source handle for a LookupMap namespace: compile-time `Prefix4` only (no capacity; keys are
caller-supplied). Methods are `@[pf_inline]` facades so Extract erases to raw map ops. -/
structure DirectLookupMap64.Handle where
  tag : DirectLookupMap64
  deriving Repr

@[pf_inline] def DirectLookupMap64.handle (tag : Nat) : DirectLookupMap64.Handle :=
  { tag := tag }

@[pf_inline] def DirectLookupMap64.Handle.getD
    (h : DirectLookupMap64.Handle) (key fallback : UInt64) : UInt64 :=
  DirectLookupMap64.getD h.tag key fallback

@[pf_inline] def DirectLookupMap64.Handle.has
    (h : DirectLookupMap64.Handle) (key : UInt64) : UInt64 :=
  DirectLookupMap64.has h.tag key

@[pf_inline] def DirectLookupMap64.Handle.put
    (h : DirectLookupMap64.Handle) (key value : UInt64) : UInt64 :=
  DirectLookupMap64.put h.tag key value

@[pf_inline] def DirectLookupMap64.Handle.remove
    (h : DirectLookupMap64.Handle) (key : UInt64) : UInt64 :=
  DirectLookupMap64.remove h.tag key

/-- Source handle for a LookupSet namespace: compile-time `Prefix4` only. -/
structure DirectLookupSet64.Handle where
  tag : DirectLookupSet64
  deriving Repr

@[pf_inline] def DirectLookupSet64.handle (tag : Nat) : DirectLookupSet64.Handle :=
  { tag := tag }

@[pf_inline] def DirectLookupSet64.Handle.has
    (h : DirectLookupSet64.Handle) (value : UInt64) : UInt64 :=
  DirectLookupSet64.has h.tag value

@[pf_inline] def DirectLookupSet64.Handle.insert
    (h : DirectLookupSet64.Handle) (value : UInt64) : UInt64 :=
  DirectLookupSet64.insert h.tag value

@[pf_inline] def DirectLookupSet64.Handle.remove
    (h : DirectLookupSet64.Handle) (value : UInt64) : UInt64 :=
  DirectLookupSet64.remove h.tag value

end ProofForge.Wasm.Near.Sdk.Store
