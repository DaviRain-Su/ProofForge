import ProofForge.Attr
import ProofForge.Core.Value

/-!
# Target-neutral bounded collections

Pure source operations over `Core.Value.BoundedVec`. The host `Vector` is an elaboration and
extraction carrier only: every operation preserves the compile-time capacity and changes at most
the runtime length and fixed element frame. Target adapters remain responsible for choosing Borsh,
ABI, account, memory, or storage geometry.

These helpers are `pf_inline` source combinators, not VM effects. They must lower to the existing
bounded comparisons and vector index reads/writes; adding another vector operation here must not
add a Vector-specific Core Op, target IR constructor, or Emit recipe.
-/

namespace ProofForge.Core.Value.BoundedVec

/-- The largest capacity representable by the `UInt32` length field. Target codec budgets normally
impose a much smaller limit before extraction. -/
@[pf_inline] def capacityIsRepresentable (n : Nat) : Bool :=
  n < UInt32.size

/-- The runtime length is canonical for this compile-time capacity. -/
@[pf_inline] def wellFormed {α : Type} {n : Nat} (items : BoundedVec α n) : Bool :=
  capacityIsRepresentable n && items.length.toNat ≤ n

/-- Compile-time capacity exposed as a scalar source value. The codec/profile gate rejects
capacities outside its much smaller resource ceiling before target lowering. -/
@[pf_inline] def capacity {α : Type} {n : Nat} (items : BoundedVec α n) : UInt64 :=
  let _ := items
  UInt64.ofNat n

/-- Runtime number of active elements. -/
@[pf_inline] def size {α : Type} {n : Nat} (items : BoundedVec α n) : UInt64 :=
  items.length.toUInt64

@[pf_inline] def isEmpty {α : Type} {n : Nat} (items : BoundedVec α n) : Bool :=
  items.length == 0

/-- Invalid over-capacity frames are treated as full. Canonical target decoders reject such a
frame before the source method runs. -/
@[pf_inline] def isFull {α : Type} {n : Nat} (items : BoundedVec α n) : Bool :=
  n ≤ items.length.toNat

/-- Checked active-prefix lookup. Inactive fixed-frame slots are never observable through this
API, even though target adapters may keep them zeroed as scratch locals. -/
@[pf_inline] def get? {α : Type} {n : Nat} (items : BoundedVec α n) (index : UInt64) : Option α :=
  if hcapacity : index.toNat < n then
    if index < items.length.toUInt64 then some (items.values[index.toNat]'hcapacity) else none
  else
    none

/-- Checked lookup with an explicit allocation-free fallback. -/
@[pf_inline] def getD {α : Type} {n : Nat}
    (items : BoundedVec α n) (index : UInt64) (fallback : α) : α :=
  if hcapacity : index.toNat < n then
    if index < items.length.toUInt64 then (items.values[index.toNat]'hcapacity) else fallback
  else
    fallback

/-- Replace one active element without changing the runtime length. -/
@[pf_inline] def set? {α : Type} {n : Nat}
    (items : BoundedVec α n) (index : UInt64) (value : α) : Option (BoundedVec α n) :=
  if hcapacity : index.toNat < n then
    if index < items.length.toUInt64 then
      some { items with values := items.values.set index.toNat value hcapacity }
    else
      none
  else
    none

/-- Append to the fixed frame. Full or malformed frames return `none` without changing any value.
The returned index is zero-based, matching Rust `Vec` indexing and both target boundary codecs. -/
@[pf_inline] def push? {α : Type} {n : Nat} (items : BoundedVec α n) (value : α) :
    Option (BoundedVec α n × UInt64) :=
  let index := items.length.toNat
  if _hcapacity : n < UInt32.size then
    if hslot : index < n then
      let next : BoundedVec α n :=
        { length := items.length + 1
          values := items.values.set index value hslot }
      some (next, items.length.toUInt64)
    else
      none
  else
    none

/-- Remove the last active element. The inactive backing slot is intentionally left unchanged:
logical length owns reachability, while a target may choose to zero storage as a separate policy. -/
@[pf_inline] def pop? {α : Type} {n : Nat}
    (items : BoundedVec α n) : Option (BoundedVec α n × α) :=
  if items.length = 0 then
    none
  else
    let index := items.length.toNat - 1
    if hcapacity : index < n then
      some ({ items with length := items.length - 1 }, (items.values[index]'hcapacity))
    else
      none

/-- Drop every logical element without allocating or rewriting the fixed backing frame. -/
@[pf_inline] def clear {α : Type} {n : Nat} (items : BoundedVec α n) : BoundedVec α n :=
  { items with length := 0 }

end ProofForge.Core.Value.BoundedVec

/-!
## Bounded key/value semantics

`BoundedMap` is the target-neutral *logical* contract for an enumerable finite map. It deliberately
uses the shared fixed-frame vector rather than Lean/Std hash maps. SVM account storage and EVM
hashed/static storage may implement these semantics with different physical layouts; this type is
never permission to persist its host representation or a pointer.
-/

namespace ProofForge.Core.Collections

open ProofForge.Core.Value

structure Entry (κ υ : Type) where
  key : κ
  value : υ
  deriving Repr, BEq

/-- An unordered finite map with compile-time capacity and explicit active-prefix length. -/
structure BoundedMap (κ υ : Type) (capacity : Nat) where
  entries : BoundedVec (Entry κ υ) capacity

inductive ExistingValuePolicy where
  | reject
  | replace
  deriving Repr, BEq, Inhabited

namespace BoundedMap

def size (map : BoundedMap κ υ capacity) : UInt64 :=
  map.entries.size

def isEmpty (map : BoundedMap κ υ capacity) : Bool :=
  map.entries.isEmpty

def isFull (map : BoundedMap κ υ capacity) : Bool :=
  map.entries.isFull

/-- Zero-based active-prefix position of `key`. The scan bound is the compile-time capacity, not
runtime input. -/
def findIndex? [BEq κ] (map : BoundedMap κ υ capacity) (key : κ) : Option UInt64 :=
  if !map.entries.wellFormed then none
  else
    Id.run do
      for i in [0:capacity] do
        if UInt64.ofNat i < map.entries.length.toUInt64 then
          if let some entry := map.entries.get? (UInt64.ofNat i) then
            if entry.key == key then return some (UInt64.ofNat i)
      return none

def contains [BEq κ] (map : BoundedMap κ υ capacity) (key : κ) : Bool :=
  (map.findIndex? key).isSome

def get? [BEq κ] (map : BoundedMap κ υ capacity) (key : κ) : Option υ := do
  let index ← map.findIndex? key
  let entry ← map.entries.get? index
  return entry.value

/-- Insert a missing key, or apply the typed policy to an existing key. `none` means
duplicate-under-reject policy, full capacity, or a malformed input frame; no input value is mutated. -/
def insert? [BEq κ] (map : BoundedMap κ υ capacity) (key : κ) (value : υ)
    (existing : ExistingValuePolicy := .reject) : Option (BoundedMap κ υ capacity) :=
  match map.findIndex? key with
  | some index =>
      match existing with
      | .reject => none
      | .replace =>
          match map.entries.set? index { key, value } with
          | some entries => some { entries }
          | none => none
  | none =>
      match map.entries.push? { key, value } with
      | some (entries, _) => some { entries }
      | none => none

/-- Remove one key by moving the final active entry into its slot, then shrinking length. Ordering
is intentionally not part of the shared map contract. Returns the removed value with the new map. -/
def remove? [BEq κ] (map : BoundedMap κ υ capacity) (key : κ) :
    Option (BoundedMap κ υ capacity × υ) := do
  let index ← map.findIndex? key
  let removed ← map.entries.get? index
  let lastIndex := map.entries.size - 1
  let last ← map.entries.get? lastIndex
  let moved ← map.entries.set? index last
  let (entries, _) ← moved.pop?
  return ({ entries }, removed.value)

def clear (map : BoundedMap κ υ capacity) : BoundedMap κ υ capacity :=
  { entries := map.entries.clear }

/-- Canonical frames contain no duplicate active keys. This is a bounded semantic check, not a
target hash-table validator. -/
def wellFormed [BEq κ] (map : BoundedMap κ υ capacity) : Bool :=
  if !map.entries.wellFormed then false
  else Id.run do
    for i in [0:capacity] do
      if UInt64.ofNat i < map.entries.length.toUInt64 then
        let some left := map.entries.get? (UInt64.ofNat i) | return false
        for j in [i + 1:capacity] do
          if UInt64.ofNat j < map.entries.length.toUInt64 then
            let some right := map.entries.get? (UInt64.ofNat j) | return false
            if left.key == right.key then return false
    return true

end BoundedMap

/-- A finite set is the map contract with unit payload. It inherits the same explicit capacity,
active-prefix scan bound, and unordered removal policy. -/
abbrev BoundedSet (α : Type) (capacity : Nat) := BoundedMap α Unit capacity

namespace BoundedSet

def contains [BEq α] (set : BoundedSet α capacity) (value : α) : Bool :=
  BoundedMap.contains set value

def insert? [BEq α] (set : BoundedSet α capacity) (value : α) :
    Option (BoundedSet α capacity) :=
  BoundedMap.insert? set value ()

def remove? [BEq α] (set : BoundedSet α capacity) (value : α) :
    Option (BoundedSet α capacity) :=
  (BoundedMap.remove? set value).map (·.1)

end BoundedSet

end ProofForge.Core.Collections
