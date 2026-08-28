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
