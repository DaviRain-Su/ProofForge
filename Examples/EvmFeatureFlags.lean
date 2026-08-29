import ProofForge
import ProofForge.Evm.Sdk.StorageBitmap

/-!
R5-015 consumer A: owner-managed feature flags over the `Evm.Sdk.StorageBitmap` persistent
bitmap policy (capacity 128 bits = 2 full words, so the word boundary at bit 64 and the final
in-range bit 127 are both reachable, and bit 128 is the first OOB index).

`declared` threads the `Storage.Static` cursor in the exact declaration order of `State`; the
`StorageBitmap.Descriptor` bundle is compile-time data erased before extraction. Every entry
reads and writes state through ordinary typed `State` field/`Vector` accesses: the SDK owns only
the bounds/word/mask policy (`inRange`/`wordIndexOf`/`maskOf`/`containsOf`/`setOf`/`clearOf`/
`toggleOf`), and each physical write is a visible literal field update of exactly one word slot.
`Tests/EvmBitmapSpec` proves the extracted slots and the `flags` vector entry equal the declared
layout, and `runtime-tests/evm/anvil_bitmap_flags.sh` covers the enable/disable/toggle, idempotence,
word-boundary, final-bit, OOB, and unauthorized matrix plus state persistence across reverts.

Policy: the owner gates every mutation; an OOB mutation reverts with the typed `oob()` error and
stores nothing; OOB reads return the `0` fallback without reverting. The inner compiler guard's
`else` is unreachable under an admissible `inRange` decision (`index < 128` implies
`index / 64 < 2`) and maps to the typed `malformed()` terminal, exactly like `EvmVecLog`.
-/

namespace Examples.EvmFeatureFlags

open ProofForge.Evm.Sdk

/-- Compile-time bit capacity of the flag bitmap. -/
abbrev capacity : Nat := 128

/-- The same capacity as the compiler-erased scalar the SDK policy helpers consume in extracted
code. The fixed-vector compiler guards below use the plain literal `2` (the word count),
matching the existing `Vector` extraction contract (`EvmStaticRoster`, `Lang`, `EvmVecLog`). -/
@[pf_inline] def capU64 : UInt64 := 128

structure State where
  owner : Address
  /-- Fixed word table of the flag bitmap; every word is live state (no runtime length). -/
  flags : Vector UInt64 2
  deriving Repr, DecidableEq, Inhabited

/-- Compile-time handles for the static fields of `State`. -/
structure Handles where
  owner : Storage.Static.Handle Address
  bitmap : StorageBitmap.Descriptor capacity

/-- Static layout declaration in the exact declaration order of `State`. -/
@[pf_inline] def declared : Storage.Static.Allocated Handles :=
  let owner := Storage.Static.Layout.root.address "owner"
  let bitmap := StorageBitmap.declare owner.next "flags" capacity
  { handle := { owner := owner.handle, bitmap := bitmap.handle }, next := bitmap.next }

/-- The accumulated static layout: slots `0..4` (`owner_w0..w2:8@0..2`, `flags_0:8@3`,
`flags_1:8@4`). -/
@[pf_inline] def layout : Storage.Static.Layout := declared.next

inductive Error where
  | oob
  | malformed
  deriving Repr, DecidableEq, Inhabited, BEq

@[pf_entry]
def init (owner : Address) : State :=
  { owner, flags := #v[0, 0] }

@[pf_entry]
def ownerOf (s : State) : Address :=
  s.owner

/-- Checked flag read: `1` when the in-range bit is set, else `0`. OOB indexes return the `0`
fallback without reverting and never alias a lower bit. -/
@[pf_entry]
def isEnabled (s : State) (index : UInt64) : UInt64 :=
  if StorageBitmap.inRange capU64 index then
    let w := StorageBitmap.wordIndexOf index
    if StorageBitmap.containsOf s.flags[w.toNat]! index then 1 else 0
  else
    0

/-- Owner-gated set. OOB reverts with `oob()` before any store; setting a set bit is an
idempotent same-word write. The physical write is the literal update of `flags[index / 64]`. -/
@[pf_entry]
def enable (s : State) (index : UInt64) : Except Error (State × UInt64) :=
  if Access.requireOwner s.owner then
    if StorageBitmap.inRange capU64 index then
      let w := StorageBitmap.wordIndexOf index
      if h : w.toNat < 2 then
        let cur := s.flags[w.toNat]
        .ok ({ s with flags := s.flags.set w.toNat (StorageBitmap.setOf cur index) h }, 1)
      else
        .error .malformed
    else
      .error .oob
  else
    .ok (s, Access.ownerViolation)

/-- Owner-gated clear. OOB reverts with `oob()` before any store; clearing a clear bit is an
idempotent same-word write. The physical write touches only `flags[index / 64]`. -/
@[pf_entry]
def disable (s : State) (index : UInt64) : Except Error (State × UInt64) :=
  if Access.requireOwner s.owner then
    if StorageBitmap.inRange capU64 index then
      let w := StorageBitmap.wordIndexOf index
      if h : w.toNat < 2 then
        let cur := s.flags[w.toNat]
        .ok ({ s with flags := s.flags.set w.toNat (StorageBitmap.clearOf cur index) h }, 0)
      else
        .error .malformed
    else
      .error .oob
  else
    .ok (s, Access.ownerViolation)

/-- Owner-gated toggle, returning the bit's new value (`1` = now set). OOB reverts with `oob()`
before any store. The physical write touches only `flags[index / 64]`. -/
@[pf_entry]
def toggle (s : State) (index : UInt64) : Except Error (State × UInt64) :=
  if Access.requireOwner s.owner then
    if StorageBitmap.inRange capU64 index then
      let w := StorageBitmap.wordIndexOf index
      if h : w.toNat < 2 then
        let next := StorageBitmap.toggleOf s.flags[w.toNat] index
        .ok ({ s with flags := s.flags.set w.toNat next h },
          if StorageBitmap.containsOf next index then 1 else 0)
      else
        .error .malformed
    else
      .error .oob
  else
    .ok (s, Access.ownerViolation)

end Examples.EvmFeatureFlags
