import ProofForge
import ProofForge.Evm.Sdk.StorageBitmap

/-!
R5-015 consumer B: permissionless one-time claims over the `Evm.Sdk.StorageBitmap` persistent
bitmap policy (capacity 130 bits = 3 words, so the word table has a *partial* final word: bits
128 and 129 are live in word 2, and bit 130 is the first OOB index — an index that would alias
bit 2 of word 2 through `index % 64` if the `inRange` gate did not fail closed).

This consumer's policy is deliberately different from `Examples.EvmFeatureFlags`: there is no
owner at all, claims are one-time (a replay reverts with the typed `already()` error instead of
an idempotent write), there is no clear/toggle, and the constructor is parameterless-state
(seeded like `EvmOrderedStorage`). `declared` threads the `Storage.Static` cursor in the exact
declaration order of `State`; every entry reads and writes state through ordinary typed `State`
field/`Vector` accesses and each physical write is a visible literal update of exactly one word
slot. `Tests/EvmBitmapSpec` proves the extracted slots and the `claimed` vector entry equal the
declared layout, and `runtime-tests/evm/anvil_bitmap_claims.sh` covers claim replay, the 63/64
word boundary, the final in-range bit 129, OOB aliasing probes, and state persistence across
reverts.

Enumeration, counting, and clear-all over the bitmap are intentionally absent: they would need
a `wordCount`-bounded loop, which this SDK policy does not provide and this consumer does not
fake.
-/

namespace Examples.EvmClaimBitmap

open ProofForge.Evm.Sdk

/-- Compile-time bit capacity of the claims bitmap: 130 bits pack into 3 words, so word 2 is a
partial word holding exactly bits 128 and 129. -/
abbrev capacity : Nat := 130

/-- The same capacity as the compiler-erased scalar the SDK policy helpers consume in extracted
code. The fixed-vector compiler guards below use the plain literal `3` (the word count),
matching the existing `Vector` extraction contract (`EvmStaticRoster`, `Lang`, `EvmVecStack`). -/
@[pf_inline] def capU64 : UInt64 := 130

structure State where
  /-- Fixed word table of the claims bitmap; every word is live state (no runtime length). -/
  claimed : Vector UInt64 3
  deriving Repr, DecidableEq, Inhabited

/-- Compile-time handles for the static fields of `State`. -/
structure Handles where
  bitmap : StorageBitmap.Descriptor capacity

/-- Static layout declaration in the exact declaration order of `State`. -/
@[pf_inline] def declared : Storage.Static.Allocated Handles :=
  let bitmap := StorageBitmap.declare Storage.Static.Layout.root "claimed" capacity
  { handle := { bitmap := bitmap.handle }, next := bitmap.next }

/-- The accumulated static layout: slots `0..2` (`claimed_0:8@0`, `claimed_1:8@1`,
`claimed_2:8@2`). -/
@[pf_inline] def layout : Storage.Static.Layout := declared.next

inductive Error where
  | oob
  | already
  | malformed
  deriving Repr, DecidableEq, Inhabited, BEq

/-- Constructor is seeded like `EvmOrderedStorage`: the word table starts all-zero. -/
@[pf_entry]
def init (_seed : UInt64) : State :=
  { claimed := #v[0, 0, 0] }

/-- Checked claim read: `1` when the in-range bit is set, else `0`. OOB indexes return the `0`
fallback without reverting and never alias a lower bit (bit 130 does not report bit 2). -/
@[pf_entry]
def hasClaimed (s : State) (index : UInt64) : UInt64 :=
  if StorageBitmap.inRange capU64 index then
    let w := StorageBitmap.wordIndexOf index
    if StorageBitmap.containsOf s.claimed[w.toNat]! index then 1 else 0
  else
    0

/-- Permissionless one-time claim. OOB reverts with `oob()` before any store; a replay of an
already-claimed index reverts with `already()` before any store. The physical write is the
literal update of `claimed[index / 64]`. -/
@[pf_entry]
def claim (s : State) (index : UInt64) : Except Error (State × UInt64) :=
  if StorageBitmap.inRange capU64 index then
    let w := StorageBitmap.wordIndexOf index
    if h : w.toNat < 3 then
      let cur := s.claimed[w.toNat]
      if StorageBitmap.containsOf cur index then
        .error .already
      else
        .ok ({ s with claimed := s.claimed.set w.toNat (StorageBitmap.setOf cur index) h }, 1)
    else
      .error .malformed
  else
    .error .oob

end Examples.EvmClaimBitmap
