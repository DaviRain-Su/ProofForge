import ProofForge
import ProofForge.Evm.Sdk.StorageBitmap
import Examples.EvmFeatureFlags
import Examples.EvmClaimBitmap

/-!
R5-015 focused suite: persistent bounded EVM storage bitmap (packed UInt64 words) policy truth
tables at the bit/word/mask boundaries, compile-time descriptor pins with fail-closed variants,
agreement with the shared `Core.Collections.BoundedBitSet` logical semantics, consumer host
behavior through ordinary typed state, and extraction-level proofs that both consumers' declared
layouts equal the real EVM state flattening — including the fixed-vector table, the
dynamic-index load/store emission shapes, and the absence of any capacity loop.

Host note: unlike the Address component stubs, every `StorageBitmap` helper is a pure scalar
function, so the host truth tables below are the real policy semantics. `Access.requireOwner`
keeps its host-true stub, so the owner gate passes on host; the Anvil matrix owns the real
authorization and revert-data checks.
-/

namespace Tests.EvmBitmapSpec

open ProofForge.Evm.Sdk
open ProofForge.Evm.Sdk.Storage.Static
open ProofForge.Core.Collections
open Lean Elab Command

/-! ## Word-table geometry (shared with `BoundedBitSet`) -/

#guard StorageBitmap.wordCount 1 == 1 && StorageBitmap.wordCount 64 == 1
#guard StorageBitmap.wordCount 65 == 2 && StorageBitmap.wordCount 128 == 2
#guard StorageBitmap.wordCount 129 == 3 && StorageBitmap.wordCount 130 == 3
#guard StorageBitmap.wordCount 128 == bitSetWordCount 128 &&
  StorageBitmap.wordCount 130 == bitSetWordCount 130

/-! ## Policy truth tables: bounds, word index, mask (capacity 128 and 130) -/

-- bounds: bit 0, the 63/64 word boundary, the final in-range bit, and OOB all fail closed
#guard StorageBitmap.inRange 128 0 && StorageBitmap.inRange 128 63 &&
  StorageBitmap.inRange 128 64 && StorageBitmap.inRange 128 127
#guard !StorageBitmap.inRange 128 128 && !StorageBitmap.inRange 128 129 &&
  !StorageBitmap.inRange 128 18446744073709551615
#guard StorageBitmap.inRange 130 128 && StorageBitmap.inRange 130 129 &&
  !StorageBitmap.inRange 130 130 && !StorageBitmap.inRange 130 255

-- word index: pure `index / 64`; truthful past the capacity as arithmetic, gated by inRange
#guard StorageBitmap.wordIndexOf 0 == 0 && StorageBitmap.wordIndexOf 63 == 0
#guard StorageBitmap.wordIndexOf 64 == 1 && StorageBitmap.wordIndexOf 127 == 1
#guard StorageBitmap.wordIndexOf 128 == 2 && StorageBitmap.wordIndexOf 129 == 2

-- mask: pure `1 <<< (index % 64)`; no wrap at the word boundary, no aliasing across words
#guard StorageBitmap.maskOf 0 == 1 && StorageBitmap.maskOf 1 == 2
#guard StorageBitmap.maskOf 63 == 9223372036854775808
#guard StorageBitmap.maskOf 64 == 1 && StorageBitmap.maskOf 65 == 2
#guard StorageBitmap.maskOf 127 == 9223372036854775808 && StorageBitmap.maskOf 129 == 2

-- contains/set/clear/toggle over a single loaded word: boundary bits and idempotence
#guard !StorageBitmap.containsOf 0 0 && StorageBitmap.containsOf 1 0 &&
  !StorageBitmap.containsOf 1 1
#guard StorageBitmap.setOf 0 63 == 9223372036854775808 &&
  StorageBitmap.setOf (StorageBitmap.setOf 0 0) 63 == 9223372036854775809
#guard StorageBitmap.setOf (StorageBitmap.setOf 5 3) 3 == StorageBitmap.setOf 5 3
#guard StorageBitmap.clearOf 15 0 == 14 && StorageBitmap.clearOf 15 4 == 15 &&
  StorageBitmap.clearOf (StorageBitmap.clearOf 15 1) 1 == StorageBitmap.clearOf 15 1
#guard StorageBitmap.setOf (StorageBitmap.clearOf 0 63) 63 == 9223372036854775808
#guard StorageBitmap.toggleOf 0 64 == 1 && StorageBitmap.toggleOf 1 64 == 0 &&
  StorageBitmap.toggleOf (StorageBitmap.toggleOf 42 70) 70 == 42
-- set/clear/toggle of one bit never disturbs other bits of the same word
#guard StorageBitmap.setOf 9223372036854775808 0 == 9223372036854775809 &&
  StorageBitmap.clearOf 9223372036854775809 0 == 9223372036854775808 &&
  StorageBitmap.toggleOf 9223372036854775809 0 == 9223372036854775808

/-! ## Agreement with `Core.Collections.BoundedBitSet` logical semantics -/

def sampleSet : BoundedBitSet 128 := { words := #v[0, 0] }

-- in-range contains agrees with the SDK word test at 0 / 63 / 64 / 127; OOB is closed in both
#guard sampleSet.contains 0 == StorageBitmap.containsOf 0 0 &&
  sampleSet.contains 128 == false
#guard match sampleSet.insert? 63 with
  | some t =>
      t.words[0]! == StorageBitmap.setOf 0 63 && t.words[1]! == 0 &&
        t.contains 63 == true && t.contains 62 == false && t.contains 64 == false
  | none => false
#guard match sampleSet.insert? 64 with
  | some t =>
      t.words[1]! == StorageBitmap.setOf 0 64 && t.words[0]! == 0 && t.contains 64 == true
  | none => false
#guard match sampleSet.insert? 127 with
  | some t => t.words[1]! == StorageBitmap.setOf 0 127
  | none => false
-- OOB update returns none: no wrap, no alias of a lower bit
#guard (sampleSet.insert? 128).isNone && (sampleSet.remove? 128).isNone
#guard ((BoundedBitSet.empty 130).insert? 130).isNone &&
  ((BoundedBitSet.empty 130).insert? 129).isSome
-- remove/toggle agreement on a populated word
#guard match (sampleSet.insert? 5).bind (·.remove? 5) with
  | some t => t.words == sampleSet.words
  | none => false

/-! ## Descriptor declaration and fail-closed validation -/

def sampleBitmap := StorageBitmap.declare Layout.root "words" 128

#guard sampleBitmap.handle.words.baseSlot == 0
#guard sampleBitmap.handle.words.length? == some 2
#guard sampleBitmap.handle.words.elementSlots? == some 1
#guard sampleBitmap.handle.wellFormed
#guard sampleBitmap.next.nextSlot == 2
#guard sampleBitmap.next.wellFormed
#guard sampleBitmap.next.matchesFlattened [("words_0", 8), ("words_1", 8)]
-- a 130-bit table declares three consecutive word slots
#guard (StorageBitmap.declare Layout.root "words" 130).handle.words.length? == some 3
#guard (StorageBitmap.declare Layout.root "words" 130).next.matchesFlattened
  [("words_0", 8), ("words_1", 8), ("words_2", 8)]

-- fail closed at the descriptor level: zero bit capacity (also flattens to a zero word table)
#guard !(StorageBitmap.declare Layout.root "words" 0).handle.wellFormed

-- fail closed: bit capacity beyond the codec-representable bound
def oversizedBits : StorageBitmap.Descriptor UInt32.size :=
  { words := { name := "words", baseSlot := 0,
               spec := .arrayLeaves .u64 (StorageBitmap.wordCount UInt32.size) } }

#guard !oversizedBits.wellFormed

-- fail closed: mismatched word table (declared length disagrees with the bit capacity)
def mismatchedWords : StorageBitmap.Descriptor 128 :=
  { words := { name := "words", baseSlot := 0, spec := .arrayLeaves .u64 3 } }

#guard !mismatchedWords.wellFormed

-- fail closed: zero word table under a positive capacity
def zeroWords : StorageBitmap.Descriptor 64 :=
  { words := { name := "words", baseSlot := 0, spec := .arrayLeaves .u64 0 } }

#guard !zeroWords.wellFormed

-- fail closed: wrong static leaf shape (scalar slot / record / record array, not a word array)
def scalarTable : StorageBitmap.Descriptor 64 :=
  { words := { name := "words", baseSlot := 0, spec := .leaf .u64 } }

def recordTable : StorageBitmap.Descriptor 64 :=
  { words := { name := "words", baseSlot := 0, spec := .record [("word", .u64)] } }

def recordArrayTable : StorageBitmap.Descriptor 64 :=
  { words := { name := "words", baseSlot := 0, spec := .arrayRecords [("word", .u64)] 1 } }

#guard !scalarTable.wellFormed && !recordTable.wellFormed && !recordArrayTable.wellFormed

-- fail closed: non-UInt64 word payload
def narrowWords : StorageBitmap.Descriptor 128 :=
  { words := { name := "words", baseSlot := 0, spec := .arrayLeaves .u16 2 } }

#guard !narrowWords.wellFormed

-- fail closed: layout disagreement against the flattened slot table
#guard !sampleBitmap.next.matchesFlattened [("words_0", 8)]
#guard !sampleBitmap.next.matchesFlattened [("words_0", 8), ("words_1", 4)]
#guard !sampleBitmap.next.matchesFlattened [("words_0", 8), ("other_1", 8)]

/-! ## Consumer descriptor and layout pins -/

#guard Examples.EvmFeatureFlags.declared.handle.bitmap.wellFormed
#guard Examples.EvmFeatureFlags.declared.handle.bitmap.words.baseSlot == 3
#guard Examples.EvmFeatureFlags.declared.handle.bitmap.words.length? == some 2
#guard Examples.EvmFeatureFlags.declared.handle.owner.wideLeaves? == some 3
#guard Examples.EvmFeatureFlags.layout.nextSlot == 5
#guard Examples.EvmFeatureFlags.layout.wellFormed

#guard Examples.EvmClaimBitmap.declared.handle.bitmap.wellFormed
#guard Examples.EvmClaimBitmap.declared.handle.bitmap.words.baseSlot == 0
#guard Examples.EvmClaimBitmap.declared.handle.bitmap.words.length? == some 3
#guard Examples.EvmClaimBitmap.layout.nextSlot == 3
#guard Examples.EvmClaimBitmap.layout.wellFormed

def flagsSlots : List (String × Nat) :=
  [("owner_w0", 8), ("owner_w1", 8), ("owner_w2", 8), ("flags_0", 8), ("flags_1", 8)]

def claimsSlots : List (String × Nat) :=
  [("claimed_0", 8), ("claimed_1", 8), ("claimed_2", 8)]

#guard Examples.EvmFeatureFlags.layout.matchesFlattened flagsSlots
#guard Examples.EvmClaimBitmap.layout.matchesFlattened claimsSlots

/-! ## Consumer host behavior through ordinary typed state -/

open Examples.EvmFeatureFlags in
#guard (init ⟨1, 2, 3⟩).flags == #v[0, 0] && isEnabled (init ⟨1, 2, 3⟩) 0 == 0 &&
  isEnabled (init ⟨1, 2, 3⟩) 127 == 0 && isEnabled (init ⟨1, 2, 3⟩) 128 == 0

-- enable at the word boundary and the final bit: exact words, exact reads, idempotent rewrite
open Examples.EvmFeatureFlags in
#guard match enable (init ⟨1, 2, 3⟩) 63 with
  | .ok (s1, r1) =>
      r1 == 1 && s1.flags == #v[9223372036854775808, 0] && isEnabled s1 63 == 1 &&
        isEnabled s1 62 == 0 && isEnabled s1 64 == 0 &&
        (match enable s1 63 with
         | .ok (s2, _) => s2.flags == s1.flags
         | _ => false)
  | _ => false

open Examples.EvmFeatureFlags in
#guard match enable (init ⟨1, 2, 3⟩) 64 with
  | .ok (s1, _) =>
      s1.flags == #v[0, 1] && isEnabled s1 64 == 1 &&
        (match enable s1 127 with
         | .ok (s2, _) =>
             s2.flags == #v[0, 9223372036854775809] && isEnabled s2 127 == 1 &&
               isEnabled s2 126 == 0 && isEnabled s2 0 == 0
         | _ => false)
  | _ => false

-- disable clears exactly one bit, keeps neighbors, and is idempotent
open Examples.EvmFeatureFlags in
#guard match enable (init ⟨1, 2, 3⟩) 0 with
  | .ok (s1, _) =>
      (match enable s1 63 with
       | .ok (s2, _) =>
           (match disable s2 0 with
            | .ok (s3, r3) =>
                r3 == 0 && s3.flags == #v[9223372036854775808, 0] && isEnabled s3 0 == 0 &&
                  isEnabled s3 63 == 1 &&
                  (match disable s3 0 with
                   | .ok (s4, _) => s4.flags == s3.flags
                   | _ => false)
            | _ => false)
       | _ => false)
  | _ => false

-- toggle flips and reports the new value; toggling twice restores the exact word
open Examples.EvmFeatureFlags in
#guard match toggle (init ⟨1, 2, 3⟩) 100 with
  | .ok (s1, r1) =>
      r1 == 1 && s1.flags == #v[0, 68719476736] && isEnabled s1 100 == 1 &&
        (match toggle s1 100 with
         | .ok (s2, r2) => r2 == 0 && s2.flags == #v[0, 0] && isEnabled s2 100 == 0
         | _ => false)
  | _ => false

-- OOB mutations fail before any store; the boundary OOB index 128 does not alias bit 0
open Examples.EvmFeatureFlags in
#guard match enable (init ⟨1, 2, 3⟩) 128 with
  | .error .oob => true
  | _ => false

open Examples.EvmFeatureFlags in
#guard match enable (init ⟨1, 2, 3⟩) 0 with
  | .ok (s1, _) =>
      (match disable s1 128 with
       | .error .oob => s1.flags == #v[1, 0]
       | _ => false) &&
        (match toggle s1 18446744073709551615 with
         | .error .oob => s1.flags == #v[1, 0]
         | _ => false)
  | _ => false

open Examples.EvmClaimBitmap in
#guard (init 0).claimed == #v[0, 0, 0] && hasClaimed (init 0) 0 == 0 &&
  hasClaimed (init 0) 129 == 0 && hasClaimed (init 0) 130 == 0

-- claim at the 63/64 word boundary and the final in-range bit of the partial word
open Examples.EvmClaimBitmap in
#guard match claim (init 0) 63 with
  | .ok (s1, r1) =>
      r1 == 1 && s1.claimed == #v[9223372036854775808, 0, 0] &&
        (match claim s1 64 with
         | .ok (s2, _) =>
             s2.claimed == #v[9223372036854775808, 1, 0] && hasClaimed s2 63 == 1 &&
               hasClaimed s2 64 == 1 &&
               (match claim s2 129 with
                | .ok (s3, _) =>
                    s3.claimed == #v[9223372036854775808, 1, 2] && hasClaimed s3 129 == 1 &&
                      hasClaimed s3 128 == 0
                | _ => false)
         | _ => false)
  | _ => false

-- claim replay reverts with the typed error and stores nothing; OOB (incl. the aliasing probe
-- 130, whose `130 % 64 = 2` would hit the live word 2) reverts with the typed error
open Examples.EvmClaimBitmap in
#guard match claim (init 0) 2 with
  | .ok (s1, _) =>
      (match claim s1 2 with
       | .error .already => s1.claimed == #v[4, 0, 0]
       | _ => false) &&
        (match claim s1 130 with
         | .error .oob => s1.claimed == #v[4, 0, 0]
         | _ => false) &&
        (match claim s1 18446744073709551615 with
         | .error .oob => true
         | _ => false)
  | _ => false

/-! ## Extraction proof: declared layout == real EVM state flattening, with the existing
fixed-vector dynamic-index load/store emission shapes, the truthful word/mask arithmetic, and
no capacity loop -/

private def expectBitmapLayout (module : Name) (expectedSlots : List (String × Nat))
    (expectedVectors : List (String × Nat × Nat × Nat)) (expectedEntries expectedErrors : List String)
    (requiredYul : List String) : CommandElabM Unit := do
  let env ← getEnv
  let source ←
    match ProofForge.Extract.extractModuleIR env module with
    | .ok source => pure source
    | .error reason => throwError reason
  let program ←
    match ProofForge.Evm.IR.fromExtracted source with
    | .ok program => pure program
    | .error reason => throwError reason
  let slots := program.slots.toList.map fun s => (s.name, s.width)
  unless slots == expectedSlots do
    throwError s!"{module}: extracted static slots diverge from the declared layout: {slots}"
  let vectors := program.vectors.toList.map fun v => (v.name, v.baseSlot, v.length, v.strideSlots)
  unless vectors == expectedVectors do
    throwError s!"{module}: extracted vectors diverge from the declared layout: {vectors}"
  let entries := program.entries.toList.map (·.ixName)
  for entry in expectedEntries do
    unless entries.contains entry do
      throwError s!"{module}: missing extracted storage-bitmap entry {entry} in {entries}"
  let yul ←
    match ProofForge.Evm.Emit.emitYul program with
    | .ok yul => pure yul
    | .error reason => throwError reason
  let abi ←
    match ProofForge.Evm.Emit.emitAbiChecked program with
    | .ok abi => pure abi
    | .error reason => throwError reason
  for errorName in expectedErrors do
    unless abi.contains s!"\"type\":\"error\",\"name\":\"{errorName}\",\"inputs\":[]" do
      throwError s!"{module}: ABI omitted source custom error {errorName}()"
  for (_, width) in expectedSlots do
    unless width == 8 do
      throwError s!"{module}: non-UInt64 leaf width survived extraction"
  unless yul.contains "sstore(" && yul.contains "sload(" do
    throwError s!"{module}: expected ordinary static slot accesses in emitted Yul"
  unless yul.contains "sstore(add(" do
    throwError s!"{module}: expected the fixed-vector dynamic-index store path in emitted Yul"
  unless yul.contains "sload(add(" do
    throwError s!"{module}: expected the fixed-vector dynamic-index load path in emitted Yul"
  for needle in requiredYul do
    unless yul.contains needle do
      throwError s!"{module}: emitted Yul missing the word/mask arithmetic shape {needle}"
  -- No capacity loop: the only bounded `for` in emitted Yul is the never-called fixed-bytes ABI
  -- helper (bounded by a calldata `size`, never by the word-table capacity); the CFG dispatch
  -- loop `for { } 1 { } {` is method plumbing, not iteration over capacity.
  unless (yul.splitOn "for { let ").length == 2 do
    throwError s!"{module}: unexpected bounded loop over capacity in emitted Yul"
  -- the fixed-bytes helper is declared unconditionally; my consumers must never call it
  unless (yul.splitOn "pf_store_fixed_bytes(").length == 2 do
    throwError s!"{module}: unexpected fixed-bytes helper call in emitted Yul"

elab "#pf_guard_evm_bitmap_flags" : command =>
  expectBitmapLayout `Examples.EvmFeatureFlags flagsSlots [("flags", 3, 2, 1)]
    ["ownerOf", "isEnabled", "enable", "disable", "toggle"] ["oob", "malformed"]
    ["div(", "mod(", "shl(", "or(", "and(", "not(", "xor("]

elab "#pf_guard_evm_bitmap_claims" : command =>
  expectBitmapLayout `Examples.EvmClaimBitmap claimsSlots [("claimed", 0, 3, 1)]
    ["hasClaimed", "claim"] ["oob", "already", "malformed"]
    ["div(", "mod(", "shl(", "or(", "and("]

#pf_guard_evm_bitmap_flags
#pf_guard_evm_bitmap_claims

end Tests.EvmBitmapSpec
