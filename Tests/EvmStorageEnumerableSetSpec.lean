import ProofForge
import ProofForge.Evm.Sdk.StorageEnumerableSet
import Examples.Evm.EvmAllowlist
import Examples.Evm.EvmIdRegistry

/-!
Focused suite for the persistent bounded EVM enumerable-set policy: descriptor geometry,
position+1 index encoding, fail-closed mutation decisions, swap-remove policy, two independent
consumers, and extraction evidence for the ordinary static-vector plus hashed-map composition.

The SDK deliberately owns decisions rather than hidden state transitions. The current extractor
requires each consumer to keep its fixed `Vector` field and bounds proof visible. The structural
checks below therefore pin both sides of that boundary: no new Runtime/Ops/IR/Emit vocabulary,
and last/only removal must not issue the middle-removal vector move or moved-key map repair.
-/

namespace Tests.EvmStorageEnumerableSetSpec

open ProofForge.Evm.Sdk
open ProofForge.Evm.Sdk.Storage.Static
open Lean Elab Command

/-! ## Position encoding and mutation policy -/

-- Position+1 keeps zero as the absent sentinel while admitting key 0 as an ordinary key.
#guard StorageEnumerableSet.absent 0 && !StorageEnumerableSet.absent 1
#guard StorageEnumerableSet.insertPosition 0 == 1
#guard StorageEnumerableSet.insertPosition 3 == 4
#guard StorageEnumerableSet.indexOf 1 == 0
#guard StorageEnumerableSet.indexOf 4 == 3
#guard StorageEnumerableSet.isPresent 1 1 0 0
#guard StorageEnumerableSet.isPresent 4 4 9 9
#guard !StorageEnumerableSet.isPresent 0 1 0 0
#guard !StorageEnumerableSet.isPresent 1 1 8 9

-- Count, insertion, and enumeration decisions all fail closed at the fixed capacity.
#guard StorageEnumerableSet.wellFormed 4 0 && StorageEnumerableSet.wellFormed 4 4
#guard !StorageEnumerableSet.wellFormed 4 5
#guard StorageEnumerableSet.canInsert 4 0 0 && StorageEnumerableSet.canInsert 4 3 0
#guard !StorageEnumerableSet.canInsert 4 4 0
#guard !StorageEnumerableSet.canInsert 4 2 1
#guard !StorageEnumerableSet.canInsert 4 5 0
#guard StorageEnumerableSet.canValueAt 4 3 0 && StorageEnumerableSet.canValueAt 4 3 2
#guard !StorageEnumerableSet.canValueAt 4 3 3 && !StorageEnumerableSet.canValueAt 4 5 0
#guard StorageEnumerableSet.lastIndex 1 == 0 && StorageEnumerableSet.lastIndex 4 == 3

-- Removal validates count, encoded position, capacity, and the backing key before any write.
#guard StorageEnumerableSet.positionLive 1 1
#guard StorageEnumerableSet.positionLive 4 4
#guard !StorageEnumerableSet.positionLive 0 1
#guard !StorageEnumerableSet.positionLive 2 0
#guard !StorageEnumerableSet.positionLive 4 2
#guard StorageEnumerableSet.canRemove 4 3 2
#guard !StorageEnumerableSet.canRemove 4 3 0
#guard !StorageEnumerableSet.canRemove 4 3 4
#guard !StorageEnumerableSet.canRemove 4 5 2
#guard StorageEnumerableSet.forged 4 3 && !StorageEnumerableSet.forged 0 3

-- Only a middle removal needs swap-and-repair. Last and only removals clear just the removed key
-- and decrement count; this is the reusable policy split consumed by both examples.
#guard StorageEnumerableSet.movesLast 1 2
#guard !StorageEnumerableSet.movesLast 2 2
#guard !StorageEnumerableSet.movesLast 1 1

/-! ## Descriptor geometry and fail-closed variants -/

def sampleSet := StorageEnumerableSet.declare
  Layout.root "values" "count" Storage.Layout.root.u64Map.handle 3

#guard sampleSet.handle.values.baseSlot == 0
#guard sampleSet.handle.values.length? == some 3
#guard sampleSet.handle.values.elementSlots? == some 1
#guard sampleSet.handle.count.slot? == some 3
#guard sampleSet.handle.positions.base == 0
#guard sampleSet.handle.wellFormed
#guard sampleSet.next.nextSlot == 4
#guard sampleSet.next.matchesFlattened
  [("values_0", 8), ("values_1", 8), ("values_2", 8), ("count", 8)]

#guard !(StorageEnumerableSet.declare
  Layout.root "values" "count" Storage.Layout.root.u64Map.handle 0).handle.wellFormed

def misalignedCount : StorageEnumerableSet.Descriptor 2 :=
  let values := Layout.root.array (α := Vector UInt64 2) "values" .u64 2
  let gap := values.next.uint64 "gap"
  let count := gap.next.uint64 "count"
  { values := values.handle, count := count.handle, positions := Storage.Layout.root.u64Map.handle }

def wrongValues : StorageEnumerableSet.Descriptor 2 :=
  let values := Layout.root.array (α := Vector UInt64 2) "values" .u16 2
  let count := values.next.uint64 "count"
  { values := values.handle, count := count.handle, positions := Storage.Layout.root.u64Map.handle }

def wrongCount : StorageEnumerableSet.Descriptor 2 :=
  let values := Layout.root.array (α := Vector UInt64 2) "values" .u64 2
  let count : Handle UInt64 := { name := "count", baseSlot := 2, spec := .leaf .u16 }
  { values := values.handle, count, positions := Storage.Layout.root.u64Map.handle }

#guard !misalignedCount.wellFormed
#guard !wrongValues.wellFormed
#guard !wrongCount.wellFormed

/-! ## Consumer layouts and host-visible state transitions -/

#guard Examples.Evm.EvmAllowlist.declared.handle.set.wellFormed
#guard Examples.Evm.EvmAllowlist.declared.handle.admin.wideLeaves? == some 3
#guard Examples.Evm.EvmAllowlist.declared.handle.set.values.baseSlot == 3
#guard Examples.Evm.EvmAllowlist.declared.handle.set.count.slot? == some 7
#guard Examples.Evm.EvmAllowlist.declared.handle.set.positions.base == 0
#guard Examples.Evm.EvmAllowlist.layout.nextSlot == 8
#guard Examples.Evm.EvmAllowlist.layout.wellFormed

#guard Examples.Evm.EvmIdRegistry.declared.handle.registry.wellFormed
#guard Examples.Evm.EvmIdRegistry.declared.handle.registry.values.baseSlot == 0
#guard Examples.Evm.EvmIdRegistry.declared.handle.registry.count.slot? == some 3
#guard Examples.Evm.EvmIdRegistry.declared.handle.registry.positions.base == 1
#guard Examples.Evm.EvmIdRegistry.layout.nextSlot == 4
#guard Examples.Evm.EvmIdRegistry.layout.wellFormed

def allowlistSlots : List (String × Nat) :=
  [("admin_w0", 8), ("admin_w1", 8), ("admin_w2", 8),
    ("members_0", 8), ("members_1", 8), ("members_2", 8), ("members_3", 8),
    ("count", 8)]

def registrySlots : List (String × Nat) :=
  [("ids_0", 8), ("ids_1", 8), ("ids_2", 8), ("count", 8)]

#guard Examples.Evm.EvmAllowlist.layout.matchesFlattened allowlistSlots
#guard Examples.Evm.EvmIdRegistry.layout.matchesFlattened registrySlots

-- Runtime map reads are intentionally host stubs, but insertion still exercises the real
-- ordinary-State vector/count transition. Key 0 is accepted as data because only map value 0 is
-- the absence sentinel.
open Examples.Evm.EvmAllowlist in
#guard match grant (init ⟨1, 2, 3⟩) 0 with
  | .ok (s, r) => r && s.count == 1 && s.members[0]! == 0 && memberAt s 0 == 0
  | _ => false

open Examples.Evm.EvmAllowlist in
#guard match grant (init ⟨1, 2, 3⟩) 9 with
  | .ok (s, r) => r && s.count == 1 && s.members[0]! == 9 && memberAt s 0 == 9 &&
      memberAt s 1 == 0
  | _ => false

open Examples.Evm.EvmAllowlist in
#guard match grant ({ init ⟨1, 2, 3⟩ with count := 5 }) 9 with
  | .error .malformed => true
  | _ => false

open Examples.Evm.EvmIdRegistry in
#guard match enroll (init 0) 0 with
  | .ok (s, r) => r && s.count == 1 && s.ids[0]! == 0 && idAt s 0 == 0
  | _ => false

open Examples.Evm.EvmIdRegistry in
#guard match enroll (init 0) 7 with
  | .ok (s, r) => r && s.count == 1 && s.ids[0]! == 7 && idAt s 0 == 7 && idAt s 1 == 0
  | _ => false

open Examples.Evm.EvmIdRegistry in
#guard match enroll ({ init 0 with count := 4 }) 7 with
  | .error .malformed => true
  | _ => false

/-! ## Extraction proof: physical shape plus optimized middle/last removal paths -/

private abbrev Op := ProofForge.Extract.IR.Op

private def isMapSet : Op → Bool
  | .ext (.evm (.component (.hashedMap (.setU64 ..)))) => true
  | _ => false

private def isIndexSet : Op → Bool
  | .indexSetLeaf .. | .indexSet .. => true
  | _ => false

private partial def findSequence (fuel : Nat) (ops : Array Op)
    (predicate : Array Op → Bool) : Option (Array Op) :=
  if predicate ops then some ops
  else match fuel with
    | 0 => none
    | fuel' + 1 => ops.findSome? fun
        | .ite _ _ _ thn els =>
            findSequence fuel' thn predicate <|> findSequence fuel' els predicate
        | .forBody _ body => findSequence fuel' body predicate
        | _ => none

private def storeNames (ops : Array Op) : Array String :=
  ops.filterMap fun
    | .storeField name _ => some name
    | _ => none

private def hasRemovalShape (ops : Array Op) (mapSets indexSets : Nat) : Bool :=
  ops.countP isMapSet == mapSets && ops.countP isIndexSet == indexSets &&
    storeNames ops == #["count"] &&
    ops.countP (fun | .returnU64 _ => true | _ => false) == 1

private def expectEnumerableLayout (module : Name) (expectedSlots : List (String × Nat))
    (expectedVector : String × Nat × Nat × Nat) (removeEntry : String)
    (expectedEntries expectedErrors : List String) : CommandElabM Unit := do
  let env ← getEnv
  let source ←
    match ProofForge.Extract.extractModuleIR env module with
    | .ok source => pure source
    | .error reason => throwError reason
  let some sourceRemoval := source.methods.find? (·.ixName == removeEntry)
    | throwError s!"{module}: missing source removal entry {removeEntry}"
  let some middle := findSequence 24 sourceRemoval.ops (hasRemovalShape · 2 1)
    | throwError s!"{module}.{removeEntry}: middle removal lost swap/moved-key repair/clear/count"
  let some last := findSequence 24 sourceRemoval.ops (hasRemovalShape · 1 0)
    | throwError s!"{module}.{removeEntry}: last/only removal still moves or repairs the final key"
  unless middle.countP isIndexSet == 1 && last.countP isIndexSet == 0 do
    throwError s!"{module}.{removeEntry}: removal resource split drifted"

  let program ←
    match ProofForge.Evm.IR.fromExtracted source with
    | .ok program => pure program
    | .error reason => throwError reason
  let slots := program.slots.toList.map fun slot => (slot.name, slot.width)
  unless slots == expectedSlots do
    throwError s!"{module}: extracted static slots diverged: {slots}"
  let vectors := program.vectors.toList.map fun vector =>
    (vector.name, vector.baseSlot, vector.length, vector.strideSlots)
  unless vectors == [expectedVector] do
    throwError s!"{module}: extracted enumerable backing vector diverged: {vectors}"
  let entries := program.entries.toList.map (·.ixName)
  for entry in expectedEntries do
    unless entries.contains entry do
      throwError s!"{module}: missing entry {entry}"

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
      throwError s!"{module}: ABI omitted {errorName}()"
  unless yul.contains "sload(add(" && yul.contains "sstore(add(" &&
      yul.contains "keccak256(0, 64)" do
    throwError s!"{module}: static-vector or hashed-position path is missing"
  -- No capacity scan: this component must remain O(1), not become a linear-search set.
  unless (yul.splitOn "for { let ").length == 2 do
    throwError s!"{module}: unexpected loop over enumerable-set capacity"

elab "#pf_guard_evm_allowlist" : command =>
  expectEnumerableLayout `Examples.Evm.EvmAllowlist allowlistSlots ("members", 3, 4, 1)
    "revoke"
    ["adminOf", "sizeOf", "containsOf", "memberAt", "grant", "revoke"]
    ["malformed", "duplicate"]

elab "#pf_guard_evm_id_registry" : command =>
  expectEnumerableLayout `Examples.Evm.EvmIdRegistry registrySlots ("ids", 0, 3, 1)
    "release" ["sizeOf", "containsOf", "idAt", "enroll", "release"]
    ["malformed", "duplicate", "full"]

#pf_guard_evm_allowlist
#pf_guard_evm_id_registry

end Tests.EvmStorageEnumerableSetSpec
