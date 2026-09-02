import ProofForge
import ProofForge.Evm.Sdk.StorageEnumerableMap
import Examples.Evm.EvmConfigMap
import Examples.Evm.EvmScoreMap

/-!
R5-019 focused suite: descriptor composition over the enumerable-set index, disjoint position and
value namespaces, key/value zero behavior, insert/update/remove decisions, two independent
consumers, and extraction evidence for constant-time swap-remove with value clearing.
-/

namespace Tests.EvmStorageEnumerableMapSpec

open ProofForge.Evm.Sdk
open ProofForge.Evm.Sdk.Storage.Static
open Lean Elab Command

/-! ## Pure map policy -/

#guard StorageEnumerableMap.absent 0 && !StorageEnumerableMap.absent 1
#guard StorageEnumerableMap.canInsert 4 0 0
#guard !StorageEnumerableMap.canInsert 4 4 0
#guard !StorageEnumerableMap.canInsert 4 2 1
#guard StorageEnumerableMap.canUpdate 4 2 1 0 0
#guard StorageEnumerableMap.canUpdate 4 2 2 9 9
#guard !StorageEnumerableMap.canUpdate 4 2 3 9 9
#guard !StorageEnumerableMap.canUpdate 4 5 1 0 0
#guard StorageEnumerableMap.canRemove 4 3 2 7 7
#guard !StorageEnumerableMap.canRemove 4 3 2 8 7
#guard !StorageEnumerableMap.canRemove 4 3 0 0 0
#guard StorageEnumerableMap.canEntryAt 4 3 2
#guard !StorageEnumerableMap.canEntryAt 4 3 3
#guard !StorageEnumerableMap.canEntryAt 4 5 0
#guard StorageEnumerableMap.insertPosition 0 == 1
#guard StorageEnumerableMap.removedCount 3 == 2
#guard StorageEnumerableMap.movesLast 1 3
#guard !StorageEnumerableMap.movesLast 3 3
#guard StorageEnumerableMap.emptyValue == 0

/-! ## Descriptor geometry -/

def sample := StorageEnumerableMap.declare Layout.root "keys" "count"
  Storage.Layout.root.u64Map.handle Storage.Layout.root.u64Map.next.u64Map.handle 3

#guard sample.handle.index.values.baseSlot == 0
#guard sample.handle.index.values.length? == some 3
#guard sample.handle.index.count.slot? == some 3
#guard sample.handle.index.positions.base == 0
#guard sample.handle.entries.base == 1
#guard sample.handle.wellFormed
#guard sample.next.nextSlot == 4
#guard sample.next.matchesFlattened
  [("keys_0", 8), ("keys_1", 8), ("keys_2", 8), ("count", 8)]

def aliasedMaps := StorageEnumerableMap.declare Layout.root "keys" "count"
  Storage.Layout.root.u64Map.handle Storage.Layout.root.u64Map.handle 3

#guard !aliasedMaps.handle.wellFormed
#guard !(StorageEnumerableMap.declare Layout.root "keys" "count"
  Storage.Layout.root.u64Map.handle Storage.Layout.root.u64Map.next.u64Map.handle 0).handle.wellFormed

/-! ## Consumer geometry and host-visible inserts -/

def configSlots : List (String × Nat) :=
  [("admin_w0", 8), ("admin_w1", 8), ("admin_w2", 8),
    ("keys_0", 8), ("keys_1", 8), ("keys_2", 8), ("keys_3", 8), ("count", 8)]

def scoreSlots : List (String × Nat) :=
  [("players_0", 8), ("players_1", 8), ("players_2", 8), ("count", 8)]

#guard Examples.Evm.EvmConfigMap.declared.handle.table.wellFormed
#guard Examples.Evm.EvmConfigMap.declared.handle.table.index.positions.base == 0
#guard Examples.Evm.EvmConfigMap.declared.handle.table.entries.base == 1
#guard Examples.Evm.EvmConfigMap.layout.matchesFlattened configSlots

#guard Examples.Evm.EvmScoreMap.declared.handle.scores.wellFormed
#guard Examples.Evm.EvmScoreMap.declared.handle.scores.index.positions.base == 0
#guard Examples.Evm.EvmScoreMap.declared.handle.scores.entries.base == 1
#guard Examples.Evm.EvmScoreMap.layout.matchesFlattened scoreSlots

-- Host map leaves are irreducible zero stubs, but a fresh insertion exercises the real fixed key
-- and count transition. Key/value zero remain admissible because only position zero means absent.
open Examples.Evm.EvmConfigMap in
#guard match write (init ⟨1, 2, 3⟩) 0 0 with
  | .ok (s, r) => r && s.count == 1 && s.keys[0]! == 0 && keyAt s 0 == 0
  | _ => false

open Examples.Evm.EvmConfigMap in
#guard match write ({ init ⟨1, 2, 3⟩ with count := 5 }) 7 9 with
  | .error .malformed => true
  | _ => false

open Examples.Evm.EvmScoreMap in
#guard match put (init 0) 7 0 with
  | .ok (s, r) => r && s.count == 1 && s.players[0]! == 7 && playerAt s 0 == 7
  | _ => false

/-! ## Extraction shape -/

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

private def expectMapLayout (module : Name) (expectedSlots : List (String × Nat))
    (expectedVector : String × Nat × Nat × Nat) (removeEntry : String)
    (expectedEntries expectedErrors : List String) : CommandElabM Unit := do
  let env ← getEnv
  let source ←
    match ProofForge.Extract.extractModuleIR env module with
    | .ok source => pure source
    | .error reason => throwError reason
  let some removal := source.methods.find? (·.ixName == removeEntry)
    | throwError s!"{module}: missing map removal entry {removeEntry}"
  let some middle := findSequence 24 removal.ops (hasRemovalShape · 3 1)
    | throwError s!"{module}.{removeEntry}: middle removal lost move/repair/two clears/count"
  let some last := findSequence 24 removal.ops (hasRemovalShape · 2 0)
    | throwError s!"{module}.{removeEntry}: last removal did not clear position/value only"
  unless middle.countP isIndexSet == 1 && last.countP isIndexSet == 0 do
    throwError s!"{module}.{removeEntry}: map removal resource split drifted"

  let program ←
    match ProofForge.Evm.IR.fromExtracted source with
    | .ok program => pure program
    | .error reason => throwError reason
  let slots := program.slots.toList.map fun slot => (slot.name, slot.width)
  unless slots == expectedSlots do
    throwError s!"{module}: enumerable-map static slots diverged: {slots}"
  let vectors := program.vectors.toList.map fun vector =>
    (vector.name, vector.baseSlot, vector.length, vector.strideSlots)
  unless vectors == [expectedVector] do
    throwError s!"{module}: enumerable-map key vector diverged: {vectors}"
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
    throwError s!"{module}: static key vector or hashed map path is missing"
  unless (yul.splitOn "for { let ").length == 2 do
    throwError s!"{module}: unexpected capacity loop in O(1) enumerable map"

elab "#pf_guard_evm_config_map" : command =>
  expectMapLayout `Examples.Evm.EvmConfigMap configSlots ("keys", 3, 4, 1) "remove"
    ["adminOf", "sizeOf", "keyAt", "valueAt", "valueOf", "write", "remove"]
    ["malformed"]

elab "#pf_guard_evm_score_map" : command =>
  expectMapLayout `Examples.Evm.EvmScoreMap scoreSlots ("players", 0, 3, 1) "erase"
    ["sizeOf", "playerAt", "scoreAt", "scoreOf", "put", "erase"]
    ["full", "malformed"]

#pf_guard_evm_config_map
#pf_guard_evm_score_map

end Tests.EvmStorageEnumerableMapSpec
