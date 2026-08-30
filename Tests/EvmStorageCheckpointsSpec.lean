import ProofForge
import ProofForge.Evm.Sdk.StorageCheckpoints
import Examples.EvmCheckpointBook
import Examples.EvmCheckpointTrace

/-!
R5-018 focused suite: bounded UInt64 checkpoint descriptor geometry, strict-order/update/lower-
bound truth tables, two application policies, malformed-state behavior, and extraction evidence
that the implementation remains ordinary static vectors plus one count slot.
-/

namespace Tests.EvmStorageCheckpointsSpec

open ProofForge.Evm.Sdk
open ProofForge.Evm.Sdk.Storage.Static
open Lean Elab Command

/-! ## Runtime policy truth tables -/

#guard StorageCheckpoints.ordered 0 0 0 0 0
#guard StorageCheckpoints.ordered 1 7 0 0 0
#guard StorageCheckpoints.ordered 4 7 9 12 20
#guard !StorageCheckpoints.ordered 2 7 7 0 0
#guard !StorageCheckpoints.ordered 3 7 9 8 0

#guard StorageCheckpoints.wellFormed 4 0 0 0 0 0
#guard StorageCheckpoints.wellFormed 4 4 7 9 12 20
#guard !StorageCheckpoints.wellFormed 4 5 7 9 12 20
#guard !StorageCheckpoints.wellFormed 4 3 7 7 12 0
#guard !StorageCheckpoints.wellFormed 0 0 0 0 0 0
#guard !StorageCheckpoints.wellFormed 5 0 0 0 0 0

-- Empty append, monotonic append, and same-latest overwrite are disjoint decisions.
#guard StorageCheckpoints.canAppend 4 0 0 0 0 0 7
#guard StorageCheckpoints.canAppend 4 2 7 9 0 0 12
#guard !StorageCheckpoints.canAppend 4 2 7 9 0 0 9
#guard !StorageCheckpoints.canAppend 4 2 7 9 0 0 8
#guard StorageCheckpoints.canOverwrite 4 2 7 9 0 0 9
#guard !StorageCheckpoints.canOverwrite 4 2 7 9 0 0 12
#guard StorageCheckpoints.canOverwrite 4 4 7 9 12 20 20
#guard !StorageCheckpoints.canAppend 4 4 7 9 12 20 21
#guard StorageCheckpoints.isDecreasing 4 4 7 9 12 20 19
#guard !StorageCheckpoints.isDecreasing 4 4 7 9 12 20 20

#guard StorageCheckpoints.latestIndex 4 == 3
#guard StorageCheckpoints.latestKey 0 0 0 0 0 == 0
#guard StorageCheckpoints.latestKey 3 7 9 12 0 == 12
#guard StorageCheckpoints.appendedCount 3 == 4

-- lower bound means first key >= query; count is the not-found sentinel.
#guard StorageCheckpoints.lowerBoundIndex 4 0 7 9 12 20 == 0
#guard StorageCheckpoints.lowerBoundIndex 4 7 7 9 12 20 == 0
#guard StorageCheckpoints.lowerBoundIndex 4 8 7 9 12 20 == 1
#guard StorageCheckpoints.lowerBoundIndex 4 12 7 9 12 20 == 2
#guard StorageCheckpoints.lowerBoundIndex 4 21 7 9 12 20 == 4
#guard StorageCheckpoints.hasLowerBound 4 3
#guard !StorageCheckpoints.hasLowerBound 4 4

/-! ## Descriptor geometry and fail-closed variants -/

def sample := StorageCheckpoints.declare Layout.root "keys" "values" "count" 4

#guard sample.handle.keys.baseSlot == 0
#guard sample.handle.keys.length? == some 4
#guard sample.handle.values.baseSlot == 4
#guard sample.handle.values.length? == some 4
#guard sample.handle.count.slot? == some 8
#guard sample.handle.wellFormed
#guard sample.next.nextSlot == 9
#guard sample.next.matchesFlattened
  [("keys_0", 8), ("keys_1", 8), ("keys_2", 8), ("keys_3", 8),
    ("values_0", 8), ("values_1", 8), ("values_2", 8), ("values_3", 8), ("count", 8)]

#guard !(StorageCheckpoints.declare Layout.root "keys" "values" "count" 0).handle.wellFormed
#guard !(StorageCheckpoints.declare Layout.root "keys" "values" "count" 5).handle.wellFormed

def displacedValues : StorageCheckpoints.Descriptor 2 :=
  let keys := Layout.root.array (α := Vector UInt64 2) "keys" .u64 2
  let gap := keys.next.uint64 "gap"
  let values := gap.next.array (α := Vector UInt64 2) "values" .u64 2
  let count := values.next.uint64 "count"
  { keys := keys.handle, values := values.handle, count := count.handle }

def wrongValues : StorageCheckpoints.Descriptor 2 :=
  let keys := Layout.root.array (α := Vector UInt64 2) "keys" .u64 2
  let values := keys.next.array (α := Vector UInt64 2) "values" .u16 2
  let count := values.next.uint64 "count"
  { keys := keys.handle, values := values.handle, count := count.handle }

#guard !displacedValues.wellFormed
#guard !wrongValues.wellFormed

/-! ## Consumer host behavior -/

open Examples.EvmCheckpointBook in
#guard match push (init ⟨1, 2, 3⟩) 10 100 with
  | .ok (s1, n1) =>
      n1 == 1 && s1.count == 1 && latestValue s1 == 100 && lowerValue s1 0 == 100 &&
        lowerValue s1 11 == 0 &&
        (match push s1 20 200 with
         | .ok (s2, n2) =>
             n2 == 2 && latestValue s2 == 200 && lowerValue s2 11 == 200 &&
               (match push s2 20 250 with
                | .ok (s3, n3) =>
                    n3 == 2 && s3.count == 2 && s3.keys[1]! == 20 &&
                      s3.values[1]! == 250 && latestValue s3 == 250
                | _ => false)
         | _ => false)
  | _ => false

open Examples.EvmCheckpointBook in
#guard match push (init ⟨1, 2, 3⟩) 10 100 with
  | .ok (s, _) =>
      (match push s 9 90 with | .error .unordered => true | _ => false)
  | _ => false

open Examples.EvmCheckpointBook in
#guard match push ({ init ⟨1, 2, 3⟩ with
    keys := #v[10, 10, 0, 0], values := #v[1, 2, 0, 0], count := 2 }) 11 3 with
  | .error .malformed => true
  | _ => false

open Examples.EvmCheckpointTrace in
#guard match push (init 0) 5 50 with
  | .ok (s1, r1) =>
      r1 == 50 &&
        (match push s1 8 80 with
         | .ok (s2, _) =>
             (match push s2 12 120 with
              | .ok (s3, _) =>
                  s3.count == 3 && lowerValue s3 6 == 80 && latestValue s3 == 120 &&
                    (match push s3 13 130 with | .error .full => true | _ => false) &&
                    (match push s3 12 121 with
                     | .ok (s4, r4) => r4 == 121 && s4.count == 3 && latestValue s4 == 121
                     | _ => false)
              | _ => false)
         | _ => false)
  | _ => false

/-! ## Extraction: two vectors + adjacent count, no checkpoint-specific target operation -/

def bookSlots : List (String × Nat) :=
  [("admin_w0", 8), ("admin_w1", 8), ("admin_w2", 8),
    ("keys_0", 8), ("keys_1", 8), ("keys_2", 8), ("keys_3", 8),
    ("values_0", 8), ("values_1", 8), ("values_2", 8), ("values_3", 8), ("count", 8)]

def traceSlots : List (String × Nat) :=
  [("keys_0", 8), ("keys_1", 8), ("keys_2", 8),
    ("values_0", 8), ("values_1", 8), ("values_2", 8), ("count", 8)]

#guard Examples.EvmCheckpointBook.declared.handle.trace.wellFormed
#guard Examples.EvmCheckpointBook.layout.matchesFlattened bookSlots
#guard Examples.EvmCheckpointTrace.declared.handle.trace.wellFormed
#guard Examples.EvmCheckpointTrace.layout.matchesFlattened traceSlots

private def expectCheckpointLayout (module : Name) (expectedSlots : List (String × Nat))
    (expectedVectors : List (String × Nat × Nat × Nat)) (expectedErrors : List String) :
    CommandElabM Unit := do
  let env ← getEnv
  let source ←
    match ProofForge.Extract.extractModuleIR env module with
    | .ok source => pure source
    | .error reason => throwError reason
  let program ←
    match ProofForge.Evm.IR.fromExtracted source with
    | .ok program => pure program
    | .error reason => throwError reason
  let slots := program.slots.toList.map fun slot => (slot.name, slot.width)
  unless slots == expectedSlots do
    throwError s!"{module}: checkpoint static slots diverged: {slots}"
  let vectors := program.vectors.toList.map fun vector =>
    (vector.name, vector.baseSlot, vector.length, vector.strideSlots)
  unless vectors == expectedVectors do
    throwError s!"{module}: checkpoint vectors diverged: {vectors}"
  let entries := program.entries.toList.map (·.ixName)
  for entry in ["latestValue", "lowerValue", "push"] do
    unless entries.contains entry do
      throwError s!"{module}: missing checkpoint entry {entry}"
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
  unless yul.contains "sload(add(" && yul.contains "sstore(add(" do
    throwError s!"{module}: fixed-vector checkpoint load/store path is missing"

elab "#pf_guard_evm_checkpoint_book" : command =>
  expectCheckpointLayout `Examples.EvmCheckpointBook bookSlots
    [("keys", 3, 4, 1), ("values", 7, 4, 1)] ["unordered", "malformed"]

elab "#pf_guard_evm_checkpoint_trace" : command =>
  expectCheckpointLayout `Examples.EvmCheckpointTrace traceSlots
    [("keys", 0, 3, 1), ("values", 3, 3, 1)] ["unordered", "full", "malformed"]

#pf_guard_evm_checkpoint_book
#pf_guard_evm_checkpoint_trace

end Tests.EvmStorageCheckpointsSpec
