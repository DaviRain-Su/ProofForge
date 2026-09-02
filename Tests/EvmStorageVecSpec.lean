import ProofForge
import Examples.Evm.EvmVecLog
import Examples.Evm.EvmVecStack

/-!
R5-010 focused suite: persistent bounded EVM storage-vector (UInt64) policy truth tables,
compile-time descriptor pins with fail-closed variants, consumer host behavior through ordinary
typed state, and extraction-level proofs that both consumers' declared layouts equal the real EVM
state flattening — including the fixed-vector table and the dynamic-index load/store emission
shapes.

Host note: unlike the Address component stubs, every `StorageVec` decision is a pure scalar
function, so the host truth tables below are the real policy semantics. `Access.requireOwner`
keeps its host-true stub, so admin gates pass on host; the Anvil matrix owns the real
authorization and revert-data checks.
-/

namespace Tests.EvmStorageVecSpec

open ProofForge.Evm.Sdk
open ProofForge.Evm.Sdk.Storage.Static
open Lean Elab Command

/-! ## Policy truth tables (capacity 4) -/

-- well-formedness: length ≤ capacity; a corrupted over-capacity length is malformed
#guard StorageVec.wellFormed 4 0 && StorageVec.wellFormed 4 4
#guard !StorageVec.wellFormed 4 5
#guard StorageVec.isEmpty 0 && !StorageVec.isEmpty 1
#guard !StorageVec.isFull 4 3 && StorageVec.isFull 4 4 && StorageVec.isFull 4 5

-- push: admissible strictly below capacity; full and malformed fail closed
#guard StorageVec.canPush 4 0 && StorageVec.canPush 4 3
#guard !StorageVec.canPush 4 4 && !StorageVec.canPush 4 5

-- pop: admissible on a canonical nonzero length; empty and malformed fail closed
#guard StorageVec.canPop 4 1 && StorageVec.canPop 4 4
#guard !StorageVec.canPop 4 0 && !StorageVec.canPop 4 5
#guard StorageVec.popIndex 4 == 3 && StorageVec.popIndex 1 == 0

-- active-prefix reads/writes: index < length on a canonical length; OOB and malformed closed
#guard StorageVec.canGet 4 2 0 && StorageVec.canGet 4 2 1
#guard !StorageVec.canGet 4 2 2 && !StorageVec.canGet 4 0 0 && !StorageVec.canGet 4 5 0
#guard StorageVec.canSet 4 1 0 && !StorageVec.canSet 4 1 1 && !StorageVec.canSet 4 5 0

-- clear resets only canonical storage; malformed lengths are never silently repaired
#guard StorageVec.canClear 4 0 && StorageVec.canClear 4 4 && !StorageVec.canClear 4 5
#guard StorageVec.clearedLength == 0

/-! ## Descriptor declaration and fail-closed validation -/

def sampleVec :=
  StorageVec.declare Layout.root "values" "count" 3

#guard sampleVec.handle.values.baseSlot == 0
#guard sampleVec.handle.values.length? == some 3
#guard sampleVec.handle.values.elementSlots? == some 1
#guard sampleVec.handle.count.slot? == some 3
#guard sampleVec.handle.count.width? == some 8
#guard sampleVec.handle.wellFormed
#guard sampleVec.next.nextSlot == 4
#guard sampleVec.next.wellFormed
#guard sampleVec.next.matchesFlattened
  [("values_0", 8), ("values_1", 8), ("values_2", 8), ("count", 8)]

-- fail closed at the descriptor level: zero capacity, non-adjacent count, wrong payload shape
#guard !(StorageVec.declare Layout.root "values" "count" 0).handle.wellFormed

def misalignedCount : StorageVec.Descriptor 2 :=
  let values := Layout.root.array (α := Vector UInt64 2) "values" .u64 2
  let count := values.next.uint64 "gap" -- one extra scalar breaks adjacency
  let tail := count.next.uint64 "count"
  { values := values.handle, count := tail.handle }

#guard !misalignedCount.wellFormed

def wrongPayload : StorageVec.Descriptor 2 :=
  let values := Layout.root.array (α := Vector UInt64 2) "values" .u16 2
  let count := values.next.uint64 "count"
  { values := values.handle, count := count.handle }

#guard !wrongPayload.wellFormed

def wrongCountPayload : StorageVec.Descriptor 2 :=
  let values := Layout.root.array (α := Vector UInt64 2) "values" .u64 2
  let count : Handle UInt64 :=
    { name := "count", baseSlot := 2, spec := .leaf .u16 }
  { values := values.handle, count }

#guard !wrongCountPayload.wellFormed

/-! ## Consumer descriptor and layout pins -/

#guard Examples.Evm.EvmVecLog.declared.handle.log.wellFormed
#guard Examples.Evm.EvmVecLog.declared.handle.log.values.baseSlot == 3
#guard Examples.Evm.EvmVecLog.declared.handle.log.count.slot? == some 7
#guard Examples.Evm.EvmVecLog.declared.handle.admin.wideLeaves? == some 3
#guard Examples.Evm.EvmVecLog.layout.nextSlot == 8
#guard Examples.Evm.EvmVecLog.layout.wellFormed

#guard Examples.Evm.EvmVecStack.declared.handle.stack.wellFormed
#guard Examples.Evm.EvmVecStack.declared.handle.stack.values.baseSlot == 0
#guard Examples.Evm.EvmVecStack.declared.handle.stack.count.slot? == some 3
#guard Examples.Evm.EvmVecStack.layout.nextSlot == 4
#guard Examples.Evm.EvmVecStack.layout.wellFormed

def logSlots : List (String × Nat) :=
  [("admin_w0", 8), ("admin_w1", 8), ("admin_w2", 8),
    ("entries_0", 8), ("entries_1", 8), ("entries_2", 8), ("entries_3", 8), ("count", 8)]

def stackSlots : List (String × Nat) :=
  [("items_0", 8), ("items_1", 8), ("items_2", 8), ("depth", 8)]

#guard Examples.Evm.EvmVecLog.layout.matchesFlattened logSlots
#guard Examples.Evm.EvmVecStack.layout.matchesFlattened stackSlots

/-! ## Consumer host behavior through ordinary typed state -/

open Examples.Evm.EvmVecLog in
#guard (init ⟨1, 2, 3⟩).count == 0 && countOf (init ⟨1, 2, 3⟩) == 0 &&
  entryAt (init ⟨1, 2, 3⟩) 0 == 0

-- append, then reads observe exactly the active prefix
open Examples.Evm.EvmVecLog in
#guard match record (init ⟨1, 2, 3⟩) 11 with
  | .ok (s, r) => r == 1 && s.count == 1 && s.entries[0]! == 11 && entryAt s 0 == 11 &&
      entryAt s 1 == 0
  | _ => false

open Examples.Evm.EvmVecLog in
#guard match record (init ⟨1, 2, 3⟩) 11 with
  | .ok (s1, _) =>
      (match record s1 22 with
       | .ok (t, r) =>
           r == 2 && t.count == 2 && t.entries[0]! == 11 && t.entries[1]! == 22 &&
             entryAt t 1 == 22 && entryAt t 2 == 0
       | _ => false)
  | _ => false

-- amend touches only the selected slot; OOB amend is the typed error with state unchanged
open Examples.Evm.EvmVecLog in
#guard match record (init ⟨1, 2, 3⟩) 11 with
  | .ok (s, _) =>
      (match amend s 0 99 with
       | .ok (t, r) =>
           r == 99 && t.entries[0]! == 99 && t.count == 1 &&
             (match amend t 1 5 with
              | .error .oob => true
              | _ => false)
       | _ => false)
  | _ => false

-- wipe resets only the length; the stale backing slot is unreachable through entryAt
open Examples.Evm.EvmVecLog in
#guard match record (init ⟨1, 2, 3⟩) 11 with
  | .ok (s, _) =>
      (match wipe s with
       | .ok (t, r) => r == 0 && t.count == 0 && t.entries[0]! == 11 && entryAt t 0 == 0
       | _ => false)
  | _ => false

-- corrupted persistent length fails every mutation before changing state
open Examples.Evm.EvmVecLog in
#guard match record ({ init ⟨1, 2, 3⟩ with count := 5 }) 11 with
  | .error .malformed => true
  | _ => false

open Examples.Evm.EvmVecLog in
#guard match amend ({ init ⟨1, 2, 3⟩ with count := 5 }) 0 11 with
  | .error .malformed => true
  | _ => false

open Examples.Evm.EvmVecLog in
#guard match wipe ({ init ⟨1, 2, 3⟩ with count := 5 }) with
  | .error .malformed => true
  | _ => false

-- a full log rejects record with the CapExceeded revert value (host stub returns it as data)
open Examples.Evm.EvmVecLog in
#guard match record (init ⟨1, 2, 3⟩) 1 with
  | .ok (s1, _) =>
      (match record s1 2 with
       | .ok (s2, _) =>
           (match record s2 3 with
            | .ok (s3, _) =>
                (match record s3 4 with
                 | .ok (s4, _) =>
                     s4.count == 4 &&
                       (match record s4 5 with
                        | .ok (t, _) => t.count == 4
                        | _ => false)
                 | _ => false)
            | _ => false)
       | _ => false)
  | _ => false

open Examples.Evm.EvmVecStack in
#guard (init 7).depth == 1 && (init 7).items[0]! == 7 && topOf (init 7) == 7 &&
  depthOf (init 7) == 1

-- push to capacity, then the full decision closes; pop returns the active prefix in LIFO order
open Examples.Evm.EvmVecStack in
#guard match push (init 7) 8 with
  | .ok (s1, r1) =>
      r1 == 2 && s1.depth == 2 && topOf s1 == 8 &&
        (match push s1 9 with
         | .ok (s2, r2) =>
             r2 == 3 && s2.depth == 3 && topOf s2 == 9 &&
               (match push s2 10 with
                | .ok (t, _) => t.depth == 3 && t.items == s2.items
                | _ => false)
         | _ => false)
  | _ => false

open Examples.Evm.EvmVecStack in
#guard match push (init 7) 8 with
  | .ok (s, _) =>
      (match pop s with
       | .ok (t, v) =>
           v == 8 && t.depth == 1 &&
             (match pop t with
              | .ok (u, v2) =>
                  v2 == 7 && u.depth == 0 &&
                    (match pop u with
                     | .error .empty => true
                     | _ => false)
              | _ => false)
       | _ => false)
  | _ => false

-- popped/cleared slots stay stale in the backing field but unreachable
open Examples.Evm.EvmVecStack in
#guard match push (init 7) 8 with
  | .ok (s, _) =>
      (match clearAll s with
       | .ok (t, r) => r == 0 && t.depth == 0 && t.items[1]! == 8 && topOf t == 0
       | _ => false)
  | _ => false

open Examples.Evm.EvmVecStack in
#guard match push ({ init 7 with depth := 4 }) 8 with
  | .error .malformed => true
  | _ => false

open Examples.Evm.EvmVecStack in
#guard match pop ({ init 7 with depth := 4 }) with
  | .error .malformed => true
  | _ => false

open Examples.Evm.EvmVecStack in
#guard match clearAll ({ init 7 with depth := 4 }) with
  | .error .malformed => true
  | _ => false

/-! ## Extraction proof: declared layout == real EVM state flattening, with the existing
fixed-vector dynamic-index load/store emission shapes -/

private def expectVecLayout (module : Name) (expectedSlots : List (String × Nat))
    (expectedVectors : List (String × Nat × Nat × Nat)) (expectedEntries expectedErrors : List String) :
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
  let slots := program.slots.toList.map fun s => (s.name, s.width)
  unless slots == expectedSlots do
    throwError s!"{module}: extracted static slots diverge from the declared layout: {slots}"
  let vectors := program.vectors.toList.map fun v => (v.name, v.baseSlot, v.length, v.strideSlots)
  unless vectors == expectedVectors do
    throwError s!"{module}: extracted vectors diverge from the declared layout: {vectors}"
  let entries := program.entries.toList.map (·.ixName)
  for entry in expectedEntries do
    unless entries.contains entry do
      throwError s!"{module}: missing extracted storage-vector entry {entry} in {entries}"
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

elab "#pf_guard_evm_vec_log" : command =>
  expectVecLayout `Examples.Evm.EvmVecLog logSlots [("entries", 3, 4, 1)]
    ["record", "amend", "wipe", "countOf", "entryAt", "adminOf"] ["malformed", "oob"]

elab "#pf_guard_evm_vec_stack" : command =>
  expectVecLayout `Examples.Evm.EvmVecStack stackSlots [("items", 0, 3, 1)]
    ["push", "pop", "clearAll", "depthOf", "topOf"] ["malformed", "empty"]

#pf_guard_evm_vec_log
#pf_guard_evm_vec_stack

end Tests.EvmStorageVecSpec
