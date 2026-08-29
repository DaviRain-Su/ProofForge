import ProofForge
import ProofForge.Evm.Sdk.StorageRing
import Examples.EvmRingMailbox
import Examples.EvmRingHistory

/-!
Focused suite: persistent fixed-capacity EVM storage ring queue (UInt64) policy truth tables,
compile-time descriptor pins with fail-closed variants, consumer host behavior through ordinary
typed state, and extraction-level proofs that both consumers' declared layouts equal the real
EVM state flattening — including the fixed-vector table and the dynamic-index load/store
emission shapes.

Host note: unlike the Address component stubs, every `StorageRing` decision is a pure scalar
function, so the host truth tables below are the real policy semantics (mirroring
`Core.Collections.BoundedQueue`'s canonical empty head). `Access.requireOwner` keeps its
host-true stub, so admin gates pass on host; the Anvil matrices own the real authorization and
revert-data checks.
-/

namespace Tests.EvmStorageRingSpec

open ProofForge.Evm.Sdk
open ProofForge.Evm.Sdk.Storage.Static
open Lean Elab Command

/-! ## Policy truth tables -/

-- well-formedness: head < capacity, live ≤ capacity, canonical head 0 while empty;
-- corrupted head/live pairs and a masked non-canonical empty head all fail closed
#guard StorageRing.wellFormed 5 0 0 && StorageRing.wellFormed 5 2 3 && StorageRing.wellFormed 5 4 4
#guard !StorageRing.wellFormed 5 5 0 && !StorageRing.wellFormed 5 2 6
#guard !StorageRing.wellFormed 5 3 0 && StorageRing.wellFormed 5 0 5 &&
  !StorageRing.wellFormed 0 0 0

#guard StorageRing.isEmpty 0 && !StorageRing.isEmpty 1
#guard !StorageRing.isFull 5 4 && StorageRing.isFull 5 5

-- wraparound: physical slot = (head + offset) mod capacity, the fixed positive divisor
#guard StorageRing.absIndex 0 0 3 == 0 && StorageRing.absIndex 0 2 3 == 2
#guard StorageRing.absIndex 1 2 3 == 0 && StorageRing.absIndex 2 2 3 == 1
#guard StorageRing.absIndex 3 0 4 == 3 && StorageRing.absIndex 1 3 4 == 0

-- enqueue: admissible strictly below capacity; full and malformed fail closed
#guard StorageRing.canPush 4 0 0 && StorageRing.canPush 4 3 3
#guard !StorageRing.canPush 4 3 4 && !StorageRing.canPush 4 5 0 && !StorageRing.canPush 4 2 5

-- dequeue/peek: admissible on a canonical nonzero live count; empty and malformed fail closed
#guard StorageRing.canPop 4 2 2 && StorageRing.canPop 4 3 4
#guard !StorageRing.canPop 4 0 0 && !StorageRing.canPop 4 4 4 && !StorageRing.canPop 4 4 1
#guard StorageRing.canPeek 4 2 2 && !StorageRing.canPeek 4 0 0

-- runtime-indexed reads: offset < live on canonical metadata; OOB and malformed closed
#guard StorageRing.canGet 4 2 3 0 && StorageRing.canGet 4 2 3 2
#guard !StorageRing.canGet 4 2 3 3 && !StorageRing.canGet 4 2 0 0 && !StorageRing.canGet 4 5 5 0

-- dequeue head advance: ring successor, canonical 0 once the queue empties
#guard StorageRing.poppedHead 0 1 3 == 0
#guard StorageRing.poppedHead 0 2 3 == 1 && StorageRing.poppedHead 2 2 3 == 0
#guard StorageRing.poppedHead 1 4 4 == 2

-- clear resets only canonical storage; malformed metadata is never silently repaired
#guard StorageRing.canClear 4 0 0 && StorageRing.canClear 4 3 3 && StorageRing.canClear 4 0 4
#guard !StorageRing.canClear 4 5 5 && !StorageRing.canClear 4 2 5 && !StorageRing.canClear 4 1 0
#guard StorageRing.clearedHead == 0 && StorageRing.clearedLive == 0

/-! ## Descriptor declaration and fail-closed validation -/

def sampleQueue :=
  StorageRing.declare Layout.root "values" "head" "live" 3

#guard sampleQueue.handle.values.baseSlot == 0
#guard sampleQueue.handle.values.length? == some 3
#guard sampleQueue.handle.values.elementSlots? == some 1
#guard sampleQueue.handle.head.slot? == some 3
#guard sampleQueue.handle.head.width? == some 8
#guard sampleQueue.handle.live.slot? == some 4
#guard sampleQueue.handle.live.width? == some 8
#guard sampleQueue.handle.wellFormed
#guard sampleQueue.next.nextSlot == 5
#guard sampleQueue.next.wellFormed
#guard sampleQueue.next.matchesFlattened
  [("values_0", 8), ("values_1", 8), ("values_2", 8), ("head", 8), ("live", 8)]

-- fail closed at the descriptor level: zero capacity, non-adjacent head, non-adjacent live,
-- wrong payload shape, wrong scalar width
#guard !(StorageRing.declare Layout.root "values" "head" "live" 0).handle.wellFormed

def misalignedHead : StorageRing.Descriptor 2 :=
  let values := Layout.root.array (α := Vector UInt64 2) "values" .u64 2
  let head : Storage.Static.Handle UInt64 :=
    { name := "head", baseSlot := 3, spec := .leaf .u64 }
  let live : Storage.Static.Handle UInt64 :=
    { name := "live", baseSlot := 4, spec := .leaf .u64 }
  { values := values.handle, head, live }

#guard !misalignedHead.wellFormed

def misalignedLive : StorageRing.Descriptor 2 :=
  let values := Layout.root.array (α := Vector UInt64 2) "values" .u64 2
  let head : Storage.Static.Handle UInt64 :=
    { name := "head", baseSlot := 2, spec := .leaf .u64 }
  let live : Storage.Static.Handle UInt64 :=
    { name := "live", baseSlot := 4, spec := .leaf .u64 }
  { values := values.handle, head, live }

#guard !misalignedLive.wellFormed

def wrongPayload : StorageRing.Descriptor 2 :=
  let values := Layout.root.array (α := Vector UInt64 2) "values" .u16 2
  let head : Storage.Static.Handle UInt64 :=
    { name := "head", baseSlot := 2, spec := .leaf .u64 }
  let live : Storage.Static.Handle UInt64 :=
    { name := "live", baseSlot := 3, spec := .leaf .u64 }
  { values := values.handle, head, live }

#guard !wrongPayload.wellFormed

def wrongScalarWidth : StorageRing.Descriptor 2 :=
  let values := Layout.root.array (α := Vector UInt64 2) "values" .u64 2
  let head : Storage.Static.Handle UInt64 :=
    { name := "head", baseSlot := 2, spec := .leaf .u32 }
  let live : Storage.Static.Handle UInt64 :=
    { name := "live", baseSlot := 3, spec := .leaf .u64 }
  { values := values.handle, head, live }

#guard !wrongScalarWidth.wellFormed

/-! ## Consumer descriptor and layout pins -/

#guard Examples.EvmRingMailbox.declared.handle.queue.wellFormed
#guard Examples.EvmRingMailbox.declared.handle.queue.values.baseSlot == 3
#guard Examples.EvmRingMailbox.declared.handle.queue.head.slot? == some 7
#guard Examples.EvmRingMailbox.declared.handle.queue.live.slot? == some 8
#guard Examples.EvmRingMailbox.declared.handle.admin.wideLeaves? == some 3
#guard Examples.EvmRingMailbox.layout.nextSlot == 9
#guard Examples.EvmRingMailbox.layout.wellFormed

#guard Examples.EvmRingHistory.declared.handle.history.wellFormed
#guard Examples.EvmRingHistory.declared.handle.history.values.baseSlot == 0
#guard Examples.EvmRingHistory.declared.handle.history.head.slot? == some 3
#guard Examples.EvmRingHistory.declared.handle.history.live.slot? == some 4
#guard Examples.EvmRingHistory.layout.nextSlot == 5
#guard Examples.EvmRingHistory.layout.wellFormed

def mailboxSlots : List (String × Nat) :=
  [("admin_w0", 8), ("admin_w1", 8), ("admin_w2", 8),
    ("pending_0", 8), ("pending_1", 8), ("pending_2", 8), ("pending_3", 8),
    ("head", 8), ("live", 8)]

def historySlots : List (String × Nat) :=
  [("tape_0", 8), ("tape_1", 8), ("tape_2", 8), ("head", 8), ("live", 8)]

#guard Examples.EvmRingMailbox.layout.matchesFlattened mailboxSlots
#guard Examples.EvmRingHistory.layout.matchesFlattened historySlots

/-! ## Consumer host behavior through ordinary typed state -/

open Examples.EvmRingMailbox in
#guard (init ⟨1, 2, 3⟩).live == 0 && (init ⟨1, 2, 3⟩).head == 0 &&
  frontOf (init ⟨1, 2, 3⟩) == 0 && messageAt (init ⟨1, 2, 3⟩) 0 == 0

-- deliveries land at the ring tail and the front view observes the active ring
open Examples.EvmRingMailbox in
#guard match deliver (init ⟨1, 2, 3⟩) 11 with
  | .ok (s, r) => r == 1 && s.live == 1 && s.head == 0 && s.pending[0]! == 11 &&
      frontOf s == 11 && messageAt s 0 == 11 && messageAt s 1 == 0
  | _ => false

open Examples.EvmRingMailbox in
#guard match deliver (init ⟨1, 2, 3⟩) 11 with
  | .ok (s1, _) =>
      (match deliver s1 22 with
       | .ok (t, r) =>
           r == 2 && t.live == 2 && t.pending[0]! == 11 && t.pending[1]! == 22 &&
             frontOf t == 11 && messageAt t 1 == 22 && messageAt t 2 == 0
       | _ => false)
  | _ => false

-- a full mailbox rejects delivery with the CapExceeded revert value and stores nothing
open Examples.EvmRingMailbox in
#guard match deliver (init ⟨1, 2, 3⟩) 11 with
  | .ok (s1, _) =>
      (match deliver s1 22 with
       | .ok (s2, _) =>
           (match deliver s2 33 with
            | .ok (s3, _) =>
                (match deliver s3 44 with
                 | .ok (s4, r4) =>
                     r4 == 4 && s4.live == 4 && s4.pending[3]! == 44 &&
                       (match deliver s4 55 with
                        | .ok (t, _) => t.live == 4 && t.pending[0]! == 11
                        | _ => false)
                 | _ => false)
            | _ => false)
       | _ => false)
  | _ => false

-- after one take the head advances, and the next delivery wraps back to physical slot 0
open Examples.EvmRingMailbox in
#guard match deliver (init ⟨1, 2, 3⟩) 11 with
  | .ok (s1, _) =>
      (match deliver s1 22 with
       | .ok (s2, _) =>
           (match deliver s2 33 with
            | .ok (s3, _) =>
                (match deliver s3 44 with
                 | .ok (s4, _) =>
                     (match take s4 with
                      | .ok (t, v) =>
                          v == 11 && t.head == 1 && t.live == 3 &&
                            (match deliver t 55 with
                             | .ok (u, r) =>
                                 r == 4 && u.head == 1 && u.live == 4 &&
                                   u.pending[0]! == 55 && u.pending[3]! == 44 &&
                                   frontOf u == 22 && messageAt u 2 == 44 &&
                                   messageAt u 3 == 55
                             | _ => false)
                      | _ => false)
                 | _ => false)
            | _ => false)
       | _ => false)
  | _ => false

-- take returns messages in FIFO order, advances the head around the ring, and canonicalizes
-- the head to 0 when the mailbox empties; the empty take is the typed error
open Examples.EvmRingMailbox in
#guard match deliver (init ⟨1, 2, 3⟩) 11 with
  | .ok (s1, _) =>
      (match deliver s1 22 with
       | .ok (s2, _) =>
           (match take s2 with
            | .ok (t1, v1) =>
                v1 == 11 && t1.head == 1 && t1.live == 1 && frontOf t1 == 22 &&
                  (match take t1 with
                   | .ok (t2, v2) =>
                       v2 == 22 && t2.head == 0 && t2.live == 0 && frontOf t2 == 0 &&
                         (match take t2 with
                          | .error .empty => true
                          | _ => false)
                   | _ => false)
            | _ => false)
       | _ => false)
  | _ => false

-- purge resets only the metadata slots; stale backing slots stay unreachable and are reused
open Examples.EvmRingMailbox in
#guard match deliver (init ⟨1, 2, 3⟩) 11 with
  | .ok (s, _) =>
      (match purge s with
       | .ok (t, r) => r == 0 && t.head == 0 && t.live == 0 && t.pending[0]! == 11 &&
           frontOf t == 0 && messageAt t 0 == 0
       | _ => false)
  | _ => false

open Examples.EvmRingMailbox in
#guard match deliver (init ⟨1, 2, 3⟩) 11 with
  | .ok (s, _) =>
      (match purge s with
       | .ok (t, _) =>
           (match deliver t 99 with
            | .ok (u, r) =>
                r == 1 && u.head == 0 && u.live == 1 && u.pending[0]! == 99 &&
                  frontOf u == 99
            | _ => false)
       | _ => false)
  | _ => false

-- messageAt falls back to 0 outside the live range; corrupted persistent metadata fails every
-- mutation before changing state, including a masked non-canonical empty head
open Examples.EvmRingMailbox in
#guard messageAt ({ init ⟨1, 2, 3⟩ with head := 1, live := 2 }) 2 == 0

open Examples.EvmRingMailbox in
#guard match deliver ({ init ⟨1, 2, 3⟩ with head := 5, live := 1 }) 11 with
  | .error .malformed => true
  | _ => false

open Examples.EvmRingMailbox in
#guard match take ({ init ⟨1, 2, 3⟩ with live := 5 }) with
  | .error .malformed => true
  | _ => false

open Examples.EvmRingMailbox in
#guard match purge ({ init ⟨1, 2, 3⟩ with head := 2, live := 0 }) with
  | .error .malformed => true
  | _ => false

open Examples.EvmRingHistory in
#guard (init 7).live == 1 && (init 7).head == 0 && (init 7).tape[0]! == 7 &&
  currentOf (init 7) == 7 && liveOf (init 7) == 1

-- appends fill the tape; the full tape has its own typed `full` error; appends return the
-- physical slot so wraparound reuse is observable
open Examples.EvmRingHistory in
#guard match append (init 7) 8 with
  | .ok (s1, r1) =>
      r1 == 1 && s1.live == 2 && s1.tape[1]! == 8 &&
        (match append s1 9 with
         | .ok (s2, r2) =>
             r2 == 2 && s2.live == 3 && currentOf s2 == 7 &&
               (match append s2 10 with
                | .error .full => true
                | _ => false)
         | _ => false)
  | _ => false

-- drain in FIFO order, refill across the wrap boundary (tail slot 0), then drain to the
-- canonical empty state
open Examples.EvmRingHistory in
#guard match append (init 7) 8 with
  | .ok (a1, _) =>
      (match append a1 9 with
       | .ok (a2, _) =>
           (match advance a2 with
            | .ok (s1, v1) =>
                v1 == 7 && s1.head == 1 && s1.live == 2 &&
                  (match append s1 10 with
                   | .ok (s2, r2) =>
                       r2 == 0 && s2.live == 3 && s2.head == 1 && s2.tape[0]! == 10 &&
                         s2.tape[1]! == 8 && s2.tape[2]! == 9 &&
                         (match advance s2 with
                          | .ok (s3, v3) =>
                              v3 == 8 && s3.head == 2 && s3.live == 2 &&
                                (match advance s3 with
                                 | .ok (s4, v4) =>
                                     v4 == 9 && s4.head == 0 && s4.live == 1 &&
                                       (match advance s4 with
                                        | .ok (s5, v5) =>
                                            v5 == 10 && s5.head == 0 && s5.live == 0 &&
                                              currentOf s5 == 0 &&
                                                (match advance s5 with
                                                 | .error .empty => true
                                                 | _ => false)
                                        | _ => false)
                                 | _ => false)
                          | _ => false)
                   | _ => false)
            | _ => false)
       | _ => false)
  | _ => false

-- reset clears only the metadata; stale slots stay unreachable and the next append reuses slot 0
open Examples.EvmRingHistory in
#guard match append (init 7) 8 with
  | .ok (s, _) =>
      (match reset s with
       | .ok (t, r) => r == 0 && t.head == 0 && t.live == 0 && t.tape[1]! == 8 &&
           currentOf t == 0 &&
           (match append t 42 with
            | .ok (u, r2) => r2 == 0 && u.live == 1 && u.head == 0 && u.tape[0]! == 42 &&
                currentOf u == 42
            | _ => false)
       | _ => false)
  | _ => false

open Examples.EvmRingHistory in
#guard match append ({ init 7 with head := 3, live := 1 }) 8 with
  | .error .malformed => true
  | _ => false

open Examples.EvmRingHistory in
#guard match advance ({ init 7 with live := 4 }) with
  | .error .malformed => true
  | _ => false

open Examples.EvmRingHistory in
#guard match reset ({ init 7 with head := 2, live := 0 }) with
  | .error .malformed => true
  | _ => false

/-! ## Extraction proof: declared layout == real EVM state flattening, with the existing
fixed-vector dynamic-index load/store emission shapes -/

private def expectQueueLayout (module : Name) (expectedSlots : List (String × Nat))
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

elab "#pf_guard_evm_ring_mailbox" : command =>
  expectQueueLayout `Examples.EvmRingMailbox mailboxSlots [("pending", 3, 4, 1)]
    ["deliver", "take", "purge", "liveOf", "headOf", "frontOf", "messageAt", "adminOf"]
    ["empty", "malformed"]

elab "#pf_guard_evm_ring_history" : command =>
  expectQueueLayout `Examples.EvmRingHistory historySlots [("tape", 0, 3, 1)]
    ["append", "advance", "reset", "liveOf", "headOf", "currentOf"]
    ["full", "empty", "malformed"]

#pf_guard_evm_ring_mailbox
#pf_guard_evm_ring_history

end Tests.EvmStorageRingSpec
