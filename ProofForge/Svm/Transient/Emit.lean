import ProofForge.Svm.Heap.Emit
import ProofForge.Svm.Sdk.Transient

/-!
# Shared invocation-local container lifecycle emission

Heap-backed transient containers all use the same checked lifecycle: reserve one fixed payload per
handle slot, record pointer/length/capacity plus an active marker in that slot's invocation-scratch
bank, validate the marker before every operation, clear logical length without reallocating, and
invalidate the handle without pretending that Solana's bump allocator can reclaim memory.

Each container kind owns two compile-time handle slots; the concrete emitters select the bank and
allocation from the source handle's slot, so same-kind handles share only this interpreter and the
bump position, never metadata or payload. Concrete vector/byte components own their element
operations and error vocabulary. This module owns only the reusable allocator/metadata protocol,
so adding another bounded container slot or kind does not copy heap or handle-lifetime assembly
into another emitter.
-/

namespace ProofForge.Svm.Transient.Emit

open ProofForge.Svm.Sdk.Transient

/-- Deep-scratch stride between two same-kind handle slots: four 8-byte metadata cells. -/
def slotStride : Nat := 32

/-- Metadata cell for handle slot `k`: `base` names slot 0, slot `k` owns `base + k * slotStride`.
Each slot's bank is disjoint from every other component's deep scratch. -/
def slotCell (base slot : Nat) : Nat := base + slot * slotStride

/-- Target-owned metadata cells and terminal errors for one transient container kind. -/
structure Lifecycle where
  kind : String
  pointerStack : Nat
  lengthStack : Nat
  capacityStack : Nat
  activeStack : Nat
  activeMagic : Nat
  oomErrorCode : Nat
  stateErrorCode : Nat
  deriving BEq, Repr, Inhabited

def failure (code : Nat) : String :=
  s!"  lddw r0, 0x{Core.IR.u64Hex (UInt64.ofNat code)}\n  exit\n"

/-- Reject inactive and capacity-mismatched source handles before a concrete operation can touch
the payload pointer. `slot` selects the metadata bank of the source handle. -/
def emitRequireActive (lifecycle : Lifecycle) (slot capacity : Nat) (label : String) : String :=
  let active := s!"{lifecycle.kind}_active_{label}"
  let matchingCapacity := s!"{lifecycle.kind}_capacity_{label}"
  s!"\
  ldxdw r1, [r10 - {slotCell lifecycle.activeStack slot}]
  lddw r2, {lifecycle.activeMagic}
  jeq r1, r2, {active}
{failure lifecycle.stateErrorCode}{active}:
  ldxdw r1, [r10 - {slotCell lifecycle.capacityStack slot}]
  lddw r2, {capacity}
  jeq r1, r2, {matchingCapacity}
{failure lifecycle.stateErrorCode}{matchingCapacity}:
"

/-- Allocate the fixed payload through the shared official-shaped heap emitter and open the slot's
invocation-local handle. -/
def emitBegin (lifecycle : Lifecycle) (vector : FixedVec) (slot : Nat)
    (label : String) : Except String String := do
  unless vector.wellFormed do
    throw s!"assemble/svm: malformed {lifecycle.kind} fixed-vector descriptor"
  let allocate ← Heap.Emit.emitAllocate lifecycle.kind label
    vector.buffer.capacityBytes vector.buffer.alignment
    (slotCell lifecycle.pointerStack slot)
    (failure lifecycle.oomErrorCode)
  return allocate ++ s!"\
  lddw r1, 0
  stxdw [r10 - {slotCell lifecycle.lengthStack slot}], r1
  lddw r1, {vector.capacity}
  stxdw [r10 - {slotCell lifecycle.capacityStack slot}], r1
  lddw r1, {lifecycle.activeMagic}
  stxdw [r10 - {slotCell lifecycle.activeStack slot}], r1
"

/-- Match Rust `Vec::truncate`: shorten the live prefix when requested, otherwise do nothing.
The requested length is already materialized in target scratch by the concrete component. -/
def emitTruncate (lifecycle : Lifecycle) (capacity newLengthStack slot : Nat)
    (label : String) : String :=
  let done := s!"{lifecycle.kind}_truncate_done_{label}"
  emitRequireActive lifecycle slot capacity label ++ s!"\
  ldxdw r2, [r10 - {newLengthStack}]
  ldxdw r3, [r10 - {slotCell lifecycle.lengthStack slot}]
  jge r2, r3, {done}
  stxdw [r10 - {slotCell lifecycle.lengthStack slot}], r2
{done}:
"

/-- Reset logical length while retaining the same bump allocation and active handle. -/
def emitClear (lifecycle : Lifecycle) (capacity slot : Nat) (label : String) : String :=
  emitRequireActive lifecycle slot capacity label ++ s!"\
  lddw r1, 0
  stxdw [r10 - {slotCell lifecycle.lengthStack slot}], r1
"

/-- Invalidate source-visible metadata. The underlying downward bump allocation is intentionally
not reclaimed. -/
def emitFinish (lifecycle : Lifecycle) (capacity slot : Nat) (label : String) : String :=
  emitRequireActive lifecycle slot capacity label ++ s!"\
  lddw r1, 0
  stxdw [r10 - {slotCell lifecycle.pointerStack slot}], r1
  stxdw [r10 - {slotCell lifecycle.lengthStack slot}], r1
  stxdw [r10 - {slotCell lifecycle.capacityStack slot}], r1
  stxdw [r10 - {slotCell lifecycle.activeStack slot}], r1
"

end ProofForge.Svm.Transient.Emit
