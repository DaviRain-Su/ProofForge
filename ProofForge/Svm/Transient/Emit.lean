import ProofForge.Svm.Heap.Emit
import ProofForge.Svm.Sdk.Transient

/-!
# Shared invocation-local container lifecycle emission

Heap-backed transient containers all use the same checked lifecycle: reserve one fixed payload,
record pointer/length/capacity plus an active marker in invocation scratch, validate that marker
before every operation, clear logical length without reallocating, and invalidate the handle
without pretending that Solana's bump allocator can reclaim memory.

Concrete vector/byte components own their element operations and error vocabulary. This module
owns only the reusable allocator/metadata protocol, so adding another bounded container does not
copy heap or handle-lifetime assembly into another emitter.
-/

namespace ProofForge.Svm.Transient.Emit

open ProofForge.Svm.Sdk.Transient

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
the payload pointer. -/
def emitRequireActive (lifecycle : Lifecycle) (capacity : Nat) (label : String) : String :=
  let active := s!"{lifecycle.kind}_active_{label}"
  let matchingCapacity := s!"{lifecycle.kind}_capacity_{label}"
  s!"\
  ldxdw r1, [r10 - {lifecycle.activeStack}]
  lddw r2, {lifecycle.activeMagic}
  jeq r1, r2, {active}
{failure lifecycle.stateErrorCode}{active}:
  ldxdw r1, [r10 - {lifecycle.capacityStack}]
  lddw r2, {capacity}
  jeq r1, r2, {matchingCapacity}
{failure lifecycle.stateErrorCode}{matchingCapacity}:
"

/-- Allocate the fixed payload through the shared official-shaped heap emitter and open its
invocation-local handle. -/
def emitBegin (lifecycle : Lifecycle) (vector : FixedVec) (label : String) : Except String String := do
  unless vector.wellFormed do
    throw s!"assemble/svm: malformed {lifecycle.kind} fixed-vector descriptor"
  let allocate ← Heap.Emit.emitAllocate lifecycle.kind label
    vector.buffer.capacityBytes vector.buffer.alignment lifecycle.pointerStack
    (failure lifecycle.oomErrorCode)
  return allocate ++ s!"\
  lddw r1, 0
  stxdw [r10 - {lifecycle.lengthStack}], r1
  lddw r1, {vector.capacity}
  stxdw [r10 - {lifecycle.capacityStack}], r1
  lddw r1, {lifecycle.activeMagic}
  stxdw [r10 - {lifecycle.activeStack}], r1
"

/-- Reset logical length while retaining the same bump allocation and active handle. -/
def emitClear (lifecycle : Lifecycle) (capacity : Nat) (label : String) : String :=
  emitRequireActive lifecycle capacity label ++ s!"\
  lddw r1, 0
  stxdw [r10 - {lifecycle.lengthStack}], r1
"

/-- Invalidate source-visible metadata. The underlying downward bump allocation is intentionally
not reclaimed. -/
def emitFinish (lifecycle : Lifecycle) (capacity : Nat) (label : String) : String :=
  emitRequireActive lifecycle capacity label ++ s!"\
  lddw r1, 0
  stxdw [r10 - {lifecycle.pointerStack}], r1
  stxdw [r10 - {lifecycle.lengthStack}], r1
  stxdw [r10 - {lifecycle.capacityStack}], r1
  stxdw [r10 - {lifecycle.activeStack}], r1
"

end ProofForge.Svm.Transient.Emit
