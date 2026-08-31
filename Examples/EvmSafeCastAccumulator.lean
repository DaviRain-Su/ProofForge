import ProofForge

/-!
Permissionless UInt256 consumer of the shared `Core.SafeCast` policy. A representable amount is
accumulated only when the subsequent UInt64 addition is also checked-valid. A separate checkpoint
path narrows to UInt32, while a batch path independently narrows to UInt16. Both apply explicit
nonzero policy, and every failure occurs before its literal state update.
-/

namespace Examples.EvmSafeCastAccumulator

open ProofForge.Core
open ProofForge.Evm.Sdk

structure State where
  total : UInt64
  checkpoint : UInt32
  batch : UInt16
  deriving Repr, DecidableEq, Inhabited

inductive Error where
  | amountTooWide
  | sumOverflow
  | checkpointTooWide
  | checkpointZero
  | batchTooWide
  | batchZero
  deriving Repr, DecidableEq, Inhabited, BEq

def u64Max : UInt64 := ~~~(0 : UInt64)

@[pf_entry]
def init (seed : UInt64) : State :=
  { total := seed, checkpoint := 1, batch := 2 }

@[pf_entry]
def totalOf (s : State) : UInt64 :=
  s.total

@[pf_entry]
def checkpointOf (s : State) : UInt32 :=
  s.checkpoint

@[pf_entry]
def batchOf (s : State) : UInt16 :=
  s.batch

/-- Checked UInt256→UInt64 accumulation. No state is returned on either failure branch. -/
@[pf_entry]
def add (s : State) (amount : UInt256) : Except Error (State × UInt64) := do
  let delta ← SafeCast.UInt256.toUInt64 amount .amountTooWide
  if s.total ≤ u64Max - delta then
    let next := s.total + delta
    .ok ({ s with total := next }, next)
  else
    .error .sumOverflow

/-- Checked UInt256→UInt32 replacement with application-owned nonzero policy. -/
@[pf_entry]
def setCheckpoint (s : State) (value : UInt256) : Except Error (State × UInt32) := do
  let checkpoint ← SafeCast.UInt256.toUInt32 value .checkpointTooWide
  if checkpoint == 0 then
    .error .checkpointZero
  else
    .ok ({ s with checkpoint }, checkpoint)

/-- Checked UInt256→UInt16 replacement with a separate application-owned nonzero policy. -/
@[pf_entry]
def setBatch (s : State) (value : UInt256) : Except Error (State × UInt16) := do
  let batch ← SafeCast.UInt256.toUInt16 value .batchTooWide
  if batch == 0 then
    .error .batchZero
  else
    .ok ({ s with batch }, batch)

end Examples.EvmSafeCastAccumulator
