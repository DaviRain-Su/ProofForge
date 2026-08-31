import ProofForge

/-!
Permissionless UInt256 consumer of the shared `Core.SafeCast` policy. A representable amount is
accumulated only when the subsequent UInt64 addition is also checked-valid. Wide-input failure
and sum overflow are distinct typed errors, and both occur before the literal `total` state update.
-/

namespace Examples.EvmSafeCastAccumulator

open ProofForge.Core
open ProofForge.Evm.Sdk

structure State where
  total : UInt64
  deriving Repr, DecidableEq, Inhabited

inductive Error where
  | amountTooWide
  | sumOverflow
  deriving Repr, DecidableEq, Inhabited, BEq

def u64Max : UInt64 := ~~~(0 : UInt64)

@[pf_entry]
def init (seed : UInt64) : State :=
  { total := seed }

@[pf_entry]
def totalOf (s : State) : UInt64 :=
  s.total

/-- Checked UInt256→UInt64 accumulation. No state is returned on either failure branch. -/
@[pf_entry]
def add (s : State) (amount : UInt256) : Except Error (State × UInt64) := do
  let delta ← SafeCast.UInt256.toUInt64 amount .amountTooWide
  if s.total ≤ u64Max - delta then
    let next := s.total + delta
    .ok ({ total := next }, next)
  else
    .error .sumOverflow

end Examples.EvmSafeCastAccumulator
