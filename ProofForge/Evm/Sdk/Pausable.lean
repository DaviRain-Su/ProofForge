import ProofForge.Evm.Sdk.Base

namespace ProofForge.Evm.Sdk.Pausable

/-!
# EVM SDK pausable policy

Reusable O(1) policy over one explicit `UInt8` state field. `running` is `0`, `paused` is `1`,
and every transition returns the replacement flag for the application to store visibly. The
component does not own authorization, emit an event, hide a storage write, allocate a slot, or add
a Runtime/Ops/IR/Component/Emit case.

Applications compose `isRunning` with their own owner/role policy, return `violation` on a blocked
operation, and explicitly write `pause current` / `unpause current` into their typed State field.
Values other than the two canonical flags fail closed as not running and not paused.

Typed Paused/Unpaused events remain a later generic-event slice; reentrancy remains separate
because it requires a storage write that is ordered before an external call and a matching clear
after it. This module does not claim either behavior.
-/

/-- Canonical state in which guarded operations may run. -/
@[pf_inline] def running : UInt8 := 0

/-- Canonical state in which guarded operations are blocked. -/
@[pf_inline] def paused : UInt8 := 1

/-- True only for the canonical running flag. -/
@[pf_inline] def isRunning (flag : UInt8) : Bool :=
  flag == running

/-- True only for the canonical paused flag. -/
@[pf_inline] def isPaused (flag : UInt8) : Bool :=
  flag == paused

/-- Replacement flag for an application-owned pause transition. -/
@[pf_inline] def pause (_current : UInt8) : UInt8 :=
  paused

/-- Replacement flag for an application-owned unpause transition. -/
@[pf_inline] def unpause (_current : UInt8) : UInt8 :=
  running

/-- Closed failure terminal for a pause gate. -/
@[pf_inline] def violation : UInt64 :=
  Revert.paused

end ProofForge.Evm.Sdk.Pausable
