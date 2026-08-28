import ProofForge.Evm.Sdk.Storage

namespace ProofForge.Evm.Sdk.Reentrancy

/-!
# EVM SDK reentrancy policy

Reusable fail-closed lock policy over one explicit static `UInt64` field. The values match
OpenZeppelin's established nonzero sentinel convention: `notEntered = 1`, `entered = 2`.

`enter` and `leave` are deliberately separate ordered storage effects. Applications place their
external call lexically between them, while the EVM transaction owns rollback if that call fails.
The SDK does not hide control flow in a higher-order wrapper, infer which calls are external,
allocate a slot, or add a Reentrancy-specific Runtime/Ops/IR/Component/Emit case. Every value other
than `notEntered` fails closed at `canEnter`; the application owns its typed error terminal.
-/

/-- Canonical initialized state in which a guarded entry may run. -/
@[pf_inline] def notEntered : UInt64 := 1

/-- State made visible before the guarded external call. -/
@[pf_inline] def entered : UInt64 := 2

/-- Fail-closed entry predicate. Uninitialized and malformed values are rejected. -/
@[pf_inline] def canEnter (status : UInt64) : Bool :=
  status == notEntered

@[pf_inline] def isEntered (status : UInt64) : Bool :=
  status == entered

/-- Immediately publish the entered sentinel through a schema-resolved static handle. -/
@[pf_inline] def enter (guard : Storage.Static.Handle UInt64) : UInt64 :=
  guard.storeNow entered

/-- Immediately restore the not-entered sentinel after the external call succeeds. -/
@[pf_inline] def leave (guard : Storage.Static.Handle UInt64) : UInt64 :=
  guard.storeNow notEntered

end ProofForge.Evm.Sdk.Reentrancy
