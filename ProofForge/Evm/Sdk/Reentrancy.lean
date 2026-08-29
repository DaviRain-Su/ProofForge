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


section Proofs

/-- **未知状态 fail-closed**：非 notEntered 非 entered 的值两个谓词都拒绝。 -/
theorem unknown_neither {status : UInt64} (h1 : status ≠ notEntered) (h2 : status ≠ entered) :
    canEnter status = false ∧ isEntered status = false := by
  constructor
  · unfold canEnter
    cases hbeq : status == notEntered with
    | false => rfl
    | true => rw [beq_iff_eq] at hbeq; exact absurd hbeq h1
  · unfold isEntered
    cases hbeq : status == entered with
    | false => rfl
    | true => rw [beq_iff_eq] at hbeq; exact absurd hbeq h2

/-- canEnter 与 isEntered 互斥。 -/
theorem not_isEntered_of_canEnter {status : UInt64} (h : canEnter status = true) :
    isEntered status = false := by
  unfold canEnter at h
  rw [beq_iff_eq] at h
  subst h
  unfold isEntered notEntered entered
  decide

theorem not_canEnter_of_isEntered {status : UInt64} (h : isEntered status = true) :
    canEnter status = false := by
  unfold isEntered at h
  rw [beq_iff_eq] at h
  subst h
  unfold canEnter notEntered entered
  decide

end Proofs

end ProofForge.Evm.Sdk.Reentrancy
