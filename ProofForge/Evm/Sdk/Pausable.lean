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


section Proofs

/-! ## fail-closed 语义的 kernel 证明

全部是纯 UInt8 谓词性质；抽取器已支持 UInt8 scalar helper（r5-004），
这些性质是链上相关性质。核心合同：**unknown flag fail closed**——
非 canonical 的 flag 既不放行也不误报 paused 终端，且 unpause 总能恢复。 -/

/-- 放行当且仅当 flag 是 canonical running。 -/
theorem isRunning_iff (flag : UInt8) : isRunning flag = true ↔ flag = running := by
  simp [isRunning, running]

/-- paused 当且仅当 flag 是 canonical paused。 -/
theorem isPaused_iff (flag : UInt8) : isPaused flag = true ↔ flag = paused := by
  simp [isPaused, paused]

/-- **互斥**：running 门开着时不会同时报 paused。 -/
theorem not_isPaused_of_isRunning {flag : UInt8} (h : isRunning flag = true) :
    isPaused flag = false := by
  rw [isRunning_iff] at h
  subst h
  simp [isPaused, paused, running]

theorem not_isRunning_of_isPaused {flag : UInt8} (h : isPaused flag = true) :
    isRunning flag = false := by
  rw [isPaused_iff] at h
  subst h
  simp [isRunning, paused, running]

/-- **unknown flag fail-closed**：非 canonical 的 flag 门保持关闭，
且不会误报 paused 终端（应用不会把未知态误判成「被暂停」）。 -/
theorem unknown_neither {flag : UInt8} (h1 : flag ≠ running) (h2 : flag ≠ paused) :
    isRunning flag = false ∧ isPaused flag = false := by
  show (flag == running) = false ∧ (flag == paused) = false
  constructor
  · cases hbeq : (flag == running) with
    | false => rfl
    | true => rw [beq_iff_eq] at hbeq; exact absurd hbeq h1
  · cases hbeq : (flag == paused) with
    | false => rfl
    | true => rw [beq_iff_eq] at hbeq; exact absurd hbeq h2

/-- pause 转换是常值替换：**任何**当前态（含 unknown）都落到 canonical paused。 -/
theorem pause_const (flag : UInt8) : pause flag = paused := by
  simp [pause, paused]

/-- unpause 转换是常值替换：任何当前态都恢复到 canonical running。 -/
theorem unpause_const (flag : UInt8) : unpause flag = running := by
  simp [unpause, running]

/-- **从 unknown 态也能可靠暂停**：pause 后必为 paused。 -/
theorem isPaused_pause (flag : UInt8) : isPaused (pause flag) = true := by
  simp [isPaused, pause, paused]

/-- **unpause 总能恢复运行态**：即使当前是 unknown flag。 -/
theorem isRunning_unpause (flag : UInt8) : isRunning (unpause flag) = true := by
  unfold isRunning unpause running
  rfl


/-- 恢复后不会处于 paused。 -/
theorem not_isPaused_unpause (flag : UInt8) : isPaused (unpause flag) = false := by
  rw [unpause_const]
  simp [isPaused, running, paused]

/-- 暂停→恢复→再暂停：转换序列收敛到 canonical 态（无状态漂移）。 -/
theorem pause_unpause_roundtrip (flag : UInt8) :
    unpause (pause flag) = running ∧ pause (unpause flag) = paused := ⟨rfl, rfl⟩

end Proofs

end ProofForge.Evm.Sdk.Pausable
