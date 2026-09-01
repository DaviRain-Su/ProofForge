import ProofForge.Attr
import ProofForge.Svm.Runtime

/-!
# SVM SDK sysvar facade

Source-facing names for the currently supported Solana sysvar reads. The facade keeps contracts
on the SDK boundary while the Runtime leaves lower through the target-owned Sysvar query
interpreter. It adds no top-level Op/IR case, scratch allocation, or persistent state.

`Rent.minimumBalance` accepts a `Nat` because the current Runtime contract requires account data
length to be known during extraction. Runtime-selected lengths remain fail closed until a bounded
generic sysvar/safe-arithmetic plan owns them.
-/

namespace ProofForge.Svm.Sdk.Sysvar

namespace Clock

/-- Current physical Solana slot (`Clock.slot`). -/
@[pf_inline] def slot : UInt64 := ProofForge.Svm.Runtime.clockSlot

/-- Current epoch (`Clock.epoch`). -/
@[pf_inline] def epoch : UInt64 := ProofForge.Svm.Runtime.clockEpoch

/-- Native `Clock.epoch_start_timestamp` (`i64` bits at offset 8) carried as `UInt64`. -/
@[pf_inline] def epochStartTimestamp : UInt64 :=
  ProofForge.Svm.Runtime.clockEpochStartTimestamp

/-- Future epoch whose leader schedule was most recently calculated. -/
@[pf_inline] def leaderScheduleEpoch : UInt64 :=
  ProofForge.Svm.Runtime.clockLeaderScheduleEpoch

/-- Native `Clock.unix_timestamp` (`i64` bits at offset 32) carried as `UInt64`. -/
@[pf_inline] def unixTimestamp : UInt64 := ProofForge.Svm.Runtime.unixTime

/-- Two's-complement `Int` view of a native Clock `i64` field. Not extracted; host/on-chain
values stay the raw 64-bit pattern returned by the Runtime leaves above. -/
def asSigned (bits : UInt64) : Int :=
  let n := bits.toNat
  if n < 0x8000000000000000 then
    Int.ofNat n
  else
    -Int.ofNat (0x10000000000000000 - n)

end Clock

namespace EpochSchedule

/-- Current `EpochSchedule.slots_per_epoch`. -/
@[pf_inline] def slotsPerEpoch : UInt64 := ProofForge.Svm.Runtime.slotsPerEpoch

/-- Number of slots before an epoch used to calculate its leader schedule. -/
@[pf_inline] def leaderScheduleSlotOffset : UInt64 :=
  ProofForge.Svm.Runtime.epochScheduleLeaderScheduleSlotOffset

/-- Whether epochs begin short and grow during warmup. -/
@[pf_inline] def warmup : Bool := ProofForge.Svm.Runtime.epochScheduleWarmup != 0

/-- First epoch after the warmup period. -/
@[pf_inline] def firstNormalEpoch : UInt64 :=
  ProofForge.Svm.Runtime.epochScheduleFirstNormalEpoch

/-- First slot after the warmup period. -/
@[pf_inline] def firstNormalSlot : UInt64 :=
  ProofForge.Svm.Runtime.epochScheduleFirstNormalSlot

end EpochSchedule

namespace Rent

/-- Rent-exempt minimum for one compile-time fixed account-data length. -/
@[pf_inline] def minimumBalance (dataLen : Nat) : UInt64 :=
  ProofForge.Svm.Runtime.rentExemption (UInt64.ofNat dataLen)

end Rent

/-!
### sf-014：Sysvar L1 形状

本 facade 仅转发 Runtime 叶；无账户持久状态、无可证 L2 字代数。矩阵标 **n/a-L2**。
下列钉死 API 仍绑定到既有 Runtime 叶（定义等式）。
-/

theorem Clock.slot_def : Clock.slot = ProofForge.Svm.Runtime.clockSlot := rfl
theorem Clock.epoch_def : Clock.epoch = ProofForge.Svm.Runtime.clockEpoch := rfl
theorem Rent.minimumBalance_def (dataLen : Nat) :
    Rent.minimumBalance dataLen =
      ProofForge.Svm.Runtime.rentExemption (UInt64.ofNat dataLen) := rfl

end ProofForge.Svm.Sdk.Sysvar
