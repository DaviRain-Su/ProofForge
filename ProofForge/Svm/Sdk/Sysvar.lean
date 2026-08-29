import ProofForge.Attr
import ProofForge.Svm.Runtime

/-!
# SVM SDK sysvar facade

Source-facing names for the currently supported Solana sysvar reads. The facade keeps contracts
on the SDK boundary while erasing directly to the existing target-owned Runtime leaves: it adds no
syscall, Op, IR node, component case, scratch allocation, or persistent state.

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

/-- Current `Clock.unix_timestamp`, exposed as the existing unsigned 64-bit bit pattern. -/
@[pf_inline] def unixTimestamp : UInt64 := ProofForge.Svm.Runtime.unixTime

end Clock

namespace EpochSchedule

/-- Current `EpochSchedule.slots_per_epoch`. -/
@[pf_inline] def slotsPerEpoch : UInt64 := ProofForge.Svm.Runtime.slotsPerEpoch

end EpochSchedule

namespace Rent

/-- Rent-exempt minimum for one compile-time fixed account-data length. -/
@[pf_inline] def minimumBalance (dataLen : Nat) : UInt64 :=
  ProofForge.Svm.Runtime.rentExemption (UInt64.ofNat dataLen)

end Rent

end ProofForge.Svm.Sdk.Sysvar
