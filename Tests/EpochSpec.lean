import Examples.Epoch

namespace Tests.EpochSpec

open Examples.Epoch
open ProofForge.Svm.Sdk

#guard (init 0).dummy == 0
#guard get (init 0) == 0
#guard span (init 0) == Sysvar.EpochSchedule.slotsPerEpoch
#guard leaderOffset (init 0) == Sysvar.EpochSchedule.leaderScheduleSlotOffset
#guard isWarmup (init 0) == Sysvar.EpochSchedule.warmup
#guard normalEpoch (init 0) == Sysvar.EpochSchedule.firstNormalEpoch
#guard normalSlot (init 0) == Sysvar.EpochSchedule.firstNormalSlot

#guard
  match stamp (init 0) with
  | .ok (st, ret) =>
      st.dummy == Sysvar.EpochSchedule.slotsPerEpoch &&
        ret == Sysvar.EpochSchedule.slotsPerEpoch
  | .error _ => false

#guard
  match ProofForge.Svm.Emit.emitCounterAsm ProofForge.Golden.extractedEpoch with
  | .error _ => false
  | .ok asm =>
      asm.contains "call sol_get_epoch_schedule_sysvar" &&
        asm.contains "load slotsPerEpoch" &&
        asm.contains "call span" &&
        asm.contains "call stamp"

end Tests.EpochSpec
