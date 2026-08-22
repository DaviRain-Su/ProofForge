import Examples.Epoch

namespace Tests.EpochSpec

open Examples.Epoch
open ProofForge.Runtime

#guard (init 0).dummy == 0
#guard get (init 0) == 0
#guard span (init 0) == slotsPerEpoch

#guard
  match stamp (init 0) with
  | .ok (st, ret) => st.dummy == slotsPerEpoch && ret == slotsPerEpoch
  | .error _ => false

#guard
  match ProofForge.Emit.emitCounterAsm ProofForge.Golden.extractedEpoch with
  | .error _ => false
  | .ok asm =>
      asm.contains "call sol_get_epoch_schedule_sysvar" &&
        asm.contains "load slotsPerEpoch" &&
        asm.contains "call span" &&
        asm.contains "call stamp"

end Tests.EpochSpec
