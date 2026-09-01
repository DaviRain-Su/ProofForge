import Examples.Clock

namespace Tests.ClockSpec

open Examples.Clock
open ProofForge.Svm.Sdk

#guard (init 0).stamped == 0
#guard get (init 0) == 0
#guard height (init 0) == Sysvar.Clock.slot
#guard era (init 0) == Sysvar.Clock.epoch
#guard leaderEra (init 0) == Sysvar.Clock.leaderScheduleEpoch
#guard epochStart (init 0) == Sysvar.Clock.epochStartTimestamp
#guard unix (init 0) == Sysvar.Clock.unixTimestamp
#guard key0 (init 0) == ProofForge.Svm.Runtime.signerKey0

#guard
  match ProofForge.Svm.ABI.fieldOffset ProofForge.Golden.extractedClock "stamped" with
  | some 8 => true
  | _ => false

#guard ProofForge.Svm.ABI.dataLen ProofForge.Golden.extractedClock == 16

#guard
  match ProofForge.Svm.Emit.emitCounterAsm ProofForge.Golden.extractedClock with
  | .error _ => false
  | .ok asm =>
      asm.contains "call sol_get_clock_sysvar" &&
        asm.contains "ACC0_KEY + 0" &&
        asm.contains "add64 r1, -3072" &&
        !asm.contains "add64 r1, -72\n  call sol_get_clock_sysvar" &&
        asm.contains "call height" &&
        asm.contains "call era" &&
        asm.contains "call key0" &&
        asm.contains "call stamp"

end Tests.ClockSpec
