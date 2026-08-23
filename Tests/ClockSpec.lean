import Examples.Clock

namespace Tests.ClockSpec

open Examples.Clock
open ProofForge.Svm.Runtime

#guard (init 0).stamped == 0
#guard get (init 0) == 0
#guard height (init 0) == clockSlot
#guard era (init 0) == clockEpoch
#guard key0 (init 0) == signerKey0

#guard
  match ProofForge.IR.fieldOffset ProofForge.Golden.extractedClock "stamped" with
  | some 8 => true
  | _ => false

#guard ProofForge.IR.dataLen ProofForge.Golden.extractedClock == 16

#guard
  match ProofForge.Svm.Emit.emitCounterAsm ProofForge.Golden.extractedClock with
  | .error _ => false
  | .ok asm =>
      asm.contains "call sol_get_clock_sysvar" &&
        asm.contains "ACC0_KEY + 0" &&
        asm.contains "call height" &&
        asm.contains "call era" &&
        asm.contains "call key0" &&
        asm.contains "call stamp"

end Tests.ClockSpec
