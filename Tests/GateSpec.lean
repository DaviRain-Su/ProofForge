import Examples.Gate

namespace Tests.GateSpec

open Examples.Gate
open ProofForge.Svm.Runtime

#guard (init 0).open_ == false
#guard isOpen (init 0) == 0
#guard now (init 0) == unixTime
#guard unixTime == 0

#guard
  match ProofForge.Svm.ABI.fieldOffset ProofForge.Golden.extractedGate "open_" with
  | some 8 => true
  | _ => false

#guard
  match ProofForge.Svm.Emit.emitCounterAsm ProofForge.Golden.extractedGate with
  | .error _ => false
  | .ok asm =>
      asm.contains "call sol_get_clock_sysvar" &&
        asm.contains "clock.unix" &&
        asm.contains "call now" &&
        asm.contains "call isOpen" &&
        asm.contains "call openGate"

end Tests.GateSpec
