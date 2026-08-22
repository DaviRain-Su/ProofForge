import Examples.Clock

namespace Tests.ClockSpec

open Examples.Clock
open SolanaLean.Runtime

#guard (init 0).stamped == 0
#guard get (init 0) == 0
#guard height (init 0) == clockSlot
#guard key0 (init 0) == signerKey0

#guard
  match SolanaLean.IR.fieldOffset SolanaLean.Golden.extractedClock "stamped" with
  | some 8 => true
  | _ => false

#guard SolanaLean.IR.dataLen SolanaLean.Golden.extractedClock == 16

#guard
  match SolanaLean.Emit.emitCounterAsm SolanaLean.Golden.extractedClock with
  | .error _ => false
  | .ok asm =>
      asm.contains "call sol_get_clock_sysvar" &&
        asm.contains "ACC0_KEY + 0" &&
        asm.contains "call height" &&
        asm.contains "call key0" &&
        asm.contains "call stamp"

end Tests.ClockSpec
