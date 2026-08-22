import Examples.Ping

namespace Tests.PingSpec

open Examples.Ping
open ProofForge.Runtime

#guard (init 0).dummy == 0
#guard get (init 0) == 0
#guard invokeAcc1 == 0

#guard ProofForge.IR.usesCpi ProofForge.Golden.extractedPing
#guard ProofForge.IR.cpiAccountCount ProofForge.Golden.extractedPing == 2

#guard
  match ProofForge.Emit.emitCounterAsm ProofForge.Golden.extractedPing with
  | .error _ => false
  | .ok asm =>
      asm.contains "call sol_invoke_signed_c" &&
        asm.contains "invoke programIx=1" &&
        !asm.contains "invoke programIx=2"

#guard
  match ProofForge.Emit.emitCounterAsm ProofForge.Golden.extractedTransfer with
  | .error _ => false
  | .ok asm =>
      asm.contains "invoke programIx=2" &&
        asm.contains "call sol_invoke_signed_c"

end Tests.PingSpec
