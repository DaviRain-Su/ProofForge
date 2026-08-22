import Examples.TokenMs

namespace Tests.TokenMsSpec

open Examples.TokenMs
open ProofForge.Runtime

#guard (init 0).dummy == 0
#guard get (init 0) == 0

#guard ProofForge.IR.usesCpi ProofForge.Golden.extractedTokenMs
#guard ProofForge.IR.cpiAccountCount ProofForge.Golden.extractedTokenMs == 5

#guard
  match ProofForge.Emit.emitCounterAsm ProofForge.Golden.extractedTokenMs with
  | .error _ => false
  | .ok asm =>
      asm.contains "call sol_invoke_signed_c" &&
        asm.contains "ja openMs" &&
        asm.contains "jlt r1, 5"

end Tests.TokenMsSpec
