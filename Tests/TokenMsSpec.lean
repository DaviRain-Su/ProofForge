import Examples.TokenMs

namespace Tests.TokenMsSpec

open Examples.TokenMs
open ProofForge.Svm.Runtime

#guard (init 0).dummy == 0
#guard get (init 0) == 0

#guard ProofForge.Svm.ABI.usesCpi ProofForge.Golden.extractedTokenMs
#guard ProofForge.Svm.ABI.cpiAccountCount ProofForge.Golden.extractedTokenMs == 5

#guard
  match ProofForge.Svm.Emit.emitCounterAsm ProofForge.Golden.extractedTokenMs with
  | .error _ => false
  | .ok asm =>
      asm.contains "call sol_invoke_signed_c" &&
        asm.contains "ja openMs" &&
        asm.contains "jlt r1, 5"

end Tests.TokenMsSpec
