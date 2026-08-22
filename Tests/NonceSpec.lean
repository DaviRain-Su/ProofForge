import Examples.Nonce

namespace Tests.NonceSpec

open Examples.Nonce
open ProofForge.Runtime

#guard (init 0).dummy == 0
#guard get (init 0) == 0

#guard ProofForge.IR.usesCpi ProofForge.Golden.extractedNonce
#guard ProofForge.IR.cpiAccountCount ProofForge.Golden.extractedNonce == 4

#guard
  match ProofForge.Svm.Emit.emitCounterAsm ProofForge.Golden.extractedNonce with
  | .error _ => false
  | .ok asm =>
      asm.contains "call sol_invoke_signed_c" &&
        asm.contains "ja advance" &&
        asm.contains "jlt r1, 4"

end Tests.NonceSpec
