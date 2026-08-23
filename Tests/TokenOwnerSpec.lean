import Examples.TokenOwner

namespace Tests.TokenOwnerSpec

open Examples.TokenOwner
open ProofForge.Svm.Runtime

#guard (init 0).dummy == 0
#guard get (init 0) == 0

#guard ProofForge.Svm.ABI.usesCpi ProofForge.Golden.extractedTokenOwner

#guard
  match ProofForge.Svm.Emit.emitCounterAsm ProofForge.Golden.extractedTokenOwner with
  | .error _ => false
  | .ok asm =>
      asm.contains "call sol_invoke_signed_c" &&
        asm.contains "ja setOwner" &&
        asm.contains "ja approve"

end Tests.TokenOwnerSpec
