import Examples.TokenOwner

namespace Tests.TokenOwnerSpec

open Examples.TokenOwner
open ProofForge.Runtime

#guard (init 0).dummy == 0
#guard get (init 0) == 0

#guard ProofForge.IR.usesCpi ProofForge.Golden.extractedTokenOwner

#guard
  match ProofForge.Emit.emitCounterAsm ProofForge.Golden.extractedTokenOwner with
  | .error _ => false
  | .ok asm =>
      asm.contains "call sol_invoke_signed_c" &&
        asm.contains "ja setOwner" &&
        asm.contains "ja approve"

end Tests.TokenOwnerSpec
