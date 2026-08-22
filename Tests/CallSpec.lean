import Examples.Call

namespace Tests.CallSpec

open Examples.Call
open ProofForge.Runtime

#guard (init 0).dummy == 0
#guard get (init 0) == 0
#guard invoke 1 #[] #[] == 0

#guard ProofForge.IR.usesCpi ProofForge.Golden.extractedCall
#guard ProofForge.IR.cpiAccountCount ProofForge.Golden.extractedCall == 2

#guard
  match ProofForge.Emit.emitCounterAsm ProofForge.Golden.extractedCall with
  | .error _ => false
  | .ok asm =>
      asm.contains "invoke programIx=1" &&
        asm.contains "call sol_invoke_signed_c"

end Tests.CallSpec
