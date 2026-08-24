import Examples.Call

namespace Tests.CallSpec

open Examples.Call
open ProofForge.Svm.Runtime

#guard (init 0).dummy == 0
#guard get (init 0) == 0
#guard invoke 1 #[] #[] == 0

#guard ProofForge.Svm.ABI.usesCpi ProofForge.Golden.extractedCall
#guard ProofForge.Svm.ABI.cpiAccountCount ProofForge.Golden.extractedCall == 3

#guard
  match ProofForge.Svm.Emit.emitCounterAsm ProofForge.Golden.extractedCall with
  | .error _ => false
  | .ok asm =>
      asm.contains "invoke programIx=2" &&
        asm.contains "call sol_invoke_signed_c"

end Tests.CallSpec
