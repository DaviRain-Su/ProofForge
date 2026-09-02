import Examples.Svm.TokenSize

namespace Tests.TokenSizeSpec

open Examples.Svm.TokenSize
open ProofForge.Svm.Runtime

#guard (init 0).dummy == 0
#guard get (init 0) == 0
#guard tokenAccountSize == 0
#guard cpiReturn == 0

#guard
  match size (init 0) with
  | .ok (st, ret) => st.dummy == 0 && ret == 0
  | .error _ => false

#guard ProofForge.Svm.ABI.usesCpi ProofForge.Golden.extractedTokenSize
#guard ProofForge.Svm.ABI.cpiAccountCount ProofForge.Golden.extractedTokenSize == 4

#guard
  match ProofForge.Svm.Emit.emitCounterAsm ProofForge.Golden.extractedTokenSize with
  | .error _ => false
  | .ok asm =>
      asm.contains "invoke programIx=3" &&
        asm.contains "dataLen=1" &&
        asm.contains "call sol_invoke_signed_c" &&
        asm.contains "call sol_get_return_data" &&
        asm.contains "jlt r1, 4" &&
        asm.contains "call size"

end Tests.TokenSizeSpec
