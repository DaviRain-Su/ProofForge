import Examples.TokenXfer

namespace Tests.TokenXferSpec

open Examples.TokenXfer
open ProofForge.Svm.Runtime

#guard (init 0).dummy == 0
#guard get (init 0) == 0
#guard tokenTransferChecked 7 6 == 0

#guard
  match send (init 0) 9 with
  | .ok (st, ret) => st.dummy == 0 && ret == 9
  | .error _ => false

#guard ProofForge.Svm.ABI.usesCpi ProofForge.Golden.extractedTokenXfer
#guard ProofForge.Svm.ABI.cpiAccountCount ProofForge.Golden.extractedTokenXfer == 6

#guard
  match ProofForge.Svm.Emit.emitCounterAsm ProofForge.Golden.extractedTokenXfer with
  | .error _ => false
  | .ok asm =>
      asm.contains "invoke programIx=5" &&
        asm.contains "dataLen=10" &&
        asm.contains "call sol_invoke_signed_c" &&
        asm.contains "jlt r1, 6"

end Tests.TokenXferSpec
