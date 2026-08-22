import Examples.TokenApprove

namespace Tests.TokenApproveSpec

open Examples.TokenApprove
open ProofForge.Runtime

#guard (init 0).dummy == 0
#guard get (init 0) == 0
#guard tokenApproveChecked 7 6 == 0

#guard
  match approve (init 0) 9 with
  | .ok (st, ret) => st.dummy == 0 && ret == 9
  | .error _ => false

#guard ProofForge.IR.usesCpi ProofForge.Golden.extractedTokenApprove
#guard ProofForge.IR.cpiAccountCount ProofForge.Golden.extractedTokenApprove == 5

#guard
  match ProofForge.Svm.Emit.emitCounterAsm ProofForge.Golden.extractedTokenApprove with
  | .error _ => false
  | .ok asm =>
      asm.contains "invoke programIx=4" &&
        asm.contains "dataLen=10" &&
        asm.contains "call sol_invoke_signed_c" &&
        asm.contains "jlt r1, 5" &&
        asm.contains "ja approve"

end Tests.TokenApproveSpec
