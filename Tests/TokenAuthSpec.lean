import Examples.TokenAuth

namespace Tests.TokenAuthSpec

open Examples.TokenAuth
open ProofForge.Svm.Runtime

#guard (init 0).dummy == 0
#guard get (init 0) == 0
#guard tokenSetMintAuthority == 0
#guard tokenRevoke == 0

#guard
  match setAuth (init 0) with
  | .ok (st, ret) => st.dummy == 0 && ret == 0
  | .error _ => false

#guard
  match revoke (init 0) with
  | .ok (st, ret) => st.dummy == 0 && ret == 0
  | .error _ => false

#guard ProofForge.Svm.ABI.usesCpi ProofForge.Golden.extractedTokenAuth
#guard ProofForge.Svm.ABI.cpiAccountCount ProofForge.Golden.extractedTokenAuth == 5

#guard
  match ProofForge.Svm.Emit.emitCounterAsm ProofForge.Golden.extractedTokenAuth with
  | .error _ => false
  | .ok asm =>
      asm.contains "invoke programIx=4" &&
        asm.contains "dataLen=35" &&
        asm.contains "dataLen=1" &&
        asm.contains "call sol_invoke_signed_c" &&
        asm.contains "jlt r1, 5" &&
        asm.contains "call setAuth" &&
        asm.contains "call revoke"

end Tests.TokenAuthSpec
