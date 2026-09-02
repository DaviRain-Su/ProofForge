import Examples.Svm.TokenFreeze

namespace Tests.TokenFreezeSpec

open Examples.Svm.TokenFreeze
open ProofForge.Svm.Runtime

#guard (init 0).dummy == 0
#guard get (init 0) == 0
#guard tokenFreezeAccount == 0
#guard tokenThawAccount == 0

#guard
  match freeze (init 0) with
  | .ok (st, ret) => st.dummy == 0 && ret == 0
  | .error _ => false

#guard
  match thaw (init 0) with
  | .ok (st, ret) => st.dummy == 0 && ret == 0
  | .error _ => false

#guard ProofForge.Svm.ABI.usesCpi ProofForge.Golden.extractedTokenFreeze
#guard ProofForge.Svm.ABI.cpiAccountCount ProofForge.Golden.extractedTokenFreeze == 5

#guard
  match ProofForge.Svm.Emit.emitCounterAsm ProofForge.Golden.extractedTokenFreeze with
  | .error _ => false
  | .ok asm =>
      asm.contains "invoke programIx=4" &&
        asm.contains "dataLen=1" &&
        asm.contains "call sol_invoke_signed_c" &&
        asm.contains "jlt r1, 5" &&
        asm.contains "call freeze" &&
        asm.contains "call thaw"

end Tests.TokenFreezeSpec
