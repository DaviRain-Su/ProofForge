import Examples.TokenFreeze

namespace Tests.TokenFreezeSpec

open Examples.TokenFreeze
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

#guard ProofForge.IR.usesCpi ProofForge.Golden.extractedTokenFreeze
#guard ProofForge.IR.cpiAccountCount ProofForge.Golden.extractedTokenFreeze == 4

#guard
  match ProofForge.Svm.Emit.emitCounterAsm ProofForge.Golden.extractedTokenFreeze with
  | .error _ => false
  | .ok asm =>
      asm.contains "invoke programIx=3" &&
        asm.contains "dataLen=1" &&
        asm.contains "call sol_invoke_signed_c" &&
        asm.contains "jlt r1, 4" &&
        asm.contains "ja freeze" &&
        asm.contains "ja thaw"

end Tests.TokenFreezeSpec
