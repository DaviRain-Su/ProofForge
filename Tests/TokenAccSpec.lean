import Examples.TokenAcc

namespace Tests.TokenAccSpec

open Examples.TokenAcc
open ProofForge.Runtime

#guard (init 0).dummy == 0
#guard get (init 0) == 0
#guard tokenInitAccount == 0
#guard tokenCloseAccount == 0

#guard
  match openAcc (init 0) with
  | .ok (st, ret) => st.dummy == 0 && ret == 0
  | .error _ => false

#guard
  match closeAcc (init 0) with
  | .ok (st, ret) => st.dummy == 0 && ret == 0
  | .error _ => false

#guard ProofForge.IR.usesCpi ProofForge.Golden.extractedTokenAcc
#guard ProofForge.IR.cpiAccountCount ProofForge.Golden.extractedTokenAcc == 4

#guard
  match ProofForge.Svm.Emit.emitCounterAsm ProofForge.Golden.extractedTokenAcc with
  | .error _ => false
  | .ok asm =>
      asm.contains "invoke programIx=3" &&
        asm.contains "dataLen=33" &&
        asm.contains "dataLen=1" &&
        asm.contains "call sol_invoke_signed_c" &&
        asm.contains "jlt r1, 4" &&
        asm.contains "ja openAcc" &&
        asm.contains "ja closeAcc"

end Tests.TokenAccSpec
