import Examples.TokenAcc

namespace Tests.TokenAccSpec

open Examples.TokenAcc
open ProofForge.Svm.Runtime

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

#guard ProofForge.Svm.ABI.usesCpi ProofForge.Golden.extractedTokenAcc
#guard ProofForge.Svm.ABI.cpiAccountCount ProofForge.Golden.extractedTokenAcc == 5

#guard
  match ProofForge.Svm.Emit.emitCounterAsm ProofForge.Golden.extractedTokenAcc with
  | .error _ => false
  | .ok asm =>
      asm.contains "invoke programIx=4" &&
        asm.contains "dataLen=33" &&
        asm.contains "dataLen=1" &&
        asm.contains "call sol_invoke_signed_c" &&
        asm.contains "jlt r1, 5" &&
        asm.contains "call openAcc" &&
        asm.contains "call closeAcc"

end Tests.TokenAccSpec
