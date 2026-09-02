import Examples.Svm.CreatePda

namespace Tests.CreatePdaSpec

open Examples.Svm.CreatePda
open ProofForge.Svm.Runtime

#guard (init 0).dummy == 0
#guard get (init 0) == 0
#guard createPda 7 == 0

#guard
  match openPda (init 0) 9 with
  | .ok (st, ret) => st.dummy == 0 && ret == 9
  | .error _ => false

#guard
  match openBad (init 0) 9 with
  | .ok (st, ret) => st.dummy == 0 && ret == 9
  | .error _ => false

#guard ProofForge.Svm.ABI.usesCpi ProofForge.Golden.extractedCreatePda
#guard ProofForge.Svm.ABI.cpiAccountCount ProofForge.Golden.extractedCreatePda == 4

#guard
  match ProofForge.Svm.Emit.emitCounterAsm ProofForge.Golden.extractedCreatePda with
  | .error _ => false
  | .ok asm =>
      asm.contains "invoke programIx=3" &&
        asm.contains "dataLen=52" &&
        asm.contains "call sol_invoke_signed_c" &&
        asm.contains "jlt r1, 4" &&
        asm.contains "call openPda" &&
        asm.contains "call openBad"

end Tests.CreatePdaSpec
