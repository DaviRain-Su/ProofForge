import Examples.CreatePda

namespace Tests.CreatePdaSpec

open Examples.CreatePda
open ProofForge.Runtime

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

#guard ProofForge.IR.usesCpi ProofForge.Golden.extractedCreatePda
#guard ProofForge.IR.cpiAccountCount ProofForge.Golden.extractedCreatePda == 3

#guard
  match ProofForge.Emit.emitCounterAsm ProofForge.Golden.extractedCreatePda with
  | .error _ => false
  | .ok asm =>
      asm.contains "invoke programIx=2" &&
        asm.contains "dataLen=52" &&
        asm.contains "call sol_invoke_signed_c" &&
        asm.contains "jlt r1, 3" &&
        asm.contains "ja openPda" &&
        asm.contains "ja openBad"

end Tests.CreatePdaSpec
