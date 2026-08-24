import Examples.Create

namespace Tests.CreateSpec

open Examples.Create
open ProofForge.Svm.Runtime

#guard (init 0).dummy == 0
#guard get (init 0) == 0
#guard systemCreate 7 16 == 0

#guard
  match create (init 0) 9 with
  | .ok (st, ret) => st.dummy == 0 && ret == 9
  | .error _ => false

#guard ProofForge.Svm.ABI.usesCpi ProofForge.Golden.extractedCreate
#guard ProofForge.Svm.ABI.cpiAccountCount ProofForge.Golden.extractedCreate == 4

#guard
  match ProofForge.Svm.Emit.emitCounterAsm ProofForge.Golden.extractedCreate with
  | .error _ => false
  | .ok asm =>
      asm.contains "invoke programIx=3" &&
        asm.contains "dataLen=52" &&
        asm.contains "call sol_invoke_signed_c" &&
        asm.contains "jlt r1, 4"

end Tests.CreateSpec
