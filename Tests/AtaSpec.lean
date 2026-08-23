import Examples.Ata

namespace Tests.AtaSpec

open Examples.Ata
open ProofForge.Svm.Runtime

#guard (init 0).dummy == 0
#guard get (init 0) == 0
#guard ataCreateIdempotent == 0

#guard
  match openAta (init 0) with
  | .ok (st, ret) => st.dummy == 0 && ret == 0
  | .error _ => false

#guard ProofForge.Svm.ABI.usesCpi ProofForge.Golden.extractedAta
#guard ProofForge.Svm.ABI.cpiAccountCount ProofForge.Golden.extractedAta == 7

#guard
  match ProofForge.Svm.Emit.emitCounterAsm ProofForge.Golden.extractedAta with
  | .error _ => false
  | .ok asm =>
      asm.contains "invoke programIx=6" &&
        asm.contains "dataLen=1" &&
        asm.contains "call sol_invoke_signed_c" &&
        asm.contains "jlt r1, 7"

end Tests.AtaSpec
