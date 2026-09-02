import Examples.Svm.Ata

namespace Tests.AtaSpec

open Examples.Svm.Ata
open ProofForge.Svm.Sdk

#guard (init 0).dummy == 0
#guard get (init 0) == 0
#guard AssociatedToken.createIdempotent == 0

#guard
  match openAta (init 0) with
  | .ok (st, ret) => st.dummy == 0 && ret == 0
  | .error _ => false

#guard ProofForge.Svm.ABI.usesCpi ProofForge.Golden.extractedAta
#guard ProofForge.Svm.ABI.cpiAccountCount ProofForge.Golden.extractedAta == 8

#guard
  match ProofForge.Svm.Emit.emitCounterAsm ProofForge.Golden.extractedAta with
  | .error _ => false
  | .ok asm =>
      asm.contains "invoke programIx=7" &&
        asm.contains "dataLen=1" &&
        asm.contains "call sol_invoke_signed_c" &&
        asm.contains "jlt r1, 8"

end Tests.AtaSpec
