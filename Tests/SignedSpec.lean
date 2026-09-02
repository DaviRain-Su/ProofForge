import Examples.Svm.Signed

namespace Tests.SignedSpec

open Examples.Svm.Signed
open ProofForge.Svm.Runtime

#guard (init 0).dummy == 0
#guard get (init 0) == 0
#guard invokeSigned 1 #[] #[] "vault" 0 == 0

#guard ProofForge.Svm.ABI.usesCpi ProofForge.Golden.extractedSigned
#guard ProofForge.Svm.ABI.cpiAccountCount ProofForge.Golden.extractedSigned == 3

#guard
  match ProofForge.Svm.Emit.emitCounterAsm ProofForge.Golden.extractedSigned with
  | .error _ => false
  | .ok asm =>
      asm.contains "call sol_invoke_signed_c" &&
        asm.contains "call sol_try_find_program_address" &&
        asm.contains "metas=1" &&
        asm.contains "lddw r5, 1" &&
        asm.contains "invoke programIx=2"

#guard
  match ProofForge.Svm.Emit.emitCounterAsm ProofForge.Golden.extractedTransfer with
  | .error _ => false
  | .ok asm =>
      asm.contains "lddw r4, 0" &&
        asm.contains "lddw r5, 0"

end Tests.SignedSpec
