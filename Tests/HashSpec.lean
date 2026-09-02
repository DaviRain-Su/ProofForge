import Examples.Svm.Hash

namespace Tests.HashSpec

open Examples.Svm.Hash
open ProofForge.Svm.Runtime

#guard (init 0).dummy == 0
#guard get (init 0) == 0
#guard vault (init 0) == sha256Lit "vault"
#guard ok (init 0) == sha256Lit "ok"
#guard empty (init 0) == sha256Lit ""
#guard sha256Lit "vault" == 0
#guard sha256Lit "ok" == 0
#guard sha256Lit "" == 0

#guard !ProofForge.Svm.ABI.usesCpi ProofForge.Golden.extractedHash
#guard !ProofForge.Svm.ABI.usesWalk ProofForge.Golden.extractedHash

#guard
  match ProofForge.Svm.Emit.emitCounterAsm ProofForge.Golden.extractedHash with
  | .error _ => false
  | .ok asm =>
      asm.contains "call sol_sha256" &&
        asm.contains "sha256Lit seed=vault" &&
        asm.contains "sha256Lit seed=ok" &&
        asm.contains "sha256Lit seed=" &&
        asm.contains "call vault" &&
        asm.contains "call ok" &&
        asm.contains "call empty" &&
        !asm.contains "call sol_invoke_signed_c"

end Tests.HashSpec
