import Examples.Svm.Keccak

namespace Tests.KeccakSpec

open Examples.Svm.Keccak
open ProofForge.Svm.Runtime

#guard (init 0).dummy == 0
#guard get (init 0) == 0
#guard vault (init 0) == keccak256Lit "vault"
#guard ok (init 0) == keccak256Lit "ok"
#guard empty (init 0) == keccak256Lit ""
#guard keccak256Lit "vault" == 0
#guard keccak256Lit "ok" == 0
#guard keccak256Lit "" == 0

#guard !ProofForge.Svm.ABI.usesCpi ProofForge.Golden.extractedKeccak
#guard !ProofForge.Svm.ABI.usesWalk ProofForge.Golden.extractedKeccak

#guard
  match ProofForge.Svm.Emit.emitCounterAsm ProofForge.Golden.extractedKeccak with
  | .error _ => false
  | .ok asm =>
      asm.contains "call sol_keccak256" &&
        asm.contains "keccak256Lit seed=vault" &&
        asm.contains "keccak256Lit seed=ok" &&
        asm.contains "keccak256Lit seed=" &&
        asm.contains "call vault" &&
        asm.contains "call ok" &&
        asm.contains "call empty" &&
        !asm.contains "call sol_sha256" &&
        !asm.contains "call sol_invoke_signed_c"

end Tests.KeccakSpec
