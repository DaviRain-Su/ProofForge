import Examples.TokenMint2

namespace Tests.TokenMint2Spec

open Examples.TokenMint2
open ProofForge.Runtime

#guard (init 0).dummy == 0
#guard get (init 0) == 0
#guard tokenInitMint == 0

#guard
  match openMint (init 0) with
  | .ok (st, ret) => st.dummy == 0 && ret == 0
  | .error _ => false

#guard ProofForge.IR.usesCpi ProofForge.Golden.extractedTokenMint2
#guard ProofForge.IR.cpiAccountCount ProofForge.Golden.extractedTokenMint2 == 3

#guard
  match ProofForge.Emit.emitCounterAsm ProofForge.Golden.extractedTokenMint2 with
  | .error _ => false
  | .ok asm =>
      asm.contains "invoke programIx=2" &&
        asm.contains "dataLen=35" &&
        asm.contains "call sol_invoke_signed_c" &&
        asm.contains "jlt r1, 3" &&
        asm.contains "ja openMint"

end Tests.TokenMint2Spec
