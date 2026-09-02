import Examples.Svm.TokenMint

namespace Tests.TokenMintSpec

open Examples.Svm.TokenMint
open ProofForge.Svm.Runtime

#guard (init 0).dummy == 0
#guard get (init 0) == 0
#guard tokenMintToChecked 7 6 == 0
#guard tokenBurnChecked 7 6 == 0

#guard
  match mintTo (init 0) 9 with
  | .ok (st, ret) => st.dummy == 0 && ret == 9
  | .error _ => false

#guard
  match burn (init 0) 4 with
  | .ok (st, ret) => st.dummy == 0 && ret == 4
  | .error _ => false

#guard ProofForge.Svm.ABI.usesCpi ProofForge.Golden.extractedTokenMint
#guard ProofForge.Svm.ABI.cpiAccountCount ProofForge.Golden.extractedTokenMint == 5

#guard
  match ProofForge.Svm.Emit.emitCounterAsm ProofForge.Golden.extractedTokenMint with
  | .error _ => false
  | .ok asm =>
      asm.contains "invoke programIx=4" &&
        asm.contains "dataLen=10" &&
        asm.contains "call sol_invoke_signed_c" &&
        asm.contains "jlt r1, 5" &&
        asm.contains "call mintTo" &&
        asm.contains "call burn"

end Tests.TokenMintSpec
