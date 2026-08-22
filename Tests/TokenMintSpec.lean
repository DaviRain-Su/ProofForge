import Examples.TokenMint

namespace Tests.TokenMintSpec

open Examples.TokenMint
open SolanaLean.Runtime

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

#guard SolanaLean.IR.usesCpi SolanaLean.Golden.extractedTokenMint
#guard SolanaLean.IR.cpiAccountCount SolanaLean.Golden.extractedTokenMint == 4

#guard
  match SolanaLean.Emit.emitCounterAsm SolanaLean.Golden.extractedTokenMint with
  | .error _ => false
  | .ok asm =>
      asm.contains "invoke programIx=3" &&
        asm.contains "dataLen=10" &&
        asm.contains "call sol_invoke_signed_c" &&
        asm.contains "jlt r1, 4" &&
        asm.contains "ja mintTo" &&
        asm.contains "ja burn"

end Tests.TokenMintSpec
