import Examples.TokenAcc

namespace Tests.TokenAccSpec

open Examples.TokenAcc
open SolanaLean.Runtime

#guard (init 0).dummy == 0
#guard get (init 0) == 0
#guard tokenInitAccount == 0
#guard tokenCloseAccount == 0

#guard
  match openAcc (init 0) with
  | .ok (st, ret) => st.dummy == 0 && ret == 0
  | .error _ => false

#guard
  match closeAcc (init 0) with
  | .ok (st, ret) => st.dummy == 0 && ret == 0
  | .error _ => false

#guard SolanaLean.IR.usesCpi SolanaLean.Golden.extractedTokenAcc
#guard SolanaLean.IR.cpiAccountCount SolanaLean.Golden.extractedTokenAcc == 4

#guard
  match SolanaLean.Emit.emitCounterAsm SolanaLean.Golden.extractedTokenAcc with
  | .error _ => false
  | .ok asm =>
      asm.contains "invoke programIx=3" &&
        asm.contains "dataLen=33" &&
        asm.contains "dataLen=1" &&
        asm.contains "call sol_invoke_signed_c" &&
        asm.contains "jlt r1, 4" &&
        asm.contains "ja openAcc" &&
        asm.contains "ja closeAcc"

end Tests.TokenAccSpec
