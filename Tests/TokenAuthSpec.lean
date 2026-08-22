import Examples.TokenAuth

namespace Tests.TokenAuthSpec

open Examples.TokenAuth
open SolanaLean.Runtime

#guard (init 0).dummy == 0
#guard get (init 0) == 0
#guard tokenSetMintAuthority == 0
#guard tokenRevoke == 0

#guard
  match setAuth (init 0) with
  | .ok (st, ret) => st.dummy == 0 && ret == 0
  | .error _ => false

#guard
  match revoke (init 0) with
  | .ok (st, ret) => st.dummy == 0 && ret == 0
  | .error _ => false

#guard SolanaLean.IR.usesCpi SolanaLean.Golden.extractedTokenAuth
#guard SolanaLean.IR.cpiAccountCount SolanaLean.Golden.extractedTokenAuth == 4

#guard
  match SolanaLean.Emit.emitCounterAsm SolanaLean.Golden.extractedTokenAuth with
  | .error _ => false
  | .ok asm =>
      asm.contains "invoke programIx=3" &&
        asm.contains "dataLen=35" &&
        asm.contains "dataLen=1" &&
        asm.contains "call sol_invoke_signed_c" &&
        asm.contains "jlt r1, 4" &&
        asm.contains "ja setAuth" &&
        asm.contains "ja revoke"

end Tests.TokenAuthSpec
