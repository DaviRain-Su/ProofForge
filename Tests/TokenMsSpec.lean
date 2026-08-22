import Examples.TokenMs

namespace Tests.TokenMsSpec

open Examples.TokenMs
open SolanaLean.Runtime

#guard (init 0).dummy == 0
#guard get (init 0) == 0

#guard SolanaLean.IR.usesCpi SolanaLean.Golden.extractedTokenMs
#guard SolanaLean.IR.cpiAccountCount SolanaLean.Golden.extractedTokenMs == 5

#guard
  match SolanaLean.Emit.emitCounterAsm SolanaLean.Golden.extractedTokenMs with
  | .error _ => false
  | .ok asm =>
      asm.contains "call sol_invoke_signed_c" &&
        asm.contains "ja openMs" &&
        asm.contains "jlt r1, 5"

end Tests.TokenMsSpec
