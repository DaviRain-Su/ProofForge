import Examples.Nonce

namespace Tests.NonceSpec

open Examples.Nonce
open SolanaLean.Runtime

#guard (init 0).dummy == 0
#guard get (init 0) == 0

#guard SolanaLean.IR.usesCpi SolanaLean.Golden.extractedNonce
#guard SolanaLean.IR.cpiAccountCount SolanaLean.Golden.extractedNonce == 4

#guard
  match SolanaLean.Emit.emitCounterAsm SolanaLean.Golden.extractedNonce with
  | .error _ => false
  | .ok asm =>
      asm.contains "call sol_invoke_signed_c" &&
        asm.contains "ja advance" &&
        asm.contains "jlt r1, 4"

end Tests.NonceSpec
