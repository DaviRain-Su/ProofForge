import Examples.TokenOwner

namespace Tests.TokenOwnerSpec

open Examples.TokenOwner
open SolanaLean.Runtime

#guard (init 0).dummy == 0
#guard get (init 0) == 0

#guard SolanaLean.IR.usesCpi SolanaLean.Golden.extractedTokenOwner

#guard
  match SolanaLean.Emit.emitCounterAsm SolanaLean.Golden.extractedTokenOwner with
  | .error _ => false
  | .ok asm =>
      asm.contains "call sol_invoke_signed_c" &&
        asm.contains "ja setOwner" &&
        asm.contains "ja approve"

end Tests.TokenOwnerSpec
