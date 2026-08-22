import Examples.Pda

namespace Tests.PdaSpec

open Examples.Pda
open SolanaLean.Runtime

#guard (init 0).dummy == 0
#guard get (init 0) == 0
#guard bump (init 0) == findPda "vault"
#guard findPda "vault" == 0

#guard
  match SolanaLean.Emit.emitCounterAsm SolanaLean.Golden.extractedPda with
  | .error _ => false
  | .ok asm =>
      asm.contains "call sol_try_find_program_address" &&
        asm.contains "findPda seed=vault" &&
        asm.contains "call bump"

end Tests.PdaSpec
