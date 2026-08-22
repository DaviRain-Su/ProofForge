import Examples.Pda

namespace Tests.PdaSpec

open Examples.Pda
open SolanaLean.Runtime

#guard (init 0).dummy == 0
#guard get (init 0) == 0
#guard bump (init 0) == findPda "vault"
#guard findPda "vault" == 0
#guard check (init 0) == 0
#guard checkBad (init 0) == 0
#guard checkPda "vault" 0 == 0

#guard
  match SolanaLean.Emit.emitCounterAsm SolanaLean.Golden.extractedPda with
  | .error _ => false
  | .ok asm =>
      asm.contains "call sol_try_find_program_address" &&
        asm.contains "call sol_create_program_address" &&
        asm.contains "findPda seed=vault" &&
        asm.contains "checkPda seed=vault" &&
        asm.contains "call bump" &&
        asm.contains "call check" &&
        asm.contains "call checkBad"

end Tests.PdaSpec
