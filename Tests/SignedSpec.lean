import Examples.Signed

namespace Tests.SignedSpec

open Examples.Signed
open SolanaLean.Runtime

#guard (init 0).dummy == 0
#guard get (init 0) == 0
#guard invokeSigned 1 #[] #[] "vault" 0 == 0

#guard SolanaLean.IR.usesCpi SolanaLean.Golden.extractedSigned
#guard SolanaLean.IR.cpiAccountCount SolanaLean.Golden.extractedSigned == 2

#guard
  match SolanaLean.Emit.emitCounterAsm SolanaLean.Golden.extractedSigned with
  | .error _ => false
  | .ok asm =>
      asm.contains "call sol_invoke_signed_c" &&
        asm.contains "call sol_try_find_program_address" &&
        asm.contains "lddw r5, 1" &&
        asm.contains "invoke programIx=1"

#guard
  match SolanaLean.Emit.emitCounterAsm SolanaLean.Golden.extractedTransfer with
  | .error _ => false
  | .ok asm =>
      asm.contains "lddw r4, 0" &&
        asm.contains "lddw r5, 0"

end Tests.SignedSpec
