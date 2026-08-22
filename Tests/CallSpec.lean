import Examples.Call

namespace Tests.CallSpec

open Examples.Call
open SolanaLean.Runtime

#guard (init 0).dummy == 0
#guard get (init 0) == 0
#guard invoke 1 #[] #[] == 0

#guard SolanaLean.IR.usesCpi SolanaLean.Golden.extractedCall
#guard SolanaLean.IR.cpiAccountCount SolanaLean.Golden.extractedCall == 2

#guard
  match SolanaLean.Emit.emitCounterAsm SolanaLean.Golden.extractedCall with
  | .error _ => false
  | .ok asm =>
      asm.contains "invoke programIx=1" &&
        asm.contains "call sol_invoke_signed_c"

end Tests.CallSpec
