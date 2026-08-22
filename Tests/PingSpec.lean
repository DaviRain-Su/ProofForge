import Examples.Ping

namespace Tests.PingSpec

open Examples.Ping
open SolanaLean.Runtime

#guard (init 0).dummy == 0
#guard get (init 0) == 0
#guard invokeAcc1 == 0

#guard SolanaLean.IR.usesCpi SolanaLean.Golden.extractedPing
#guard SolanaLean.IR.cpiAccountCount SolanaLean.Golden.extractedPing == 2

#guard
  match SolanaLean.Emit.emitCounterAsm SolanaLean.Golden.extractedPing with
  | .error _ => false
  | .ok asm =>
      asm.contains "call sol_invoke_signed_c" &&
        asm.contains "invoke programIx=1" &&
        !asm.contains "invoke programIx=2"

#guard
  match SolanaLean.Emit.emitCounterAsm SolanaLean.Golden.extractedTransfer with
  | .error _ => false
  | .ok asm =>
      asm.contains "invoke programIx=2" &&
        asm.contains "call sol_invoke_signed_c"

end Tests.PingSpec
