import Examples.TokenNative

namespace Tests.TokenNativeSpec

open Examples.TokenNative
open SolanaLean.Runtime

#guard (init 0).dummy == 0
#guard get (init 0) == 0
#guard tokenSyncNative == 0

#guard
  match syncNative (init 0) with
  | .ok (st, ret) => st.dummy == 0 && ret == 0
  | .error _ => false

#guard SolanaLean.IR.usesCpi SolanaLean.Golden.extractedTokenNative
#guard SolanaLean.IR.cpiAccountCount SolanaLean.Golden.extractedTokenNative == 3

#guard
  match SolanaLean.Emit.emitCounterAsm SolanaLean.Golden.extractedTokenNative with
  | .error _ => false
  | .ok asm =>
      asm.contains "invoke programIx=2" &&
        asm.contains "dataLen=1" &&
        asm.contains "call sol_invoke_signed_c" &&
        asm.contains "jlt r1, 3" &&
        asm.contains "ja syncNative"

end Tests.TokenNativeSpec
