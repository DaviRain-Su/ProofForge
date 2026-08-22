import Examples.TokenSize

namespace Tests.TokenSizeSpec

open Examples.TokenSize
open SolanaLean.Runtime

#guard (init 0).dummy == 0
#guard get (init 0) == 0
#guard tokenAccountSize == 0
#guard cpiReturn == 0

#guard
  match size (init 0) with
  | .ok (st, ret) => st.dummy == 0 && ret == 0
  | .error _ => false

#guard SolanaLean.IR.usesCpi SolanaLean.Golden.extractedTokenSize
#guard SolanaLean.IR.cpiAccountCount SolanaLean.Golden.extractedTokenSize == 3

#guard
  match SolanaLean.Emit.emitCounterAsm SolanaLean.Golden.extractedTokenSize with
  | .error _ => false
  | .ok asm =>
      asm.contains "invoke programIx=2" &&
        asm.contains "dataLen=1" &&
        asm.contains "call sol_invoke_signed_c" &&
        asm.contains "call sol_get_return_data" &&
        asm.contains "jlt r1, 3" &&
        asm.contains "ja size"

end Tests.TokenSizeSpec
