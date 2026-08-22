import Examples.Transfer

namespace Tests.TransferSpec

open Examples.Transfer
open SolanaLean.Runtime

#guard (init 0).dummy == 0
#guard get (init 0) == 0
#guard systemTransfer 7 == 7

#guard
  match transfer (init 0) 9 with
  | .ok (st, ret) => st.dummy == 0 && ret == 9
  | .error _ => false

#guard SolanaLean.IR.usesSystemTransfer SolanaLean.Golden.extractedTransfer

#guard
  let l := SolanaLean.IR.inputLayout SolanaLean.Golden.extractedTransfer
  l.instructionDataLen == 31016 && l.instructionData == 31024

#guard
  match SolanaLean.Emit.emitCounterAsm SolanaLean.Golden.extractedTransfer with
  | .error _ => false
  | .ok asm =>
      asm.contains "call sol_invoke_signed_c" &&
        asm.contains "MAX_PERMITTED_DATA_INCREASE" &&
        asm.contains "jlt r1, 3" &&
        asm.contains "ja transfer"

end Tests.TransferSpec
