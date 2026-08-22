import Examples.Transfer

namespace Tests.TransferSpec

open Examples.Transfer
open ProofForge.Runtime

#guard (init 0).dummy == 0
#guard get (init 0) == 0
#guard systemTransfer 7 == 0

#guard
  match transfer (init 0) 9 with
  | .ok (st, ret) => st.dummy == 0 && ret == 9
  | .error _ => false

#guard ProofForge.IR.usesCpi ProofForge.Golden.extractedTransfer
#guard ProofForge.IR.cpiAccountCount ProofForge.Golden.extractedTransfer == 3

#guard
  let l := ProofForge.IR.inputLayout ProofForge.Golden.extractedTransfer
  l.instructionDataLen == 31016 && l.instructionData == 31024

#guard
  match ProofForge.Emit.emitCounterAsm ProofForge.Golden.extractedTransfer with
  | .error _ => false
  | .ok asm =>
      asm.contains "call sol_invoke_signed_c" &&
        asm.contains "MAX_PERMITTED_DATA_INCREASE" &&
        asm.contains "jlt r1, 3" &&
        asm.contains "ja transfer" &&
        asm.contains "stxb [r5 + 8], r1" &&
        asm.contains "stxb [r5 + 24], r1" &&
        !asm.contains "stxb [r5 + 40], r1"

end Tests.TransferSpec
