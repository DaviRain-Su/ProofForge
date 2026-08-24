import Examples.Transfer

namespace Tests.TransferSpec

open Examples.Transfer
open ProofForge.Svm.Runtime

#guard (init 0).dummy == 0
#guard get (init 0) == 0
#guard systemTransfer 7 == 0

#guard
  match transfer (init 0) 9 with
  | .ok (st, ret) => st.dummy == 0 && ret == 9
  | .error _ => false

#guard ProofForge.Svm.ABI.usesCpi ProofForge.Golden.extractedTransfer
#guard ProofForge.Svm.ABI.cpiAccountCount ProofForge.Golden.extractedTransfer == 4

#guard
  let l := ProofForge.Svm.ABI.inputLayout ProofForge.Golden.extractedTransfer
  l.instructionDataLen == 41352 && l.instructionData == 41360

#guard
  match ProofForge.Svm.Emit.emitCounterAsm ProofForge.Golden.extractedTransfer with
  | .error _ => false
  | .ok asm =>
      let marker :=
        (ProofForge.Svm.ABI.layoutMarkerHex ProofForge.Golden.extractedTransfer).toOption.getD ""
      asm.contains "; validate walked state account owner, data length, and layout marker" &&
        asm.contains "ldxdw r1, [r8 + 40]" &&
        asm.contains "ldxdw r1, [r8 + 80]" &&
        asm.contains s!"lddw r2, {marker}" &&
        asm.contains "body_initialize:\n  ldxdw r7" &&
        asm.contains "stxdw [r6 + ACC0_DATA + 0], r1" &&
        asm.contains "call sol_invoke_signed_c" &&
        asm.contains "invoke programIx=3" &&
        asm.contains "ldxdw r8, [r10 - 520]" &&
        asm.contains "MAX_PERMITTED_DATA_INCREASE" &&
        asm.contains "jlt r1, 4" &&
        asm.contains "call transfer" &&
        asm.contains "stxb [r5 + 8], r1" &&
        asm.contains "stxb [r5 + 24], r1" &&
        !asm.contains "stxb [r5 + 40], r1"

end Tests.TransferSpec
