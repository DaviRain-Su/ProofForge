import Examples.SysXfer

namespace Tests.SysXferSpec

open Examples.SysXfer
open ProofForge.Svm.Runtime

#guard (init 0).dummy == 0
#guard get (init 0) == 0
#guard systemTransferWithSeed 7 == 0

#guard
  match sendSeed (init 0) 9 with
  | .ok (st, ret) => st.dummy == 0 && ret == 9
  | .error _ => false

#guard ProofForge.Svm.ABI.usesCpi ProofForge.Golden.extractedSysXfer
#guard ProofForge.Svm.ABI.cpiAccountCount ProofForge.Golden.extractedSysXfer == 4

#guard
  match ProofForge.Svm.Emit.emitCounterAsm ProofForge.Golden.extractedSysXfer with
  | .error _ => false
  | .ok asm =>
      asm.contains "invoke programIx=3" &&
        asm.contains "dataLen=57" &&
        asm.contains "call sol_invoke_signed_c" &&
        asm.contains "jlt r1, 4" &&
        asm.contains "ja sendSeed"

end Tests.SysXferSpec
