import Examples.SysXfer

namespace Tests.SysXferSpec

open Examples.SysXfer
open ProofForge.Svm.Sdk

#guard (init 0).dummy == 0
#guard get (init 0) == 0
#guard System.AsciiSeed.transfer "vault" 7 == 0

#guard
  match sendSeed (init 0) 9 with
  | .ok (st, ret) => st.dummy == 0 && ret == 9
  | .error _ => false

#guard ProofForge.Svm.ABI.usesCpi ProofForge.Golden.extractedSysXfer
#guard ProofForge.Svm.ABI.cpiAccountCount ProofForge.Golden.extractedSysXfer == 5

#guard
  match ProofForge.Svm.Emit.emitCounterAsm ProofForge.Golden.extractedSysXfer with
  | .error _ => false
  | .ok asm =>
      asm.contains "invoke programIx=4" &&
        asm.contains "dataLen=57" &&
        asm.contains "call sol_invoke_signed_c" &&
        asm.contains "jlt r1, 5" &&
        asm.contains "call sendSeed"

end Tests.SysXferSpec
