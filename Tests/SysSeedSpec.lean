import Examples.SysSeed

namespace Tests.SysSeedSpec

open Examples.SysSeed
open ProofForge.Svm.Runtime

#guard (init 0).dummy == 0
#guard get (init 0) == 0
#guard systemAllocateWithSeed 16 == 0
#guard systemCreateWithSeed 7 16 == 0
#guard systemAssignWithSeed == 0

#guard
  match openSeed (init 0) with
  | .ok (st, ret) => st.dummy == 0 && ret == 16
  | .error _ => false

#guard
  match createSeed (init 0) 9 with
  | .ok (st, ret) => st.dummy == 0 && ret == 9
  | .error _ => false

#guard
  match assignSeed (init 0) with
  | .ok (st, ret) => st.dummy == 0 && ret == 0
  | .error _ => false

#guard ProofForge.Svm.ABI.usesCpi ProofForge.Golden.extractedSysSeed
#guard ProofForge.Svm.ABI.cpiAccountCount ProofForge.Golden.extractedSysSeed == 3

#guard
  match ProofForge.Svm.Emit.emitCounterAsm ProofForge.Golden.extractedSysSeed with
  | .error _ => false
  | .ok asm =>
      asm.contains "invoke programIx=2" &&
        asm.contains "dataLen=89" &&
        asm.contains "dataLen=97" &&
        asm.contains "dataLen=81" &&
        asm.contains "call sol_invoke_signed_c" &&
        asm.contains "jlt r1, 3" &&
        asm.contains "ja openSeed" &&
        asm.contains "ja createSeed" &&
        asm.contains "ja assignSeed"

end Tests.SysSeedSpec
