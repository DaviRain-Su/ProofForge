import Examples.Svm.SysAlloc

namespace Tests.SysAllocSpec

open Examples.Svm.SysAlloc
open ProofForge.Svm.Runtime

#guard (init 0).dummy == 0
#guard get (init 0) == 0
#guard systemAllocate 16 == 0
#guard systemAssign == 0

#guard
  match alloc (init 0) with
  | .ok (st, ret) => st.dummy == 0 && ret == 16
  | .error _ => false

#guard
  match assign (init 0) with
  | .ok (st, ret) => st.dummy == 0 && ret == 0
  | .error _ => false

#guard ProofForge.Svm.ABI.usesCpi ProofForge.Golden.extractedSysAlloc
#guard ProofForge.Svm.ABI.cpiAccountCount ProofForge.Golden.extractedSysAlloc == 3

#guard
  match ProofForge.Svm.Emit.emitCounterAsm ProofForge.Golden.extractedSysAlloc with
  | .error _ => false
  | .ok asm =>
      asm.contains "invoke programIx=2" &&
        asm.contains "dataLen=12" &&
        asm.contains "dataLen=36" &&
        asm.contains "call sol_invoke_signed_c" &&
        asm.contains "jlt r1, 3" &&
        asm.contains "call alloc" &&
        asm.contains "call assign"

end Tests.SysAllocSpec
