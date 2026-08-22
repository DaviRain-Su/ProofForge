import Examples.SysAlloc

namespace Tests.SysAllocSpec

open Examples.SysAlloc
open ProofForge.Runtime

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

#guard ProofForge.IR.usesCpi ProofForge.Golden.extractedSysAlloc
#guard ProofForge.IR.cpiAccountCount ProofForge.Golden.extractedSysAlloc == 2

#guard
  match ProofForge.Emit.emitCounterAsm ProofForge.Golden.extractedSysAlloc with
  | .error _ => false
  | .ok asm =>
      asm.contains "invoke programIx=1" &&
        asm.contains "dataLen=12" &&
        asm.contains "dataLen=36" &&
        asm.contains "call sol_invoke_signed_c" &&
        asm.contains "jlt r1, 2" &&
        asm.contains "ja alloc" &&
        asm.contains "ja assign"

end Tests.SysAllocSpec
