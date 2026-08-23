import Examples.TokenNative

namespace Tests.TokenNativeSpec

open Examples.TokenNative
open ProofForge.Svm.Runtime

#guard (init 0).dummy == 0
#guard get (init 0) == 0
#guard tokenSyncNative == 0

#guard
  match syncNative (init 0) with
  | .ok (st, ret) => st.dummy == 0 && ret == 0
  | .error _ => false

#guard ProofForge.IR.usesCpi ProofForge.Golden.extractedTokenNative
#guard ProofForge.IR.cpiAccountCount ProofForge.Golden.extractedTokenNative == 3

#guard
  match ProofForge.Svm.Emit.emitCounterAsm ProofForge.Golden.extractedTokenNative with
  | .error _ => false
  | .ok asm =>
      asm.contains "invoke programIx=2" &&
        asm.contains "dataLen=1" &&
        asm.contains "call sol_invoke_signed_c" &&
        asm.contains "jlt r1, 3" &&
        asm.contains "ja syncNative"

end Tests.TokenNativeSpec
