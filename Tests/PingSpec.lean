import Examples.Svm.Ping

namespace Tests.PingSpec

open Examples.Svm.Ping
open ProofForge.Svm.Runtime

#guard (init 0).dummy == 0
#guard get (init 0) == 0
#guard invokeAcc1 == 0

#guard ProofForge.Svm.ABI.usesCpi ProofForge.Golden.extractedPing
#guard ProofForge.Svm.ABI.cpiAccountCount ProofForge.Golden.extractedPing == 3

#guard
  match ProofForge.Svm.Emit.emitCounterAsm ProofForge.Golden.extractedPing with
  | .error _ => false
  | .ok asm =>
      asm.contains "call sol_invoke_signed_c" &&
        asm.contains "invoke programIx=2" &&
        !asm.contains "invoke programIx=1"

#guard
  match ProofForge.Svm.Emit.emitCounterAsm ProofForge.Golden.extractedTransfer with
  | .error _ => false
  | .ok asm =>
      asm.contains "invoke programIx=3" &&
        asm.contains "call sol_invoke_signed_c"

end Tests.PingSpec
