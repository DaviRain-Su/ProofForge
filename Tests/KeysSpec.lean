import Examples.Keys

namespace Tests.KeysSpec

open Examples.Keys
open ProofForge.Svm.Runtime

#guard (init 0).dummy == 0
#guard get (init 0) == 0
#guard key00 (init 0) == accKeyWord 0 0
#guard key03 (init 0) == accKeyWord 0 3
#guard owner00 (init 0) == accOwnerWord 0 0
#guard key10 (init 0) == accKeyWord 1 0
#guard owner13 (init 0) == accOwnerWord 1 3
#guard accKeyWord 0 0 == 0
#guard accOwnerWord 1 3 == 0

#guard !ProofForge.IR.usesCpi ProofForge.Golden.extractedKeys
#guard ProofForge.IR.usesWalk ProofForge.Golden.extractedKeys
#guard ProofForge.IR.cpiAccountCount ProofForge.Golden.extractedKeys == 2

#guard
  match ProofForge.Svm.Emit.emitCounterAsm ProofForge.Golden.extractedKeys with
  | .error _ => false
  | .ok asm =>
      asm.contains "load acc0 key word 0" &&
        asm.contains "load acc0 key word 3" &&
        asm.contains "load acc0 owner word 0" &&
        asm.contains "load acc0 owner word 3" &&
        asm.contains "load walked acc1 +8" &&
        asm.contains "load walked acc1 +32" &&
        asm.contains "load walked acc1 +40" &&
        asm.contains "load walked acc1 +64" &&
        asm.contains "jlt r1, 2" &&
        asm.contains "call key00" &&
        asm.contains "call key10" &&
        !asm.contains "call sol_invoke_signed_c" &&
        !asm.contains "ja key00"

end Tests.KeysSpec
