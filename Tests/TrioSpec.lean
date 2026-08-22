import Examples.Trio

namespace Tests.TrioSpec

open Examples.Trio
open ProofForge.Runtime

#guard (init 0).dummy == 0
#guard get (init 0) == 0
#guard lamports2 (init 0) == accLamports 2
#guard dataLen2 (init 0) == accDataLen 2
#guard signer2 (init 0) == isSigner 2
#guard key20 (init 0) == accKeyWord 2 0
#guard needSig1 (init 0) == signerKey 1
#guard self0 (init 0) == ownerIsSelf 0
#guard self2 (init 0) == ownerIsSelf 2
#guard accLamports 2 == 0
#guard signerKey 1 == 0
#guard ownerIsSelf 0 == 0

#guard !ProofForge.IR.usesCpi ProofForge.Golden.extractedTrio
#guard ProofForge.IR.usesWalk ProofForge.Golden.extractedTrio
#guard ProofForge.IR.cpiAccountCount ProofForge.Golden.extractedTrio == 3

#guard
  match ProofForge.Svm.Emit.emitCounterAsm ProofForge.Golden.extractedTrio with
  | .error _ => false
  | .ok asm =>
      asm.contains "load walked acc2 +72" &&
        asm.contains "load walked acc2 +80" &&
        asm.contains "load walked acc2 +8" &&
        asm.contains "jlt r1, 3" &&
        asm.contains "ownerIsSelf acc=0" &&
        asm.contains "ownerIsSelf acc=2" &&
        asm.contains "call lamports2" &&
        asm.contains "call needSig1" &&
        !asm.contains "call sol_invoke_signed_c" &&
        !asm.contains "ja lamports2"

end Tests.TrioSpec
