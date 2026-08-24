import Examples.Trio

namespace Tests.TrioSpec

open Examples.Trio
open ProofForge.Svm.Runtime

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

#guard ProofForge.Svm.ABI.maxTxAccountLocks == 64
#guard ProofForge.Svm.ABI.maxAccountsPerInstruction == 255
#guard ProofForge.Svm.ABI.accInRange 0 == true
#guard ProofForge.Svm.ABI.accInRange 63 == true
#guard ProofForge.Svm.ABI.accInRange 64 == false

#guard !ProofForge.Svm.ABI.usesCpi ProofForge.Golden.extractedTrio
#guard ProofForge.Svm.ABI.usesWalk ProofForge.Golden.extractedTrio
#guard ProofForge.Svm.ABI.cpiAccountCount ProofForge.Golden.extractedTrio == 3

#guard
  match ProofForge.Svm.Emit.emitCounterAsm ProofForge.Golden.extractedTrio with
  | .error _ => false
  | .ok asm =>
      let marker :=
        (ProofForge.Svm.ABI.layoutMarkerHex ProofForge.Golden.extractedTrio).toOption.getD ""
      asm.contains "; validate walked state account owner, data length, and layout marker" &&
        asm.contains "ldxdw r1, [r8 + 40]" &&
        asm.contains "ldxdw r1, [r8 + 80]" &&
        asm.contains s!"lddw r2, {marker}" &&
        asm.contains "body_initialize:\n  ldxdw r7" &&
        asm.contains "stxdw [r6 + ACC0_DATA + 0], r1" &&
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
