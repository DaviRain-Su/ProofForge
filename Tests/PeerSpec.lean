import Examples.Peer

namespace Tests.PeerSpec

open Examples.Peer
open ProofForge.Runtime

#guard (init 0).dummy == 0
#guard get (init 0) == 0
#guard lamports1 (init 0) == accLamports1
#guard owner1 (init 0) == accOwner1
#guard dataLen1 (init 0) == accDataLen1
#guard signer1 (init 0) == isSigner1
#guard writable1 (init 0) == isWritable1
#guard executable1 (init 0) == isExecutable1

#guard !ProofForge.IR.usesCpi ProofForge.Golden.extractedPeer
#guard ProofForge.IR.usesWalk ProofForge.Golden.extractedPeer
#guard ProofForge.IR.cpiAccountCount ProofForge.Golden.extractedPeer == 2

#guard
  match ProofForge.Svm.Emit.emitCounterAsm ProofForge.Golden.extractedPeer with
  | .error _ => false
  | .ok asm =>
      asm.contains "load walked acc1 +72" &&
        asm.contains "load walked acc1 +40" &&
        asm.contains "load walked acc1 +80" &&
        asm.contains "jlt r1, 2" &&
        asm.contains "call lamports1" &&
        !asm.contains "call sol_invoke_signed_c" &&
        !asm.contains "ja lamports1"

end Tests.PeerSpec
