import Examples.Info

namespace Tests.InfoSpec

open Examples.Info
open ProofForge.Runtime

#guard (init 0).dummy == 0
#guard get (init 0) == 0
#guard lamports (init 0) == accLamports0
#guard owner0 (init 0) == accOwner0
#guard dataLen (init 0) == accDataLen0
#guard nacc (init 0) == accN
#guard signer (init 0) == isSigner0
#guard writable (init 0) == isWritable0
#guard executable (init 0) == isExecutable0

#guard
  match ProofForge.Svm.Emit.emitCounterAsm ProofForge.Golden.extractedInfo with
  | .error _ => false
  | .ok asm =>
      asm.contains "ACC0_LAMPORTS" &&
        asm.contains "ACC0_OWNER + 0" &&
        asm.contains "ACC0_DATA_LEN" &&
        asm.contains "NUM_ACCOUNTS" &&
        asm.contains "ACC0_HEADER + 1" &&
        asm.contains "ACC0_HEADER + 2" &&
        asm.contains "ACC0_HEADER + 3" &&
        asm.contains "call lamports" &&
        !asm.contains "call sol_invoke_signed_c"

end Tests.InfoSpec
