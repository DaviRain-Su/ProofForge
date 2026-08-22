import Examples.SysXfer

namespace Tests.SysXferSpec

open Examples.SysXfer
open SolanaLean.Runtime

#guard (init 0).dummy == 0
#guard get (init 0) == 0
#guard systemTransferWithSeed 7 == 0

#guard
  match sendSeed (init 0) 9 with
  | .ok (st, ret) => st.dummy == 0 && ret == 9
  | .error _ => false

#guard SolanaLean.IR.usesCpi SolanaLean.Golden.extractedSysXfer
#guard SolanaLean.IR.cpiAccountCount SolanaLean.Golden.extractedSysXfer == 4

#guard
  match SolanaLean.Emit.emitCounterAsm SolanaLean.Golden.extractedSysXfer with
  | .error _ => false
  | .ok asm =>
      asm.contains "invoke programIx=3" &&
        asm.contains "dataLen=57" &&
        asm.contains "call sol_invoke_signed_c" &&
        asm.contains "jlt r1, 4" &&
        asm.contains "ja sendSeed"

end Tests.SysXferSpec
