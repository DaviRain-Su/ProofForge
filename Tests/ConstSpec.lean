import Examples.Const

namespace Tests.ConstSpec

open Examples.Const
open ProofForge.Evm.Runtime

def sample : Addr20 := ⟨1, 2, 3⟩

#guard (init 7 3 sample sample).dummy == 0
#guard get (init 7 3 sample sample) == 0
#guard seedOf (init 7 3 sample sample) == 0
#guard saltOf (init 7 3 sample sample) == 0
#guard whoOf (init 7 3 sample sample) == ⟨0, 0, 0⟩
#guard peerOf (init 7 3 sample sample) == ⟨0, 0, 0⟩

#guard
  match touch (init 7 3 sample sample) 9 with
  | .ok (st, ret) => st.dummy == 9 && ret == 9
  | .error _ => false

#guard
  let p := ProofForge.Evm.Golden.extractedConst
  match ProofForge.Evm.Emit.emitYul p with
  | .error _ => false
  | .ok yul =>
      yul.contains "setimmutable" &&
        yul.contains "loadimmutable" &&
        yul.contains "imm0" &&
        yul.contains "imm1" &&
        yul.contains "immAddr" &&
        yul.contains "immAddr2"

#guard
  match ProofForge.Svm.Emit.emitCounterAsm ProofForge.Golden.extractedEvmCtx with
  | .error reason => reason.contains "svm rejects evm leaf"
  | .ok _ => false

end Tests.ConstSpec
