import Examples.Const

namespace Tests.ConstSpec

open Examples.Const
open ProofForge.Evm.Runtime

def sample : Addr20 := ⟨1, 2, 3⟩

#guard (init 7 sample).dummy == 0
#guard get (init 7 sample) == 0
#guard seedOf (init 7 sample) == 0
#guard whoOf (init 7 sample) == ⟨0, 0, 0⟩

#guard
  match touch (init 7 sample) 9 with
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
        yul.contains "immAddr"

#guard
  match ProofForge.Svm.Emit.emitCounterAsm ProofForge.Golden.extractedEvmCtx with
  | .error reason => reason.contains "svm rejects evm leaf"
  | .ok _ => false

end Tests.ConstSpec
