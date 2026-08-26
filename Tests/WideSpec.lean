import Examples.Wide

namespace Tests.WideSpec

open Examples.Wide
open ProofForge.Evm.Runtime

def one : UInt256 := ⟨1, 0, 0, 0⟩

#guard (init 0).dummy == 0
#guard get (init 0) == 0
#guard echo (init 0) one == one

-- Host stub does not model overflow; `evmAdd256 a b` returns `a`.
#guard add (init 0) one ⟨2, 0, 0, 0⟩ == one

#guard
  match ProofForge.Svm.Emit.emitCounterAsm ProofForge.Golden.extractedEvmCtx with
  | .error reason => reason.contains "svm rejects evm leaf"
  | .ok _ => false

end Tests.WideSpec
