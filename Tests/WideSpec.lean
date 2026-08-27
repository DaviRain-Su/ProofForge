import Examples.Wide

namespace Tests.WideSpec

open Examples.Wide
open ProofForge.Evm.Runtime
open ProofForge.Core.Value

def one : UInt256 := ⟨1, 0, 0, 0⟩
def one128 : UInt128 := ⟨1, 2⟩
def bytes12 : FixedBytes 12 := ⟨0x0706050403020100, 0x0b0a0908, 0, 0⟩

#guard (init 0).dummy == 0
#guard get (init 0) == 0
#guard echo (init 0) one == one
#guard echo128 (init 0) one128 == one128
#guard echoBytes12 (init 0) bytes12 == bytes12

-- Host stub does not model overflow; `evmAdd256 a b` returns `a`.
#guard add (init 0) one ⟨2, 0, 0, 0⟩ == one

#guard
  match ProofForge.Svm.Emit.emitCounterAsm ProofForge.Golden.extractedEvmCtx with
  | .error reason => reason.contains "svm rejects evm leaf"
  | .ok _ => false

end Tests.WideSpec
