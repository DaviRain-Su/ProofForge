import Examples.Evm.Capped

namespace Tests.CappedSpec

open Examples.Evm.Capped
open ProofForge.Evm.Runtime

def sample : Addr20 := ⟨1, 2, 3⟩
def nine : UInt256 := ⟨9, 0, 0, 0⟩
def zero256 : UInt256 := ⟨0, 0, 0, 0⟩

#guard (init sample).paused == 0
#guard (init sample).cap == ⟨100, 0, 0, 0⟩
#guard (init sample).supply == zero256
#guard pausedOf (init sample) == 0
#guard capOf (init sample) == ⟨100, 0, 0, 0⟩
#guard totalSupply (init sample) == zero256
#guard ownerOf (init sample) == ⟨0, 0, 0⟩

#guard
  match mint (init sample) nine with
  | .ok _ => true
  | .error _ => false

#guard
  match pause (init sample) with
  | .ok (st, ret) => ret == 1 && st.paused == 1 && pausedOf st == 1
  | .error _ => false

#guard
  match unpause (init sample) with
  | .ok (st, ret) => ret == 0 && st.paused == 0
  | .error _ => false

#guard
  let p := ProofForge.Evm.Golden.extractedCapped
  match ProofForge.Evm.Emit.emitYul p, ProofForge.Evm.Emit.emitAbi p with
  | .error _, _ => false
  | .ok yul, abi =>
      yul.contains "setimmutable" &&
        yul.contains "loadimmutable" &&
        yul.contains "immAddr" &&
        yul.contains "revert(0, 4)" &&
        yul.contains "revert(0, 36)" &&
        abi.contains "\"name\":\"Unauthorized\"" &&
        abi.contains "\"name\":\"Paused\"" &&
        abi.contains "\"name\":\"CapExceeded\"" &&
        abi.contains "\"name\":\"mint\"" &&
        abi.contains "\"name\":\"pause\"" &&
        abi.contains "\"name\":\"capOf\""

#guard
  let p := ProofForge.Evm.Golden.extractedCapped
  (p.entries.find? (·.ixName == "mint")).isSome &&
    (p.entries.find? (·.ixName == "pause")).isSome &&
    (p.entries.find? (·.ixName == "unpause")).isSome &&
    (p.entries.find? (·.ixName == "pausedOf")).map (·.view) == some true &&
    (p.entries.find? (·.ixName == "pausedOf")).map (·.retWidths) == some #[1] &&
    (p.entries.find? (·.ixName == "capOf")).map (·.view) == some true &&
    (p.entries.find? (·.ixName == "capOf")).map (·.retWidths) == some #[32] &&
    (p.entries.find? (·.ixName == "totalSupply")).map (·.view) == some true &&
    (p.entries.find? (·.ixName == "totalSupply")).map (·.retWidths) == some #[32] &&
    (p.entries.find? (·.ixName == "ownerOf")).map (·.view) == some true &&
    (p.entries.find? (·.ixName == "ownerOf")).map (·.retWidths) == some #[20]

#guard
  match ProofForge.Svm.Emit.emitCounterAsm ProofForge.Golden.extractedEvmCtx with
  | .error reason => reason.contains "svm rejects evm leaf"
  | .ok _ => false

end Tests.CappedSpec
