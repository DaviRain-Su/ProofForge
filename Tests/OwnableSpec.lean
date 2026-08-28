import ProofForge
import Examples.Ownable

namespace Tests.OwnableSpec

open Examples.Ownable
open ProofForge.Evm.Sdk

def sample : Address := ⟨1, 2, 3⟩
def zero256 : UInt256 := ⟨0, 0, 0, 0⟩

#guard (init sample).value == 0
#guard get (init sample) == 0
#guard ownerOf (init sample) == ⟨0, 0, 0⟩
#guard allowance (init sample) sample ⟨4, 5, 6⟩ == zero256

#guard
  match logInc (init ⟨0, 0, 0⟩) 9 with
  | .ok (_, ret) => ret == 9
  | .error _ => false

#guard
  match approve (init ⟨0, 0, 0⟩) ⟨1, 2, 3⟩ ⟨4, 5, 6⟩ ⟨7, 0, 0, 0⟩ with
  | .ok (_, ret) => ret == 7
  | .error _ => false

#guard ProofForge.Evm.Keccak.keccak256HexOfString "Incremented(uint64)" !=
  ProofForge.Evm.Keccak.keccak256HexOfString "Tipped(uint64)"

#guard
  let p := ProofForge.Evm.Golden.extractedOwnable
  match ProofForge.Evm.Emit.emitYul p with
  | .error _ => false
  | .ok yul =>
      yul.contains "keccak256(0, 224)" &&
        yul.contains "log1(0, 32, 0x" &&
        yul.contains "revert(0, 36)" &&
        yul.contains "eq(" &&
        yul.contains "setimmutable" &&
        yul.contains "loadimmutable" &&
        yul.contains "immAddr" &&
        yul.contains "sstore(0,"

#guard
  let p := ProofForge.Evm.Golden.extractedOwnable
  (p.entries.find? (·.ixName == "bump")).isSome &&
    (p.entries.find? (·.ixName == "approve")).isSome &&
    (p.entries.find? (·.ixName == "allowance")).map (·.view) == some true &&
    (p.entries.find? (·.ixName == "logInc")).map (·.payable) == some false

#guard
  match ProofForge.Svm.Emit.emitCounterAsm ProofForge.Golden.extractedOwnable with
  | .error reason => reason.contains "svm rejects evm leaf"
  | .ok _ => false

end Tests.OwnableSpec
