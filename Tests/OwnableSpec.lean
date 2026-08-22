import Examples.Ownable

namespace Tests.OwnableSpec

open Examples.Ownable
open ProofForge.Runtime

#guard (init 1 2 3).owner0 == 1
#guard (init 1 2 3).owner1 == 2
#guard (init 1 2 3).owner2 == 3
#guard get (init 1 2 3) == 0
#guard ownerW0 (init 1 2 3) == 1
#guard allowance (init 1 2 3) 1 2 3 4 5 6 == 0

#guard
  match logInc (init 0 0 0) 9 with
  | .ok (_, ret) => ret == 9
  | .error _ => false

#guard
  match approve (init 0 0 0) 1 2 3 4 5 6 7 with
  | .ok (_, ret) => ret == 7
  | .error _ => false

#guard ProofForge.Evm.Keccak.keccak256HexOfString "Incremented(uint64)" !=
  ProofForge.Evm.Keccak.keccak256HexOfString "Tipped(uint64)"

#guard
  match ProofForge.Evm.IR.fromProgram ProofForge.Golden.extractedOwnable with
  | .error _ => false
  | .ok p =>
      match ProofForge.Evm.Emit.emitYul p with
      | .error _ => false
      | .ok yul =>
          yul.contains "keccak256(0, 224)" &&
            yul.contains "log1(0, 32, 0x" &&
            yul.contains "revert(0, 4)" &&
            yul.contains "eq(" &&
            yul.contains "sstore(0," &&
            yul.contains "sstore(1," &&
            yul.contains "sstore(2,"

#guard
  match ProofForge.Evm.IR.fromProgram ProofForge.Golden.extractedOwnable with
  | .error _ => false
  | .ok p =>
      (p.entries.find? (·.ixName == "bump")).isSome &&
        (p.entries.find? (·.ixName == "approve")).isSome &&
        (p.entries.find? (·.ixName == "allowance")).map (·.view) == some true &&
        (p.entries.find? (·.ixName == "logInc")).map (·.payable) == some false

#guard
  match ProofForge.Emit.emitCounterAsm ProofForge.Golden.extractedOwnable with
  | .error reason => reason.contains "svm rejects evm leaf"
  | .ok _ => false

end Tests.OwnableSpec
