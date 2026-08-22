import Examples.Token

namespace Tests.TokenSpec

open Examples.Token
open ProofForge.Runtime

#guard (init 0).dummy == 0
#guard get (init 0) == 0
#guard balanceOf (init 0) 1 2 3 == 0
#guard allowanceOf (init 0) 1 2 3 4 5 6 == 0

#guard
  match mint (init 0) 1 2 3 9 with
  | .ok (_, ret) => ret == 9
  | .error _ => false

#guard
  match logXfer (init 0) 4 with
  | .ok (_, ret) => ret == 4
  | .error _ => false

#guard ProofForge.Evm.Keccak.keccak256HexOfString "Transfer(uint64)" !=
  ProofForge.Evm.Keccak.keccak256HexOfString "Approval(uint64)"

#guard
  match ProofForge.Evm.IR.fromProgram ProofForge.Golden.extractedToken with
  | .error _ => false
  | .ok p =>
      match ProofForge.Evm.Emit.emitYul p, ProofForge.Evm.Emit.emitAbi p with
      | .error _, _ => false
      | .ok yul, abi =>
          yul.contains "keccak256(0, 128)" &&
            yul.contains "keccak256(0, 224)" &&
            yul.contains "log1(0, 32, 0x" &&
            yul.contains "revert(0, 4)" &&
            abi.contains "\"type\":\"event\"" &&
            abi.contains "\"name\":\"Transfer\"" &&
            abi.contains "\"name\":\"Approval\""

#guard
  match ProofForge.Evm.IR.fromProgram ProofForge.Golden.extractedToken with
  | .error _ => false
  | .ok p =>
      (p.entries.find? (·.ixName == "transfer")).isSome &&
        (p.entries.find? (·.ixName == "transferFrom")).isSome &&
        (p.entries.find? (·.ixName == "approve")).isSome &&
        (p.entries.find? (·.ixName == "balanceOf")).map (·.view) == some true &&
        (p.entries.find? (·.ixName == "allowanceOf")).map (·.view) == some true

#guard
  match ProofForge.Emit.emitCounterAsm ProofForge.Golden.extractedToken with
  | .error reason => reason.contains "svm rejects evm leaf"
  | .ok _ => false

end Tests.TokenSpec
