import Examples.Vault

namespace Tests.VaultSpec

open Examples.Vault
open ProofForge.Evm.Runtime

#guard (init 0).dummy == 0
#guard get (init 0) == 0
#guard getU64 (init 0) 7 == 0
#guard shareOf (init 0) 1 2 3 == 0
#guard held (init 0) 1 2 3 == 0

#guard
  match setU64 (init 0) 7 9 with
  | .ok (st, ret) => st.dummy == 0 && ret == 9
  | .error _ => false

#guard
  match ProofForge.Evm.IR.fromProgram ProofForge.Golden.extractedVault with
  | .error _ => false
  | .ok p =>
      match ProofForge.Evm.Emit.emitYul p with
      | .error _ => false
      | .ok yul =>
          yul.contains "keccak256(0, 64)" &&
            yul.contains "keccak256(0, 128)" &&
            yul.contains "0xa9059cbb" &&
            yul.contains "0x70a08231" &&
            yul.contains "staticcall(gas()" &&
            yul.contains "returndatasize()"

#guard
  match ProofForge.Svm.Emit.emitCounterAsm ProofForge.Golden.extractedVault with
  | .error reason => reason.contains "svm rejects evm leaf"
  | .ok _ => false

end Tests.VaultSpec
