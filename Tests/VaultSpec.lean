import Examples.Vault

namespace Tests.VaultSpec

open Examples.Vault
open ProofForge.Evm.Runtime

def sample : Addr20 := ⟨1, 2, 3⟩

def zero256 : UInt256 := ⟨0, 0, 0, 0⟩

#guard (init 0).dummy == 0
#guard get (init 0) == 0
#guard getU64 (init 0) 7 == 0
#guard shareOf (init 0) sample == zero256
#guard held (init 0) sample == zero256
#guard allowed (init 0) sample sample sample == zero256

#guard
  match setU64 (init 0) 7 9 with
  | .ok (st, ret) => st.dummy == 0 && ret == 9
  | .error _ => false

#guard
  match grant (init 0) sample sample ⟨4, 0, 0, 0⟩ with
  | .ok (_, ret) => ret == 4
  | .error _ => false

#guard
  match wrap (init 0) sample ⟨5, 0, 0, 0⟩ with
  | .ok (_, ret) => ret == 5
  | .error _ => false

#guard
  match unwrap (init 0) sample ⟨6, 0, 0, 0⟩ with
  | .ok (_, ret) => ret == 6
  | .error _ => false

#guard
  match swap2 (init 0) sample sample sample ⟨8, 0, 0, 0⟩ ⟨1, 0, 0, 0⟩ with
  | .ok (_, ret) => ret == 8
  | .error _ => false

#guard
  match swap3 (init 0) sample sample sample sample ⟨9, 0, 0, 0⟩ ⟨1, 0, 0, 0⟩ with
  | .ok (_, ret) => ret == 9
  | .error _ => false

#guard
  match permit (init 0) sample sample sample ⟨10, 0, 0, 0⟩ ⟨11, 0, 0, 0⟩
      27 ⟨1, 2, 3, 4⟩ ⟨5, 6, 7, 8⟩ with
  | .ok (_, ret) => ret == 10
  | .error _ => false

#guard
  match receive (init 0) with
  | .ok (_, ret) => ret == 0
  | .error _ => false

#guard
  let p := ProofForge.Evm.Golden.extractedVault
  match ProofForge.Evm.Emit.emitYul p with
  | .error _ => false
  | .ok yul =>
      yul.contains "keccak256(0, 64)" &&
        yul.contains "keccak256(0, 128)" &&
        yul.contains "0xa9059cbb" &&
        yul.contains "0x095ea7b3" &&
        yul.contains "0x23b872dd" &&
        yul.contains "0xdd62ed3e" &&
        yul.contains "0x70a08231" &&
        yul.contains "0xd0e30db0" &&
        yul.contains "0x2e1a7d4d" &&
        yul.contains "0x38ed1739" &&
        yul.contains "0xd505accf" &&
        yul.contains "mstore(164, 3)" &&
        yul.contains "call(gas(), " &&
        yul.contains "staticcall(gas()" &&
        yul.contains "returndatasize()"

#guard
  match ProofForge.Svm.Emit.emitCounterAsm ProofForge.Golden.extractedVault with
  | .error reason => reason.contains "svm rejects evm leaf"
  | .ok _ => false

end Tests.VaultSpec
