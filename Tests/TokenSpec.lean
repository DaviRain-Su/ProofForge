import Examples.Token

namespace Tests.TokenSpec

open Examples.Token
open ProofForge.Evm.Runtime

def sample : Addr20 := ⟨1, 2, 3⟩
def nobody : Addr20 := ⟨0, 0, 0⟩

def nine : UInt256 := ⟨9, 0, 0, 0⟩
def zero256 : UInt256 := ⟨0, 0, 0, 0⟩

#guard (init 0).dummy == 0
#guard (init 0).supply == zero256
#guard get (init 0) == 0
#guard balanceOf (init 0) sample == zero256
#guard totalSupply (init 0) == zero256
#guard decimals (init 0) == 18
#guard name (init 0) == ⟨0x546f6b656e, 0, 0, 0⟩
#guard symbol (init 0) == ⟨0x5046, 0, 0, 0⟩
#guard allowanceOf (init 0) sample ⟨4, 5, 6⟩ == zero256

#guard
  match mint (init 0) sample nine with
  | .ok _ => true
  | .error _ => false

#guard
  match mint (init 0) nobody nine with
  | .ok _ => true
  | .error _ => false

#guard
  match burn (init 0) nine with
  | .ok (_, ret) => ret == 9
  | .error _ => false

#guard
  match burnFrom (init 0) sample nine with
  | .ok _ => true
  | .error _ => false

#guard
  match increaseAllowance (init 0) sample nine with
  | .ok _ => true
  | .error _ => false

#guard
  match decreaseAllowance (init 0) sample nine with
  | .ok _ => true
  | .error _ => false

#guard nonceOf (init 0) sample == zero256
#guard DOMAIN_SEPARATOR (init 0) == ⟨0, 0, 0, 0⟩

#guard
  match permit (init 0) sample sample nine nine 27 ⟨1, 0, 0, 0⟩ ⟨2, 0, 0, 0⟩ with
  | .ok (_, ret) => ret == 9
  | .error _ => false

#guard
  match logXfer (init 0) 4 with
  | .ok (_, ret) => ret == 4
  | .error _ => false

#guard ProofForge.Evm.Keccak.keccak256HexOfString "Transfer(uint64)" !=
  ProofForge.Evm.Keccak.keccak256HexOfString "Approval(uint64)"

#guard ProofForge.Evm.Keccak.keccak256HexOfString "Transfer(address,address,uint256)" !=
  ProofForge.Evm.Keccak.keccak256HexOfString "Transfer(uint64)"

#guard
  let p := ProofForge.Evm.Golden.extractedToken
  match ProofForge.Evm.Emit.emitYul p, ProofForge.Evm.Emit.emitAbi p with
  | .error _, _ => false
  | .ok yul, abi =>
      yul.contains "function pf_store_addr20(off, w0, w1, w2)" &&
        yul.contains "pf_store_addr20(0," &&
        !yul.contains "mstore8(12," &&
        yul.contains "keccak256(0, 128)" &&
        yul.contains "keccak256(0, 224)" &&
        yul.contains "log1(0, 32, 0x" &&
        yul.contains "log3(0, 32, 0x" &&
        yul.contains "revert(0, 68)" &&
        abi.contains "\"type\":\"event\"" &&
        abi.contains "\"name\":\"Transfer\"" &&
        abi.contains "\"name\":\"Approval\"" &&
        abi.contains "\"name\":\"Insufficient\"" &&
        abi.contains "\"name\":\"Expired\"" &&
        abi.contains "\"name\":\"Unauthorized\"" &&
        abi.contains "\"name\":\"ZeroAddress\"" &&
        abi.contains "\"type\":\"error\"" &&
        yul.contains "revert(0, 36)" &&
        yul.contains "staticcall(gas(), 1," &&
        yul.contains "0x1901" &&
        yul.contains "keccak256(0, 160)" &&
        abi.contains "\"name\":\"DOMAIN_SEPARATOR\"" &&
        abi.contains "\"type\":\"bytes32\"" &&
        abi.contains "\"name\":\"decimals\"" &&
        abi.contains "\"type\":\"uint8\"" &&
        abi.contains "\"name\":\"name\"" &&
        abi.contains "\"name\":\"symbol\"" &&
        abi.contains "\"type\":\"bytes32\""

#guard
  let p := ProofForge.Evm.Golden.extractedToken
  (p.entries.find? (·.ixName == "transfer")).isSome &&
    (p.entries.find? (·.ixName == "transferFrom")).isSome &&
    (p.entries.find? (·.ixName == "approve")).isSome &&
    (p.entries.find? (·.ixName == "burn")).isSome &&
    (p.entries.find? (·.ixName == "burnFrom")).isSome &&
    (p.entries.find? (·.ixName == "increaseAllowance")).isSome &&
    (p.entries.find? (·.ixName == "decreaseAllowance")).isSome &&
    (p.entries.find? (·.ixName == "balanceOf")).map (·.view) == some true &&
    (p.entries.find? (·.ixName == "allowanceOf")).map (·.view) == some true &&
    (p.entries.find? (·.ixName == "DOMAIN_SEPARATOR")).map (·.view) == some true &&
    (p.entries.find? (·.ixName == "DOMAIN_SEPARATOR")).map (·.retWidths) == some #[33] &&
    (p.entries.find? (·.ixName == "totalSupply")).map (·.view) == some true &&
    (p.entries.find? (·.ixName == "totalSupply")).map (·.retWidths) == some #[32] &&
    (p.entries.find? (·.ixName == "decimals")).map (·.view) == some true &&
    (p.entries.find? (·.ixName == "decimals")).map (·.retWidths) == some #[1] &&
    (p.entries.find? (·.ixName == "name")).map (·.view) == some true &&
    (p.entries.find? (·.ixName == "name")).map (·.retWidths) == some #[33] &&
    (p.entries.find? (·.ixName == "symbol")).map (·.view) == some true &&
    (p.entries.find? (·.ixName == "symbol")).map (·.retWidths) == some #[33]

#guard
  match ProofForge.Svm.Emit.emitCounterAsm ProofForge.Golden.extractedToken with
  | .error reason => reason.contains "svm rejects evm leaf"
  | .ok _ => false

end Tests.TokenSpec
