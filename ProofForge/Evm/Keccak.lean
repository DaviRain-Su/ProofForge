import ProofForge.Crypto.Keccak
import ProofForge.Evm.Codec

/-!
本机 Keccak-256 在 `ProofForge.Crypto.Keccak`。
这个模块只保留旧名。
-/
namespace ProofForge.Evm.Keccak

def keccak256 (input : ByteArray) : ByteArray :=
  ProofForge.Crypto.Keccak.keccak256 input

def keccak256Hex (input : ByteArray) : String :=
  ProofForge.Crypto.Keccak.keccak256Hex input

def keccak256HexOfString (s : String) : String :=
  ProofForge.Crypto.Keccak.keccak256HexOfString s

def signature (name : String) (paramTypes : Array String) : String :=
  ProofForge.Crypto.Keccak.signature name paramTypes

def selector (name : String) (paramTypes : Array String) : String :=
  ProofForge.Crypto.Keccak.selector name paramTypes

def selectorU64 (name : String) (paramCount : Nat) : String :=
  ProofForge.Crypto.Keccak.selectorU64 name paramCount

def abiTypeOfWidth (width : Nat) : String :=
  match Codec.scalarOfLegacyWidth width with
  | .ok type => (Codec.abiType type).toOption.getD "uint64"
  | .error _ => "uint64"

def selectorOfWidths (name : String) (widths : Array Nat) : String :=
  if widths.isEmpty then selector name #[] else selector name (widths.map abiTypeOfWidth)

end ProofForge.Evm.Keccak
