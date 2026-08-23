import ProofForge.Crypto.Sha256

/-!
本机 SHA-256 在 `ProofForge.Crypto.Sha256`。
这个兼容模块只保留旧名。
-/
namespace ProofForge.Sha256

def digestBytes (s : String) : Array UInt8 :=
  ProofForge.Crypto.Sha256.digestBytes s

def digestHex (s : String) : String :=
  ProofForge.Crypto.Sha256.digestHex s

def first8Le (s : String) : UInt64 :=
  ProofForge.Crypto.Sha256.first8Le s

def first8Be (s : String) : UInt64 :=
  ProofForge.Crypto.Sha256.first8Be s

end ProofForge.Sha256
