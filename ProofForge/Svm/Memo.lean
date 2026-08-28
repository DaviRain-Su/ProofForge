namespace ProofForge.Svm.Memo.Ascii

/-- ProofForge's static Memo payload budget. It stays below the shared 1,024-byte CPI scratch
budget after instruction/account descriptors are included. -/
def maxBytes : Nat := 512

/-- Bounded seven-bit payload policy. Seven-bit input makes `String.length` the encoded byte
length; runtime UTF-8 encoding and dynamic byte buffers remain outside this contract. -/
def wellFormed (value : String) : Bool :=
  value.length ≤ maxBytes && value.toList.all (·.toNat < 128)

end ProofForge.Svm.Memo.Ascii
