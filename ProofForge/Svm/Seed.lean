namespace ProofForge.Svm.Seed.Ascii

/-- Solana's bounded static seed policy used by PDA and seed-derived System APIs. Seven-bit input
makes `String.length` equal the encoded byte length. -/
def wellFormed (seed : String) : Bool :=
  !seed.isEmpty && seed.length ≤ 32 && seed.toList.all (·.toNat < 128)

end ProofForge.Svm.Seed.Ascii
