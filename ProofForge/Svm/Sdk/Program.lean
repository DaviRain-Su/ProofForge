import ProofForge.Svm.Sdk.Pubkey

/-!
# SVM SDK canonical program identities

These constants are the decoded 32-byte identities published by the official Solana/SPL interface
crates. Contracts compare account bytes directly; base58 remains a compiler/client concern.
`Id.matches` also requires the selected account to be executable, and `Id.owns` authenticates both
the executable program account and a state account's complete owner field.
-/

namespace ProofForge.Svm.Sdk.Program

structure Id where
  key : Pubkey
  deriving BEq, Repr, Inhabited

attribute [pf_inline] Id.key

@[pf_inline] def Id.ofWords
    (word0 word1 word2 word3 : UInt64) : Id :=
  { key := Pubkey.ofWords word0 word1 word2 word3 }

/-- `11111111111111111111111111111111`. -/
@[pf_inline] def system : Id := Id.ofWords 0 0 0 0

/-- `TokenkegQfeZyiNwAJbNbGKPFXCWuBvf9Ss623VQ5DA`. -/
@[pf_inline] def classicToken : Id :=
  Id.ofWords 10637895772709248262 12428223917890587609
    10463932726783620124 12178014311288245306

/-- `TokenzQdBNbLqP5VEhdkAS6EPFLC1PHnBqCXEpPxuEb`. -/
@[pf_inline] def token2022 : Id :=
  Id.ofWords 16037166466943343878 15766377600162546200
    2814109315776649910 18197816669093084670

/-- `ATokenGPvbdGVxr1b2hvZbsiqW5xWH25efTNsLJA8knL`. -/
@[pf_inline] def associatedToken : Id :=
  Id.ofWords 17404482154777646988 9443360210905218491
    9516387326969993739 6483188794038914564

/-- Current Memo v4: `Memo4c2pN8afCj432Lb7RMVKi9PbQnnW7ewFFaV3oAH`. -/
@[pf_inline] def memoV4 : Id :=
  Id.ofWords 15117832056309238277 1726465464192650243
    13549895254235327634 13996149263823438487

/-- Compatibility Memo v3: `MemoSq4gqABAXKb96qnH8TysNcWxMyWCqXgDLGmfcHr`. -/
@[pf_inline] def memoV3 : Id :=
  Id.ofWords 441679977081162245 8951144367161615437
    9348226791408743804 10179266835579936740

/-- Authenticate one statically selected executable account against this complete program id. -/
@[pf_inline] def Id.matches (id : Id) (program : Account.Handle) : Bool :=
  match id with
  | ⟨key⟩ => program.isExecutable = 1 && key.matchesKey program

/-- UInt64 form for protocols whose existing gates encode validity as `0` / `1`. -/
@[pf_inline] def Id.validWord (id : Id) (program : Account.Handle) : UInt64 :=
  match id with
  | ⟨key⟩ =>
      if program.isExecutable = 1 && key.matchesKey program then 1 else 0

/-- Authenticate `program`, then require `account.owner == program.key == id`. -/
@[pf_inline] def Id.owns
    (id : Id) (program account : Account.Handle) : Bool :=
  match id with
  | ⟨key⟩ =>
      program.isExecutable = 1 && key.matchesKey program && account.ownerIsKeyOf program

/-- Official helper parity: either SPL Token program id is accepted, but no other executable. -/
@[pf_inline] def isSplToken (program : Account.Handle) : Bool :=
  classicToken.matches program || token2022.matches program

end ProofForge.Svm.Sdk.Program
