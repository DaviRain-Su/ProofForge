import ProofForge.Attr
import ProofForge.Svm.Sdk.Account

/-!
# SVM SDK fixed public keys

A Solana public key is represented by four little-endian UInt64 words. The value is compiler data:
`pf_inline` consumers erase it to the existing checked account-key or account-owner word queries.
There is no base58 decoder, heap buffer, byte array, pointer, new Runtime operation, or emitter
recipe on chain.
-/

namespace ProofForge.Svm.Sdk

/-- One fixed 32-byte Solana public key in account-memory word order. -/
structure Pubkey where
  word0 : UInt64
  word1 : UInt64
  word2 : UInt64
  word3 : UInt64
  deriving BEq, Repr, Inhabited

attribute [pf_inline] Pubkey.word0 Pubkey.word1 Pubkey.word2 Pubkey.word3

@[pf_inline] def Pubkey.ofWords
    (word0 word1 word2 word3 : UInt64) : Pubkey :=
  { word0, word1, word2, word3 }

@[pf_inline] def Pubkey.equals (lhs rhs : Pubkey) : Bool :=
  match lhs, rhs with
  | ⟨lhs0, lhs1, lhs2, lhs3⟩, ⟨rhs0, rhs1, rhs2, rhs3⟩ =>
      lhs0 = rhs0 && lhs1 = rhs1 && lhs2 = rhs2 && lhs3 = rhs3

/-- Compare a fixed key with the complete 32-byte key of one statically selected account. -/
@[pf_inline] def Pubkey.matchesKey (key : Pubkey) (account : Account.Handle) : Bool :=
  match key with
  | ⟨word0, word1, word2, word3⟩ =>
      account.keyWord 0 = word0 && account.keyWord 1 = word1 &&
        account.keyWord 2 = word2 && account.keyWord 3 = word3

/-- Compare a fixed key with the complete 32-byte owner of one statically selected account. -/
@[pf_inline] def Pubkey.matchesOwner (key : Pubkey) (account : Account.Handle) : Bool :=
  match key with
  | ⟨word0, word1, word2, word3⟩ =>
      account.ownerWord 0 = word0 && account.ownerWord 1 = word1 &&
        account.ownerWord 2 = word2 && account.ownerWord 3 = word3

/-- Compare the complete keys of two statically selected accounts without copying either key. -/
@[pf_inline] def Account.Handle.sameKey (lhs rhs : Account.Handle) : Bool :=
  lhs.keyWord 0 = rhs.keyWord 0 && lhs.keyWord 1 = rhs.keyWord 1 &&
    lhs.keyWord 2 = rhs.keyWord 2 && lhs.keyWord 3 = rhs.keyWord 3

/-- Compare an account's complete owner with another account's complete key. -/
@[pf_inline] def Account.Handle.ownerIsKeyOf
    (account program : Account.Handle) : Bool :=
  account.ownerWord 0 = program.keyWord 0 && account.ownerWord 1 = program.keyWord 1 &&
    account.ownerWord 2 = program.keyWord 2 && account.ownerWord 3 = program.keyWord 3

end ProofForge.Svm.Sdk
