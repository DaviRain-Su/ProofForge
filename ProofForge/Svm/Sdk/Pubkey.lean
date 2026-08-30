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
@[pf_boundary] structure Pubkey where
  word0 : UInt64
  word1 : UInt64
  word2 : UInt64
  word3 : UInt64
  deriving BEq, Repr, Inhabited

attribute [pf_inline] Pubkey.word0 Pubkey.word1 Pubkey.word2 Pubkey.word3

@[pf_inline] def Pubkey.ofWords
    (word0 word1 word2 word3 : UInt64) : Pubkey :=
  { word0, word1, word2, word3 }

/-- Complete-key equality over all four words. The body uses the `pf_inline` word
projections directly so extraction erases it to four scalar comparisons; a two-discriminant
`match` would compile to a matcher that extraction deliberately does not iota-reduce. -/
@[pf_inline] def Pubkey.equals (lhs rhs : Pubkey) : Bool :=
  lhs.word0 = rhs.word0 && lhs.word1 = rhs.word1 &&
    lhs.word2 = rhs.word2 && lhs.word3 = rhs.word3

/-- Complete-key inequality: the negation of `Pubkey.equals` over all four words. -/
@[pf_inline] def Pubkey.notEquals (lhs rhs : Pubkey) : Bool :=
  !(lhs.equals rhs)

/-- Project the complete 32-byte key of one statically selected account as a first-class
Pubkey value. The value stays compiler data: `pf_inline` consumers erase it back to the four
existing key-word queries; nothing is copied on chain. -/
@[pf_inline] def Account.Handle.key (account : Account.Handle) : Pubkey :=
  Pubkey.ofWords (account.keyWord 0) (account.keyWord 1)
    (account.keyWord 2) (account.keyWord 3)

/-- Project the complete 32-byte owner of one statically selected account as a Pubkey value. -/
@[pf_inline] def Account.Handle.owner (account : Account.Handle) : Pubkey :=
  Pubkey.ofWords (account.ownerWord 0) (account.ownerWord 1)
    (account.ownerWord 2) (account.ownerWord 3)

/-- Compare any first-class key value with the complete 32-byte key of one statically selected
account. Direct projections keep both fixed and boundary-supplied values compiler-erased. -/
@[pf_inline] def Pubkey.matchesKey (key : Pubkey) (account : Account.Handle) : Bool :=
  account.keyWord 0 = key.word0 && account.keyWord 1 = key.word1 &&
    account.keyWord 2 = key.word2 && account.keyWord 3 = key.word3

/-- Compare any first-class key value with the complete 32-byte owner of one statically selected
account. -/
@[pf_inline] def Pubkey.matchesOwner (key : Pubkey) (account : Account.Handle) : Bool :=
  account.ownerWord 0 = key.word0 && account.ownerWord 1 = key.word1 &&
    account.ownerWord 2 = key.word2 && account.ownerWord 3 = key.word3

/-- Compare the complete keys of two statically selected accounts by projecting both as
Pubkey values and comparing the values; neither key is copied. -/
@[pf_inline] def Account.Handle.sameKey (lhs rhs : Account.Handle) : Bool :=
  lhs.key.equals rhs.key

/-- Compare an account's complete owner with another account's complete key. -/
@[pf_inline] def Account.Handle.ownerIsKeyOf
    (account program : Account.Handle) : Bool :=
  account.owner.equals program.key


section Proofs

/-- **Pubkey.equals 的反身性**：同一个 key 与自身比较为 true。 -/
theorem pubkey_equals_refl (key : Pubkey) : Pubkey.equals key key = true := by
  unfold Pubkey.equals
  simp

/-- **Pubkey.equals 的对称性**。 -/
theorem pubkey_equals_symm (lhs rhs : Pubkey) (h : Pubkey.equals lhs rhs = true) :
    Pubkey.equals rhs lhs = true := by
  cases lhs with
  | mk l0 l1 l2 l3 =>
    cases rhs with
    | mk r0 r1 r2 r3 =>
      simp only [Pubkey.equals, Bool.and_eq_true, decide_eq_true_iff] at h ⊢
      obtain ⟨⟨⟨h0, h1⟩, h2⟩, h3⟩ := h
      exact ⟨⟨⟨h0.symm, h1.symm⟩, h2.symm⟩, h3.symm⟩

/-- **Pubkey.notEquals 与 equals 互补**：不等恰为相等的否定。 -/
theorem pubkey_notEquals_iff (lhs rhs : Pubkey) :
    Pubkey.notEquals lhs rhs = true ↔ Pubkey.equals lhs rhs = false := by
  unfold Pubkey.notEquals
  cases Pubkey.equals lhs rhs <;> simp

end Proofs

end ProofForge.Svm.Sdk
