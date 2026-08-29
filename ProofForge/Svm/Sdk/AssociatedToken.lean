import ProofForge.Attr
import ProofForge.Svm.Sdk.Account

/-!
# SVM SDK Associated Token Account facade

Role-typed, compiler-erased plans for the three official Associated Token Account instructions.
They lower through generic `Runtime.invoke`; applications do not repeat instruction tags or
positional account metas, and the target does not gain an ATA-specific operation or emitter recipe.

The Token program is always an explicit account role, so a transaction may select either classic
Token or Token-2022. The selected ATA program owns canonical derived-address validation. Target
account privilege and executable checks remain in force; canonical program-id authentication is a
separate future SDK policy rather than a hidden default.

This is a compiler-erased fixed geometry, not a runtime account list or persistent allocation.
Derived-address helpers and runtime-selected account geometry remain fail closed.
-/

namespace ProofForge.Svm.Sdk.AssociatedToken

/-- Account roles shared by ordinary and idempotent creation. Every handle is relative to the
external-account region after state. -/
structure CreateAccounts where
  associatedTokenProgram : CpiAccount.Handle
  payer : CpiAccount.Handle
  associatedAccount : CpiAccount.Handle
  wallet : CpiAccount.Handle
  mint : CpiAccount.Handle
  systemProgram : CpiAccount.Handle
  tokenProgram : CpiAccount.Handle
  deriving BEq, Repr, Inhabited

attribute [pf_inline]
  CreateAccounts.associatedTokenProgram CreateAccounts.payer CreateAccounts.associatedAccount
  CreateAccounts.wallet CreateAccounts.mint CreateAccounts.systemProgram CreateAccounts.tokenProgram

/-- Name statically selected creation accounts without exposing CPI meta flags. -/
@[pf_inline] def CreateAccounts.at
    (associatedTokenProgram payer associatedAccount wallet mint systemProgram tokenProgram : Nat) :
    CreateAccounts :=
  { associatedTokenProgram := .at associatedTokenProgram
    payer := .at payer
    associatedAccount := .at associatedAccount
    wallet := .at wallet
    mint := .at mint
    systemProgram := .at systemProgram
    tokenProgram := .at tokenProgram }

def CreateAccounts.wellFormed (accounts : CreateAccounts) (accountLimit : Nat := 64) : Bool :=
  accounts.associatedTokenProgram.wellFormed accountLimit &&
    accounts.payer.wellFormed accountLimit &&
    accounts.associatedAccount.wellFormed accountLimit &&
    accounts.wallet.wellFormed accountLimit &&
    accounts.mint.wellFormed accountLimit &&
    accounts.systemProgram.wellFormed accountLimit &&
    accounts.tokenProgram.wellFormed accountLimit

/-- Existing fixed creation geometry: payer s+w / ATA w / wallet / mint / System / selected Token,
with the Associated Token Account program as callee account 6. -/
@[pf_inline] def fixedCreateAccounts : CreateAccounts :=
  CreateAccounts.at 6 0 1 2 3 4 5

/-- Create an ATA and fail if that canonical account is already initialized. -/
@[pf_inline] def createWith (accounts : CreateAccounts) : UInt64 :=
  ProofForge.Svm.Runtime.invoke (UInt64.ofNat accounts.associatedTokenProgram.index)
    #[{ acc := UInt64.ofNat accounts.payer.index, signer := true, writable := true },
      { acc := UInt64.ofNat accounts.associatedAccount.index, writable := true },
      { acc := UInt64.ofNat accounts.wallet.index },
      { acc := UInt64.ofNat accounts.mint.index },
      { acc := UInt64.ofNat accounts.systemProgram.index },
      { acc := UInt64.ofNat accounts.tokenProgram.index }]
    #[.u8le 0]

/-- Create an ATA if absent and accept an already initialized canonical account. -/
@[pf_inline] def createIdempotentWith (accounts : CreateAccounts) : UInt64 :=
  ProofForge.Svm.Runtime.invoke (UInt64.ofNat accounts.associatedTokenProgram.index)
    #[{ acc := UInt64.ofNat accounts.payer.index, signer := true, writable := true },
      { acc := UInt64.ofNat accounts.associatedAccount.index, writable := true },
      { acc := UInt64.ofNat accounts.wallet.index },
      { acc := UInt64.ofNat accounts.mint.index },
      { acc := UInt64.ofNat accounts.systemProgram.index },
      { acc := UInt64.ofNat accounts.tokenProgram.index }]
    #[.u8le 1]

/-- Fixed-account ordinary Create. -/
@[pf_inline] def create : UInt64 :=
  ProofForge.Svm.Runtime.invoke 6
    #[{ acc := 0, signer := true, writable := true },
      { acc := 1, writable := true },
      { acc := 2 },
      { acc := 3 },
      { acc := 4 },
      { acc := 5 }]
    #[.u8le 0]

/-- Fixed-account idempotent Create retained as the source-compatible default. -/
@[pf_inline] def createIdempotent : UInt64 :=
  ProofForge.Svm.Runtime.invoke 6
    #[{ acc := 0, signer := true, writable := true },
      { acc := 1, writable := true },
      { acc := 2 },
      { acc := 3 },
      { acc := 4 },
      { acc := 5 }]
    #[.u8le 1]

/-- Official RecoverNested roles. The wallet is signer+writable because it receives the closed
nested account's lamports. Every handle is CPI-relative. -/
structure RecoverNestedAccounts where
  associatedTokenProgram : CpiAccount.Handle
  nestedAssociatedAccount : CpiAccount.Handle
  nestedMint : CpiAccount.Handle
  destinationAssociatedAccount : CpiAccount.Handle
  ownerAssociatedAccount : CpiAccount.Handle
  ownerMint : CpiAccount.Handle
  wallet : CpiAccount.Handle
  tokenProgram : CpiAccount.Handle
  deriving BEq, Repr, Inhabited

attribute [pf_inline]
  RecoverNestedAccounts.associatedTokenProgram RecoverNestedAccounts.nestedAssociatedAccount
  RecoverNestedAccounts.nestedMint RecoverNestedAccounts.destinationAssociatedAccount
  RecoverNestedAccounts.ownerAssociatedAccount RecoverNestedAccounts.ownerMint
  RecoverNestedAccounts.wallet RecoverNestedAccounts.tokenProgram

/-- Name statically selected RecoverNested accounts without exposing its seven account metas. -/
@[pf_inline] def RecoverNestedAccounts.at
    (associatedTokenProgram nestedAssociatedAccount nestedMint destinationAssociatedAccount
      ownerAssociatedAccount ownerMint wallet tokenProgram : Nat) : RecoverNestedAccounts :=
  { associatedTokenProgram := .at associatedTokenProgram
    nestedAssociatedAccount := .at nestedAssociatedAccount
    nestedMint := .at nestedMint
    destinationAssociatedAccount := .at destinationAssociatedAccount
    ownerAssociatedAccount := .at ownerAssociatedAccount
    ownerMint := .at ownerMint
    wallet := .at wallet
    tokenProgram := .at tokenProgram }

def RecoverNestedAccounts.wellFormed
    (accounts : RecoverNestedAccounts) (accountLimit : Nat := 64) : Bool :=
  accounts.associatedTokenProgram.wellFormed accountLimit &&
    accounts.nestedAssociatedAccount.wellFormed accountLimit &&
    accounts.nestedMint.wellFormed accountLimit &&
    accounts.destinationAssociatedAccount.wellFormed accountLimit &&
    accounts.ownerAssociatedAccount.wellFormed accountLimit &&
    accounts.ownerMint.wellFormed accountLimit &&
    accounts.wallet.wellFormed accountLimit &&
    accounts.tokenProgram.wellFormed accountLimit

/-- Existing fixed RecoverNested geometry: nested ATA w / nested mint / destination ATA w /
owner ATA / owner mint / wallet s+w / selected Token, with the ATA program as callee account 7. -/
@[pf_inline] def fixedRecoverNestedAccounts : RecoverNestedAccounts :=
  RecoverNestedAccounts.at 7 0 1 2 3 4 5 6

/-- Recover every token and the rent lamports from a nested ATA using statically named roles. -/
@[pf_inline] def recoverNestedWith (accounts : RecoverNestedAccounts) : UInt64 :=
  ProofForge.Svm.Runtime.invoke (UInt64.ofNat accounts.associatedTokenProgram.index)
    #[{ acc := UInt64.ofNat accounts.nestedAssociatedAccount.index, writable := true },
      { acc := UInt64.ofNat accounts.nestedMint.index },
      { acc := UInt64.ofNat accounts.destinationAssociatedAccount.index, writable := true },
      { acc := UInt64.ofNat accounts.ownerAssociatedAccount.index },
      { acc := UInt64.ofNat accounts.ownerMint.index },
      { acc := UInt64.ofNat accounts.wallet.index, signer := true, writable := true },
      { acc := UInt64.ofNat accounts.tokenProgram.index }]
    #[.u8le 2]

/-- Fixed-account RecoverNested. -/
@[pf_inline] def recoverNested : UInt64 :=
  ProofForge.Svm.Runtime.invoke 7
    #[{ acc := 0, writable := true },
      { acc := 1 },
      { acc := 2, writable := true },
      { acc := 3 },
      { acc := 4 },
      { acc := 5, signer := true, writable := true },
      { acc := 6 }]
    #[.u8le 2]

section Proofs

theorem createAccounts_wf_parts (accounts : CreateAccounts) (L : Nat)
    (h : accounts.wellFormed L = true) :
    accounts.associatedTokenProgram.index + 1 < L ∧ accounts.payer.index + 1 < L ∧
    accounts.associatedAccount.index + 1 < L ∧ accounts.wallet.index + 1 < L ∧
    accounts.mint.index + 1 < L ∧ accounts.systemProgram.index + 1 < L ∧
    accounts.tokenProgram.index + 1 < L := by
  simp only [CreateAccounts.wellFormed, Bool.and_eq_true,
    ProofForge.Svm.Sdk.CpiAccount.Handle.wellFormed, decide_eq_true_eq] at h
  exact ⟨h.1.1.1.1.1.1, h.1.1.1.1.1.2, h.1.1.1.1.2, h.1.1.1.2, h.1.1.2, h.1.2, h.2⟩


theorem recoverNestedAccounts_wf_parts (accounts : RecoverNestedAccounts) (L : Nat)
    (h : accounts.wellFormed L = true) :
    accounts.associatedTokenProgram.index + 1 < L ∧ accounts.nestedAssociatedAccount.index + 1 < L ∧
    accounts.nestedMint.index + 1 < L ∧ accounts.destinationAssociatedAccount.index + 1 < L ∧
    accounts.ownerAssociatedAccount.index + 1 < L ∧ accounts.ownerMint.index + 1 < L ∧
    accounts.wallet.index + 1 < L ∧ accounts.tokenProgram.index + 1 < L := by
  simp only [RecoverNestedAccounts.wellFormed, Bool.and_eq_true,
    ProofForge.Svm.Sdk.CpiAccount.Handle.wellFormed, decide_eq_true_eq] at h
  exact ⟨h.1.1.1.1.1.1.1, h.1.1.1.1.1.1.2, h.1.1.1.1.1.2, h.1.1.1.1.2, h.1.1.1.2, h.1.1.2, h.1.2, h.2⟩

end Proofs

end ProofForge.Svm.Sdk.AssociatedToken
