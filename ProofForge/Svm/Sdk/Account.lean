import ProofForge.Attr
import ProofForge.Svm.AccountView
import ProofForge.Svm.Runtime

/-!
# SVM SDK account and signer handles

Source contracts name fixed accounts, required signers, and bounded remaining-account windows with
compile-time handles. Every accessor is `pf_inline`: extraction erases the handle to the existing
target-owned Runtime leaf or `Svm.AccountView` component query. This module adds no operation, IR
variant, component, emitter recipe, runtime geometry, pointer, or account copy.

Fixed handles contain one static account index. Bounded views contain static `base/capacity`
geometry and one runtime zero-based index; the target checks that index against both capacity and
the invocation's account count before reading. All malformed or unavailable accesses keep the
existing target-owned `Custom(1)` failure behavior.
-/

namespace ProofForge.Svm.Sdk

open ProofForge.Svm.Runtime

namespace Account

/-- One compile-time physical account index. The descriptor is erased during extraction. -/
structure Handle where
  index : Nat
  deriving BEq, Repr, Inhabited

attribute [pf_inline] Handle.index

/-- Name a fixed account. Presence remains an invocation-time property checked by the target. -/
@[pf_inline] def Handle.at (index : Nat) : Handle := { index }

/-- Static transaction account-lock bound. -/
def Handle.wellFormed (handle : Handle) (accountLimit : Nat := 64) : Bool :=
  handle.index < accountLimit

/-- A 32-byte key/owner exposes four little-endian words. -/
def Handle.wordWellFormed (handle : Handle) (word : Nat) (accountLimit : Nat := 64) : Bool :=
  handle.wellFormed accountLimit && word ≤ ProofForge.Svm.AccountView.maxKeyWord

/-- A data word's final byte must fit in the target's u64 `data_len` arithmetic. -/
def Handle.dataWordWellFormed (handle : Handle) (word : Nat)
    (accountLimit : Nat := 64) : Bool :=
  handle.wellFormed accountLimit && word < ProofForge.Svm.AccountView.maxDataWord

@[pf_inline] def Handle.lamports (handle : Handle) : UInt64 :=
  accLamports (UInt64.ofNat handle.index)

@[pf_inline] def Handle.dataLen (handle : Handle) : UInt64 :=
  accDataLen (UInt64.ofNat handle.index)

@[pf_inline] def Handle.isSigner (handle : Handle) : UInt64 :=
  Runtime.isSigner (UInt64.ofNat handle.index)

@[pf_inline] def Handle.isWritable (handle : Handle) : UInt64 :=
  Runtime.isWritable (UInt64.ofNat handle.index)

@[pf_inline] def Handle.isExecutable (handle : Handle) : UInt64 :=
  Runtime.isExecutable (UInt64.ofNat handle.index)

@[pf_inline] def Handle.keyWord (handle : Handle) (word : Nat) : UInt64 :=
  accKeyWord (UInt64.ofNat handle.index) (UInt64.ofNat word)

@[pf_inline] def Handle.ownerWord (handle : Handle) (word : Nat) : UInt64 :=
  accOwnerWord (UInt64.ofNat handle.index) (UInt64.ofNat word)

@[pf_inline] def Handle.dataWord (handle : Handle) (word : Nat) : UInt64 :=
  accDataWord (UInt64.ofNat handle.index) (UInt64.ofNat word)

/-- Existing Runtime convention: `0` means owned by this program, `1` means another owner. -/
@[pf_inline] def Handle.ownedBySelf (handle : Handle) : UInt64 :=
  ownerIsSelf (UInt64.ofNat handle.index)

/--
Move `amount` lamports from the fixed `source` account to the fixed `destination` account. The
two typed handles are erased at extraction, leaving only their static physical indexes; callers
never supply raw offsets, pointers, or ABI markers. The target preflights both writable flags,
source current-program ownership, source balance, destination overflow, and canonical-header
distinctness (duplicate aliases fail closed) before either store; any failure is `Custom(1)` with
no writes. A writable foreign-owned destination may be credited. Amount zero succeeds after the
same validation, keeping the API contract stable. The signed total lamport delta is zero.
-/
@[pf_inline] def Handle.transferLamports (source destination : Handle) (amount : UInt64) :
    UInt64 :=
  Runtime.transferLamports (UInt64.ofNat source.index) (UInt64.ofNat destination.index) amount

/-!
Resize one fixed external account's data using the current zero-initializing Solana
`AccountInfo::resize` contract. This is a bounded direct account-ABI mutation, not System
`Allocate`, heap `realloc`, or a persistent pointer. The target checks writable/current-program
ownership, the 10 MiB ceiling, and the 10,240-byte growth budget relative to the invocation's
original length before any change. A shrink preserves the retained prefix; a grow preserves the
old prefix and zeroes every newly exposed byte.

The managed ProofForge State account at physical index zero has a fixed extracted schema and is
not an admissible resize handle. A fixed external position that aliases state account zero also
fails closed. Duplicate aliases among external positions share their canonical account header.
-/
@[pf_inline] def Handle.resizeData (handle : Handle) (newLength : UInt64) : UInt64 :=
  Runtime.resizeAccountData (UInt64.ofNat handle.index) newLength

/-!
Close one fixed program-owned account by shrinking its data to zero and moving its complete
lamport balance to a fixed refund destination. This is ordinary SDK composition over the checked
`resizeData` and `transferLamports` contracts above, not a new Runtime operation: extraction first
snapshots the source balance, then preserves exactly one resize and one transfer in source order.

The source must be a writable external account owned by the current program. The destination must
be writable and canonically distinct, but may be foreign-owned. Runtime duplicate aliases,
destination overflow, malformed account data, and all other underlying preflight failures remain
`Custom(1)`. Solana instruction rollback makes a later transfer failure atomic with the earlier
resize. No owner reassignment, pointer, heap allocation, or runtime-selected account geometry is
introduced.
-/
@[pf_inline] def Handle.closeTo (source destination : Handle) : UInt64 :=
  let balance := source.lamports
  let _ := source.resizeData 0
  let _ := source.transferLamports destination balance
  balance

/-- Compile-time bounded remaining-account window. This is the target plan type itself, not a
second source-side geometry structure. -/
abbrev View := ProofForge.Svm.AccountView.View

@[pf_inline] def View.bounded (base capacity : Nat) : View := { base, capacity }

@[pf_inline] def View.peekData (view : View) (word : Nat) (index : UInt64) : UInt64 :=
  viewDataWord (UInt64.ofNat view.base) (UInt64.ofNat view.capacity) (UInt64.ofNat word) index

@[pf_inline] def View.peekKey (view : View) (word : Nat) (index : UInt64) : UInt64 :=
  viewKeyWord (UInt64.ofNat view.base) (UInt64.ofNat view.capacity) (UInt64.ofNat word) index

@[pf_inline] def View.peekSigner (view : View) (index : UInt64) : UInt64 :=
  viewIsSigner (UInt64.ofNat view.base) (UInt64.ofNat view.capacity) index

@[pf_inline] def View.peekWritable (view : View) (index : UInt64) : UInt64 :=
  viewIsWritable (UInt64.ofNat view.base) (UInt64.ofNat view.capacity) index

@[pf_inline] def View.peekDataLen (view : View) (index : UInt64) : UInt64 :=
  viewDataLen (UInt64.ofNat view.base) (UInt64.ofNat view.capacity) index

@[pf_inline] def View.peekLamports (view : View) (index : UInt64) : UInt64 :=
  viewLamports (UInt64.ofNat view.base) (UInt64.ofNat view.capacity) index

@[pf_inline] def View.ownedBySelf (view : View) (index : UInt64) : UInt64 :=
  viewOwnerIsSelf (UInt64.ofNat view.base) (UInt64.ofNat view.capacity) index

end Account

namespace CpiAccount

/-- One compile-time account index relative to the external-account region after state. This is
the index convention used by CPI metas, account-key PDA seeds, and signed-CPI authorities; it is
deliberately distinct from `Account.Handle`, whose index is physical. -/
structure Handle where
  index : Nat
  deriving BEq, Repr, Inhabited

attribute [pf_inline] Handle.index

/-- Name one statically selected CPI account. The descriptor is erased during extraction. -/
@[pf_inline] def Handle.at (index : Nat) : Handle := { index }

/-- Static transaction account-lock bound for CPI-relative indexes. Physical account zero is
reserved for state, so the external index must leave room for that prefix account. -/
def Handle.wellFormed (handle : Handle) (accountLimit : Nat := 64) : Bool :=
  handle.index + 1 < accountLimit

end CpiAccount

namespace Signer

/-- A fixed account whose first key-word access carries the existing target signer requirement. -/
structure Handle where
  account : Account.Handle
  deriving BEq, Repr, Inhabited

attribute [pf_inline] Handle.account

@[pf_inline] def Handle.at (index : Nat) : Handle :=
  { account := Account.Handle.at index }

def Handle.wellFormed (handle : Handle) (accountLimit : Nat := 64) : Bool :=
  handle.account.wellFormed accountLimit

/-- First little-endian public-key word. As with the established Runtime leaf, using it requires
the fixed account to be a transaction signer before method execution. -/
@[pf_inline] def Handle.key0 (handle : Handle) : UInt64 :=
  signerKey (UInt64.ofNat handle.account.index)

end Signer

end ProofForge.Svm.Sdk
