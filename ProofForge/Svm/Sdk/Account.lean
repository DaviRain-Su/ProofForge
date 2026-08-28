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
