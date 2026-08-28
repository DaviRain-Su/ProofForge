import ProofForge.Attr
import ProofForge.Svm.AccountView
import ProofForge.Svm.Runtime

/-!
# SVM SDK bounded remaining-account view facade

A contract names its bounded remaining-account window once as a compile-time `Source.View` handle
and reads the runtime-selected account through `pf_inline` accessors. Extraction erases the handle
and the numeric window geometry into the existing target-owned `Svm.AccountView` component query;
no runtime geometry, pointer, heap container, or new SVM operation is introduced.

## Physical contract

The handle carries exactly two static scalars, `base` and `capacity`: physical accounts
`[base, base + capacity)` are addressable by one runtime zero-based index. Physical account 0 stays
reserved for authenticated ProofForge state. At every access the target validates
`index < capacity` (compile-time bound) and `base + index < NUM_ACCOUNTS` (available accounts),
then walks the real account headers in place and reads the selected header field or data word.
Any violation exits `Custom(1)` atomically before selected field/data bytes are read or state is stored.

The view is read-only: persistent state remains fixed account bytes owned by the storage
components. There is no write path, no duplicated window state, and no invocation-local copy of
account bytes.
-/

namespace ProofForge.Svm.AccountView.Source

open ProofForge.Svm.Runtime

/-- Compile-time bounded remaining-account window. -/
structure View where
  base : Nat
  capacity : Nat
  deriving BEq, Repr, Inhabited

/-- Name one bounded window once. `base ≥ 1` keeps physical account 0 reserved for state;
`base + capacity` must stay inside the transaction account-lock limit. -/
@[pf_inline] def View.bounded (base capacity : Nat) : View := { base, capacity }

/-- The window descriptor must satisfy the shared component contract. -/
def View.wellFormed (view : View) (accountLimit : Nat := 64) : Bool :=
  ProofForge.Svm.AccountView.View.wellFormed
    { base := view.base, capacity := view.capacity } accountLimit

/-- First `word`-th little-endian u64 of the selected account's data. The target checks both index
bounds and `data_len` before the read; OOB exits `Custom(1)` atomically. -/
@[pf_inline] def View.peekData (view : View) (word : Nat) (index : UInt64) : UInt64 :=
  viewDataWord (UInt64.ofNat view.base) (UInt64.ofNat view.capacity) (UInt64.ofNat word) index

/-- Public-key word `word` (0..=3) of the selected account. -/
@[pf_inline] def View.peekKey (view : View) (word : Nat) (index : UInt64) : UInt64 :=
  viewKeyWord (UInt64.ofNat view.base) (UInt64.ofNat view.capacity) (UInt64.ofNat word) index

/-- `is_signer` (0 or 1) of the selected account. -/
@[pf_inline] def View.peekSigner (view : View) (index : UInt64) : UInt64 :=
  viewIsSigner (UInt64.ofNat view.base) (UInt64.ofNat view.capacity) index

/-- `is_writable` (0 or 1) of the selected account. -/
@[pf_inline] def View.peekWritable (view : View) (index : UInt64) : UInt64 :=
  viewIsWritable (UInt64.ofNat view.base) (UInt64.ofNat view.capacity) index

/-- `data_len` of the selected account. -/
@[pf_inline] def View.peekDataLen (view : View) (index : UInt64) : UInt64 :=
  viewDataLen (UInt64.ofNat view.base) (UInt64.ofNat view.capacity) index

/-- Lamports of the selected account. -/
@[pf_inline] def View.peekLamports (view : View) (index : UInt64) : UInt64 :=
  viewLamports (UInt64.ofNat view.base) (UInt64.ofNat view.capacity) index

/-- Whether the selected account is owned by the current program (0 = yes, 1 = no). -/
@[pf_inline] def View.ownedBySelf (view : View) (index : UInt64) : UInt64 :=
  viewOwnerIsSelf (UInt64.ofNat view.base) (UInt64.ofNat view.capacity) index

end ProofForge.Svm.AccountView.Source
