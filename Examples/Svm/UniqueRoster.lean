import ProofForge.Attr
import ProofForge.Svm.Sdk.StorageEnumerableSet

/-!
Idempotent roster policy over the same reusable SVM persistent enumerable set as
`MemberDirectory`, with a distinct capacity and application contract.
-/

namespace Examples.Svm.UniqueRoster
open ProofForge.Svm.Sdk.StorageEnumerableSet

@[pf_inline] def roster (account : Nat) : Descriptor :=
  Descriptor.oneBased account 3 5

structure State where
  dummy : UInt64
  deriving Repr, DecidableEq, Inhabited

inductive Error where
  | full
  deriving Repr, DecidableEq, Inhabited, BEq

@[pf_entry] def init (_seed : UInt64) : State := { dummy := 0 }

@[pf_entry] def initializeStorage (_s : State) : UInt64 :=
  (roster 1).initialize

@[pf_entry] def size (_s : State) : UInt64 := (roster 1).size
@[pf_entry] def enrolled (_s : State) (identity : UInt64) : Bool :=
  (roster 1).contains identity
@[pf_entry] def identityAt (_s : State) (index : UInt64) : UInt64 :=
  (roster 1).valueAt index

/-- Existing membership is an idempotent success; only a genuinely absent full insert fails. -/
@[pf_entry] def enroll (_s : State) (identity : UInt64) : Except Error (State × UInt64) :=
  let result := (roster 1).insert identity
  if result = 0 then .error .full else .ok ({ dummy := 1 }, 1)

/-- Missing membership is an idempotent no-op. -/
@[pf_entry] def withdraw (_s : State) (identity : UInt64) : UInt64 :=
  (roster 1).remove identity

end Examples.Svm.UniqueRoster