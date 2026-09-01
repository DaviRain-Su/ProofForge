import ProofForge.Attr
import ProofForge.Svm.Sdk.StorageEnumerableSet

/-!
Strict membership directory over the reusable SVM persistent enumerable-set SDK. Protocol policy
owns duplicate/full/missing errors; the SDK owns compact account geometry, position validation,
tree indexing, bounded enumeration, and swap-remove.
-/

namespace Examples.MemberDirectory

open ProofForge.Svm.Sdk.StorageEnumerableSet

@[pf_inline] def members (account : Nat) : Descriptor :=
  Descriptor.oneBased account 2 4

structure State where
  dummy : UInt64
  deriving Repr, DecidableEq, Inhabited

inductive Error where
  | duplicate
  | full
  | missing
  deriving Repr, DecidableEq, Inhabited, BEq

@[pf_entry] def init (_seed : UInt64) : State := { dummy := 0 }

@[pf_entry] def initializeStorage (_s : State) : UInt64 :=
  (members 1).initialize

@[pf_entry] def size (_s : State) : UInt64 := (members 1).size
@[pf_entry] def contains (_s : State) (member : UInt64) : Bool := (members 1).contains member
@[pf_entry] def valueAt (_s : State) (index : UInt64) : UInt64 := (members 1).valueAt index

/-- Strict remove-by-index. OOB is `missing`. Uses the existing valueAt+remove path so the
index scan and swap-remove stay independently fail-closed. -/
@[pf_entry] def removeAt (_s : State) (index : UInt64) : Except Error (State × UInt64) :=
  let set := members 1
  if set.size ≤ index then .error .missing
  else
    let removed := set.remove (set.valueAt index)
    if removed = 0 then .error .missing else .ok ({ dummy := 1 }, 1)

/-- Reset headers; stale value words stay unreachable. -/
@[pf_entry] def clearStorage (_s : State) : UInt64 :=
  (members 1).clear

@[pf_entry] def add (_s : State) (member : UInt64) : Except Error (State × UInt64) :=
  let result := (members 1).insert member
  if result = 1 then .ok ({ dummy := 1 }, 1)
  else if result = 2 then .error .duplicate
  else .error .full

@[pf_entry] def remove (_s : State) (member : UInt64) : Except Error (State × UInt64) :=
  let removed := (members 1).remove member
  if removed = 0 then .error .missing else .ok ({ dummy := 1 }, 1)

end Examples.MemberDirectory
