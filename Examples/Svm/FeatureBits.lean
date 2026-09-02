import ProofForge.Attr
import ProofForge.Svm.Sdk.StorageBitSet

/-!
Owner-independent feature configuration over the reusable SVM persistent bit-set SDK. This
consumer chooses idempotent enable/disable semantics and exposes toggle's resulting membership;
the SDK owns fixed packed-word geometry, bounds, and one-word account effects.
-/

namespace Examples.Svm.FeatureBits
open ProofForge.Svm.Sdk.StorageBitSet

/-- Runtime account `1`, word 1 reserved for layout metadata, words 2..3 hold 128 feature bits. -/
@[pf_inline] def flags (account : Nat) : BitSet :=
  BitSet.oneBased account 2 128

structure State where
  dummy : UInt64
  deriving Repr, DecidableEq, Inhabited

inductive Error where
  | outOfRange
  deriving Repr, DecidableEq, Inhabited, BEq

@[pf_entry]
def init (_seed : UInt64) : State :=
  { dummy := 0 }

@[pf_entry]
def enabled (_s : State) (index : UInt64) : UInt64 :=
  (flags 1).contains index

/-- Idempotently enable a feature. Application policy makes OOB a typed error while an existing
feature remains a successful enabled state. -/
@[pf_entry]
def enable (_s : State) (index : UInt64) : Except Error (State × UInt64) :=
  if !inRange (flags 1).capacity index then .error .outOfRange
  else
    let _ := (flags 1).insert index
    .ok ({ dummy := 1 }, 1)

/-- Idempotently disable a feature. -/
@[pf_entry]
def disable (_s : State) (index : UInt64) : Except Error (State × UInt64) :=
  if !inRange (flags 1).capacity index then .error .outOfRange
  else
    let _ := (flags 1).remove index
    .ok ({ dummy := 0 }, 0)

/-- Toggle a feature and return the resulting membership. -/
@[pf_entry]
def toggle (_s : State) (index : UInt64) : Except Error (State × UInt64) :=
  if !inRange (flags 1).capacity index then .error .outOfRange
  else
    let present := (flags 1).toggle index
    .ok ({ dummy := present }, present)

end Examples.Svm.FeatureBits