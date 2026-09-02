import ProofForge.Attr
import ProofForge.Svm.Sdk.StorageBitSet

/-!
One-time claim registry over the reusable SVM persistent bit-set SDK. Unlike FeatureBits, this
consumer treats existing membership as a replay error. Capacity 130 exercises a partial final
word while preserving O(1) selected-word access.
-/

namespace Examples.Svm.ClaimBits
open ProofForge.Svm.Sdk.StorageBitSet

/-- Runtime account `1`, word 1 reserved, words 2..4 hold 130 claims. Bits 130..191 in the final
physical word are unreachable because the bit-capacity gate dominates every access. -/
@[pf_inline] def claims (account : Nat) : BitSet :=
  BitSet.oneBased account 2 130

structure State where
  dummy : UInt64
  deriving Repr, DecidableEq, Inhabited

inductive Error where
  | outOfRange
  | replay
  deriving Repr, DecidableEq, Inhabited, BEq

@[pf_entry]
def init (_seed : UInt64) : State :=
  { dummy := 0 }

@[pf_entry]
def claimed (_s : State) (index : UInt64) : UInt64 :=
  (claims 1).contains index

/-- Record one claim. OOB and replay are distinct source-policy branches; the current SVM named
error ABI maps both to its generic fail-closed code. Successful storage remains one checked
read-modify-write of the selected packed word. -/
@[pf_entry]
def claim (_s : State) (index : UInt64) : Except Error (State × UInt64) :=
  if !inRange (claims 1).capacity index then .error .outOfRange
  else
    let changed := (claims 1).insert index
    if changed = 0 then .error .replay
    else .ok ({ dummy := 1 }, 1)

end Examples.Svm.ClaimBits