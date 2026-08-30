import ProofForge.Attr
import ProofForge.Core.Collections
import ProofForge.Svm.Sdk.Storage

/-!
# SVM SDK persistent bounded bit set

Account-resident binding of the shared `Core.Collections.BoundedBitSet` packed-word law. A bit
capacity is compile-time data; the physical state is exactly `(bits + 63) / 64` consecutive
program-owned `UInt64` account words. There is no runtime length, allocator, pointer, heap object,
or target-specific container operation.

Every operation first checks `index < bits`, then touches exactly one selected word through the
existing checked account-storage source facade. Out-of-range indexes return `0` without account
access and cannot wrap into a lower word. Bulk clear and enumeration are intentionally absent:
they require an explicit capacity-bounded application policy rather than pretending to be O(1).
-/

namespace ProofForge.Svm.Sdk.StorageBitSet

open ProofForge.Svm.AccountStorage
open ProofForge.Svm.AccountStorage.Source
open ProofForge.Svm.Sdk.Storage

/-- Number of persistent `UInt64` words required for `bits`; shared exactly with the target-neutral
bounded bit-set semantics and the EVM storage binding. -/
@[pf_inline] def wordCount (bits : Nat) : Nat :=
  ProofForge.Core.Collections.bitSetWordCount bits

/-- Compile-time descriptor of one account-resident bit set. `words` is a one-based, stride-one
column whose region capacity is exactly `wordCount bitCapacity`. Both fields are erased descriptor
data; the capacity is not stored in the account or selected at runtime. -/
structure BitSet where
  words : Field
  bitCapacity : Nat
  deriving BEq, Repr, Inhabited

attribute [pf_inline] BitSet.words BitSet.bitCapacity

/-- Construct a bit set over consecutive words of one program-owned account. -/
@[pf_inline] def BitSet.oneBased
    (account baseWord bits : Nat) : BitSet :=
  { words := Field.oneBased account baseWord 1 ((bits + 63) / 64), bitCapacity := bits }

/-- Descriptor validity. The word ceiling is inherited from persistent SDK containers; the
checked account stubs still enforce actual `data_len`, writability, and current-program ownership
on every selected access. -/
def BitSet.wellFormed (set : BitSet) (accountLimit : Nat := 64) : Bool :=
  0 < set.bitCapacity && wordCount set.bitCapacity ≤ containerCapacityLimit &&
    set.words.mutableOneBasedWord accountLimit && set.words.region.account > 0 &&
    set.words.region.capacity == wordCount set.bitCapacity

/-- Compile-time bit capacity exposed as an erased runtime literal. -/
@[pf_inline] def BitSet.capacity (set : BitSet) : UInt64 :=
  UInt64.ofNat set.bitCapacity

/-! ## Shared packed-word policy -/

/-- Single bounds authority. Callers can use it to distinguish OOB application policy from an
ordinary absent bit before invoking a mutating operation. -/
@[pf_inline] def inRange (bits index : UInt64) : Bool :=
  ProofForge.Core.Collections.BoundedBitSet.inRange bits index

/-- Zero-based word index of a bit. Meaningful only behind `inRange`. -/
@[pf_inline] def wordIndexOf (index : UInt64) : UInt64 :=
  ProofForge.Core.Collections.BoundedBitSet.wordIndexOf index

/-- One-based account slot of a bit's selected word. -/
@[pf_inline] def wordSlotOf (index : UInt64) : UInt64 :=
  wordIndexOf index + 1

/-- Single-bit mask within the selected word. -/
@[pf_inline] def maskOf (index : UInt64) : UInt64 :=
  ProofForge.Core.Collections.BoundedBitSet.maskOf index

/-- Pure packed-word membership decision, shared in shape with the EVM binding. -/
@[pf_inline] def containsOf (word index : UInt64) : Bool :=
  ProofForge.Core.Collections.BoundedBitSet.containsOf word index

/-- Pure word value after setting one bit. -/
@[pf_inline] def insertOf (word index : UInt64) : UInt64 :=
  ProofForge.Core.Collections.BoundedBitSet.insertOf word index

/-- Pure word value after clearing one bit. -/
@[pf_inline] def removeOf (word index : UInt64) : UInt64 :=
  ProofForge.Core.Collections.BoundedBitSet.removeOf word index

/-- Pure word value after toggling one bit. -/
@[pf_inline] def toggleOf (word index : UInt64) : UInt64 :=
  ProofForge.Core.Collections.BoundedBitSet.toggleOf word index

/-! ## Account-resident operations -/

/-- Return `1` when an in-range bit is present, otherwise `0`. OOB performs no account read. -/
@[pf_inline] def BitSet.contains (set : BitSet) (index : UInt64) : UInt64 :=
  if !inRange set.capacity index then 0
  else
    let word := read set.words (wordSlotOf index)
    if word &&& maskOf index = 0 then 0 else 1

/-- Set one in-range bit. Returns `1` only when membership changed; an existing bit or OOB index
returns `0` without a write. -/
@[pf_inline] def BitSet.insert (set : BitSet) (index : UInt64) : UInt64 :=
  if !inRange set.capacity index then 0
  else
    let slot := wordSlotOf index
    let word := read set.words slot
    if word &&& maskOf index = 0 then
      let _ := write set.words slot (insertOf word index)
      1
    else
      0

/-- Clear one in-range bit. Returns `1` only when membership changed; an absent bit or OOB index
returns `0` without a write. -/
@[pf_inline] def BitSet.remove (set : BitSet) (index : UInt64) : UInt64 :=
  if !inRange set.capacity index then 0
  else
    let slot := wordSlotOf index
    let word := read set.words slot
    if word &&& maskOf index = 0 then
      0
    else
      let _ := write set.words slot (removeOf word index)
      1

/-- Toggle one in-range bit and return its resulting membership (`0` or `1`). OOB returns `0`
without account access. -/
@[pf_inline] def BitSet.toggle (set : BitSet) (index : UInt64) : UInt64 :=
  if !inRange set.capacity index then 0
  else
    let slot := wordSlotOf index
    let word := read set.words slot
    if word &&& maskOf index = 0 then
      let _ := write set.words slot (insertOf word index)
      1
    else
      let _ := write set.words slot (removeOf word index)
      0

end ProofForge.Svm.Sdk.StorageBitSet
