import ProofForge.Attr
import ProofForge.Svm.Sdk.Transient
import ProofForge.Svm.Sdk.TransientVec

/-!
# Source-facing invocation-local fixed-width POD records

A bounded counterpart of an on-chain `Vec<Record>` with a compile-time record shape: each record
occupies a fixed positive number of `UInt64` limbs and the capacity is a fixed positive number of
records. The payload, lifecycle, and failure vocabulary are entirely the existing two-slot
`Transient.Vector64` component - this module composes that API and adds nothing below it: no new
Runtime leaf, no new top-level Ops/IR op, no component interpreter, and no main-emitter recipe.
The compiler-erased handle is still one static `UInt64` word with the reusable
`Sdk.Transient` slot identity (slot 0 = plain payload, slot 1 = payload packed above bit 32).

Record semantics are SDK-owned and stay record-aligned by construction:

- `count` rejects a live word length that is not divisible by the fixed stride.
- `append1` through `append4` preflight the whole record before sequencing existing word pushes;
  the SDK does not expose a single-word push that could leave a partial logical record.
- Record-aligned pop is consumer composition of `lastLimb` reads followed by `dropLast`;
  `truncateRecords`, `clear`, and `finish` are single component calls whose new length is derived
  from the live record count.
- Checked record/limb access routes failure through the underlying `Vector64` bounded-index gate
  (0x1202); `finish`/stale handles keep the component state error (0x1203), and OOM keeps the
  component OOM error (0x1201).

Geometry is a compile-time truth table. Constructors accept only `(limbs, records)` and derive the
payload product and erased slot word; callers cannot repeat or disagree about that product. Zero
limbs/records and products outside the existing Vector64 frame/handle envelope fail closed. Two
same-kind record handles (slots 0 and 1) can be active in one invocation exactly as for plain
`Vector64`.

This layer is invocation-local only: no native or source-visible pointer, no realloc, no
persistent heap object, no account-resident heap metadata, and no reclamation claim. Persistent
SVM collections remain canonical account bytes.
-/

namespace ProofForge.Svm.Sdk.Transient

open ProofForge.Svm.TransientVec

/-- Compile-time geometry for one bounded invocation-local fixed-width record vector.

`limbs` is the record stride in `UInt64` words, `records` the bounded record capacity, and
`alternate` selects existing Vector64 slot 0 or 1. Payload words and the erased handle word are
derived, never supplied independently. Every field is consumed statically; nothing but existing
component leaves reaches the target. -/
structure Record64 where
  limbs : Nat
  records : Nat
  alternate : Bool
  deriving BEq, Repr, Inhabited

/-- Slot-0 record handle: the historical plain-payload encoding, exactly `Vector64.bounded`. -/
@[pf_inline] def Record64.bounded (limbs records : Nat) : Record64 :=
  { limbs, records, alternate := false }

/-- Slot-1 record handle: same shape, private metadata bank and payload region, exactly
`Vector64.boundedAlt`. The slot rides additively inside the erased word, so extraction still
decodes one static `UInt64` argument and no new runtime leaf. -/
@[pf_inline] def Record64.boundedAlt (limbs records : Nat) : Record64 :=
  { limbs, records, alternate := true }

/-- Derived payload word count. Nat multiplication is exact at compile time; Vector64 validation
owns the low-32-bit handle and invocation-frame limits. -/
@[pf_inline] def Record64.payload (record : Record64) : Nat :=
  record.limbs * record.records

/-- Existing compiler-erased Vector64 handle word for the selected slot. -/
@[pf_inline] def Record64.words (record : Record64) : Nat :=
  if record.alternate then secondSlotWord record.payload else record.payload

/-- The existing bounded vector this record handle composes. -/
@[pf_inline] private def Record64.vector (record : Record64) : Vector64 :=
  { capacity := record.words }

/-- Compile-time truth table: positive stride and capacity plus the existing frame-fitting,
low-32-bit Vector64 geometry. The payload product and slot cannot be malformed independently. -/
def Record64.wellFormed (record : Record64) : Bool :=
  0 < record.limbs && 0 < record.records && record.vector.wellFormed

/-! ## Geometry and checked record access -/

/-- Fixed record stride in `UInt64` limbs. -/
@[pf_inline] def Record64.stride (record : Record64) : UInt64 :=
  UInt64.ofNat record.limbs

/-- Compile-time record capacity. -/
@[pf_inline] def Record64.capacity (record : Record64) : UInt64 :=
  UInt64.ofNat record.records

/-- Force the existing bounds terminal without mutating the live prefix. `length` is exactly the
first invalid Vector64 index. -/
@[pf_inline] private def Record64.rejectBounds (record : Record64) : UInt64 :=
  record.vector.get record.vector.length

/-- Live record count. A malformed partial prefix is rejected instead of being rounded down. -/
@[pf_inline] def Record64.count (record : Record64) : UInt64 :=
  let length := record.vector.length
  if record.stride == 0 then
    record.rejectBounds
  else if length % record.stride == 0 then
    length / record.stride
  else
    record.rejectBounds

/-- SDK-owned preflight: `records` more whole records still fit under the current live length.
The subtraction form cannot wrap when the requested runtime count is huge. -/
@[pf_inline] def Record64.hasRoom (record : Record64) (additional : UInt64) : Bool :=
  let count := record.count
  if count <= record.capacity then additional <= record.capacity - count else false

/-- SDK-owned preflight: no room for even one more record. -/
@[pf_inline] def Record64.isFull (record : Record64) : Bool := !record.hasRoom 1

/-- Checked read of one record limb. Out-of-range record or limb indexes terminate with the
component's bounded-index error. -/
@[pf_inline] def Record64.getLimb (record : Record64)
    (recordIndex limbIndex : UInt64) : UInt64 :=
  let count := record.count
  if recordIndex < count then
    if limbIndex < record.stride then
      record.vector.get (recordIndex * record.stride + limbIndex)
    else
      record.rejectBounds
  else
    record.rejectBounds

/-- Checked in-place write of one record limb. Out-of-range indexes terminate with the
component's bounded-index error; the write itself is one component call and never leaves a
partial record. -/
@[pf_inline] def Record64.setLimb (record : Record64)
    (recordIndex limbIndex value : UInt64) : UInt64 :=
  let count := record.count
  if recordIndex < count then
    if limbIndex < record.stride then
      record.vector.set (recordIndex * record.stride + limbIndex) value
    else
      record.rejectBounds
  else
    record.rejectBounds

/-! ## Record-aligned mutation -/

/-- Preflight one fixed-arity append. The expected arity prevents using (for example) `append2`
on a three-limb descriptor. -/
@[pf_inline] private def Record64.canAppendAs (record : Record64) (arity : UInt64) : Bool :=
  record.stride == arity && record.hasRoom 1

/-- Append one complete one-limb record. -/
@[pf_inline] def Record64.append1 (record : Record64) (a : UInt64) : UInt64 :=
  if record.canAppendAs 1 then record.vector.push a else record.rejectBounds

/-- Append one complete two-limb record after a whole-record preflight. -/
@[pf_inline] def Record64.append2 (record : Record64) (a b : UInt64) : UInt64 :=
  if record.canAppendAs 2 then
    let _ := record.vector.push a
    record.vector.push b
  else
    record.rejectBounds

/-- Append one complete three-limb record after a whole-record preflight. -/
@[pf_inline] def Record64.append3 (record : Record64) (a b c : UInt64) : UInt64 :=
  if record.canAppendAs 3 then
    let _ := record.vector.push a
    let _ := record.vector.push b
    record.vector.push c
  else
    record.rejectBounds

/-- Append one complete four-limb record after a whole-record preflight. Wider records remain
explicitly unsupported until another bounded arity is justified. -/
@[pf_inline] def Record64.append4 (record : Record64) (a b c d : UInt64) : UInt64 :=
  if record.canAppendAs 4 then
    let _ := record.vector.push a
    let _ := record.vector.push b
    let _ := record.vector.push c
    record.vector.push d
  else
    record.rejectBounds

/-- Remove the last live record (a fixed `limbs`-word shortening). Empty is a bounds error, like
`Vector64.pop`, rather than a silent no-op. -/
@[pf_inline] def Record64.dropLast (record : Record64) : UInt64 :=
  let count := record.count
  if count == 0 then record.rejectBounds
  else record.vector.truncate ((count - 1) * record.stride)

/-- Shorten to `keep` live records, saturating above the current count. New lengths are computed
in whole records, so truncation can never stop inside a record. -/
@[pf_inline] def Record64.truncateRecords (record : Record64) (keep : UInt64) : UInt64 :=
  let count := record.count
  record.vector.truncate ((if keep < count then keep else count) * record.stride)

/-- First limb of the last live record. An empty handle fails with the component's
bounded-index error before subtracting from the live record count. -/
@[pf_inline] def Record64.lastLimb (record : Record64) (limbIndex : UInt64) : UInt64 :=
  let count := record.count
  if count == 0 then record.rejectBounds else record.getLimb (count - 1) limbIndex

/-! ## Lifecycle -/

/-- Open (or historically re-open) this record handle's slot. -/
@[pf_inline] def Record64.begin (record : Record64) : UInt64 :=
  record.vector.begin

/-- Invalidate this slot's record handle without reclaiming the bump allocation. -/
@[pf_inline] def Record64.finish (record : Record64) : UInt64 :=
  record.vector.finish

/-- Reset the live prefix to zero records without reallocating. -/
@[pf_inline] def Record64.clear (record : Record64) : UInt64 :=
  let count := record.count
  if count <= record.capacity then record.vector.clear else record.rejectBounds

attribute [pf_inline] Record64.limbs Record64.records Record64.alternate

end ProofForge.Svm.Sdk.Transient
