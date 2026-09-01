import ProofForge.Attr
import ProofForge.Core.Value
import ProofForge.Svm.Sdk.Pubkey
import ProofForge.Svm.Sdk.TransientRecord64

/-!
# Source-facing invocation-local typed wide vectors

`Vector128` and `Vector256` are bounded, allocation-free vectors for the target-neutral logical
values in `ProofForge.Core.Value`. `VectorPubkey` is the same composition for the SVM-local
`Sdk.Pubkey` fixed schema (four little-endian `UInt64` words / 32 bytes). Physical binding is
SVM-local and composed entirely over `Transient.Record64` and therefore over the existing two-slot
`Transient.Vector64` component.

Consumers never select record limbs. A push preflights one complete wide value before its first
word write; get, set, last, and drop preserve one logical element boundary; truncate and clear can
only select whole-value lengths. OOM (0x1201), bounds/full (0x1202), stale state (0x1203), bump-heap
lifetime, and two-slot isolation are inherited unchanged. This module adds no pointer, runtime
leaf, Ops/IR case, component, emitter recipe, persistence, realloc, or reclamation behavior.
-/

namespace ProofForge.Svm.Sdk.Transient

open ProofForge.Core.Value

/-! ## UInt128 -/

/-- Compile-time geometry for one bounded invocation-local vector of `Core.Value.UInt128`. -/
structure Vector128 where
  elements : Nat
  alternate : Bool
  deriving BEq, Repr, Inhabited

/-- Slot-0 typed UInt128 vector. -/
@[pf_inline] def Vector128.bounded (elements : Nat) : Vector128 :=
  { elements, alternate := false }

/-- Slot-1 typed UInt128 vector with a private existing Vector64 metadata bank. -/
@[pf_inline] def Vector128.boundedAlt (elements : Nat) : Vector128 :=
  { elements, alternate := true }

@[pf_inline] private def Vector128.record (vector : Vector128) : Record64 :=
  { limbs := 2, records := vector.elements, alternate := vector.alternate }

/-- Compile-time geometry gate inherited from the two-word Record64 shape. -/
def Vector128.wellFormed (vector : Vector128) : Bool := vector.record.wellFormed

@[pf_inline] def Vector128.begin (vector : Vector128) : UInt64 := vector.record.begin

/-- Number of live complete UInt128 values. -/
@[pf_inline] def Vector128.length (vector : Vector128) : UInt64 := vector.record.count

@[pf_inline] def Vector128.isFull (vector : Vector128) : Bool := vector.record.isFull

/-- Append one complete UInt128 after Record64 preflights both words. -/
@[pf_inline] def Vector128.push (vector : Vector128) (value : UInt128) : UInt64 :=
  let record := vector.record
  if record.hasRoom 1 then
    let words : Vector64 := { capacity := record.words }
    let _ := words.push value.w0
    words.push value.w1
  else
    record.getLimb record.count 0

/-- Read one complete UInt128 at a checked runtime index. -/
@[pf_inline] def Vector128.get (vector : Vector128) (index : UInt64) : UInt128 :=
  let w0 := vector.record.getLimb index 0
  let w1 := vector.record.getLimb index 1
  { w0, w1 }

/-- Replace one complete UInt128. The whole record index is checked before the first word write;
the fixed second word is then inside that same existing record. -/
@[pf_inline] def Vector128.set (vector : Vector128) (index : UInt64)
    (value : UInt128) : UInt64 :=
  let record := vector.record
  let count := record.count
  if index < count then
    let words : Vector64 := { capacity := record.words }
    let base := index * 2
    let _ := words.set base value.w0
    words.set (base + 1) value.w1
  else
    record.getLimb index 0

/-- Read the last complete UInt128; empty is the existing bounded-index error. -/
@[pf_inline] def Vector128.last (vector : Vector128) : UInt128 :=
  let w0 := vector.record.lastLimb 0
  let w1 := vector.record.lastLimb 1
  { w0, w1 }

/-- Remove the last complete UInt128 with one record-aligned truncate; empty is the existing
bounded-index error. Consumers that need the value read it through typed `last` before dropping. -/
@[pf_inline] def Vector128.dropLast (vector : Vector128) : UInt64 :=
  vector.record.dropLast

/-- Shorten to at most `keep` complete UInt128 values. -/
@[pf_inline] def Vector128.truncate (vector : Vector128) (keep : UInt64) : UInt64 :=
  vector.record.truncateRecords keep

@[pf_inline] def Vector128.clear (vector : Vector128) : UInt64 := vector.record.clear

@[pf_inline] def Vector128.finish (vector : Vector128) : UInt64 := vector.record.finish

/-! ## UInt256 -/

/-- Compile-time geometry for one bounded invocation-local vector of `Core.Value.UInt256`. -/
structure Vector256 where
  elements : Nat
  alternate : Bool
  deriving BEq, Repr, Inhabited

/-- Slot-0 typed UInt256 vector. -/
@[pf_inline] def Vector256.bounded (elements : Nat) : Vector256 :=
  { elements, alternate := false }

/-- Slot-1 typed UInt256 vector with a private existing Vector64 metadata bank. -/
@[pf_inline] def Vector256.boundedAlt (elements : Nat) : Vector256 :=
  { elements, alternate := true }

@[pf_inline] private def Vector256.record (vector : Vector256) : Record64 :=
  { limbs := 4, records := vector.elements, alternate := vector.alternate }

/-- Compile-time geometry gate inherited from the four-word Record64 shape. -/
def Vector256.wellFormed (vector : Vector256) : Bool := vector.record.wellFormed

@[pf_inline] def Vector256.begin (vector : Vector256) : UInt64 := vector.record.begin

/-- Number of live complete UInt256 values. -/
@[pf_inline] def Vector256.length (vector : Vector256) : UInt64 := vector.record.count

@[pf_inline] def Vector256.isFull (vector : Vector256) : Bool := vector.record.isFull

/-- Append one complete UInt256 after Record64 preflights all four words. -/
@[pf_inline] def Vector256.push (vector : Vector256) (value : UInt256) : UInt64 :=
  let record := vector.record
  if record.hasRoom 1 then
    let words : Vector64 := { capacity := record.words }
    let _ := words.push value.w0
    let _ := words.push value.w1
    let _ := words.push value.w2
    words.push value.w3
  else
    record.getLimb record.count 0

/-- Read one complete UInt256 at a checked runtime index. -/
@[pf_inline] def Vector256.get (vector : Vector256) (index : UInt64) : UInt256 :=
  let w0 := vector.record.getLimb index 0
  let w1 := vector.record.getLimb index 1
  let w2 := vector.record.getLimb index 2
  let w3 := vector.record.getLimb index 3
  { w0, w1, w2, w3 }

/-- Replace one complete UInt256. The whole record index is checked before the first word write;
the three fixed remaining words are then inside that same existing record. -/
@[pf_inline] def Vector256.set (vector : Vector256) (index : UInt64)
    (value : UInt256) : UInt64 :=
  let record := vector.record
  let count := record.count
  if index < count then
    let words : Vector64 := { capacity := record.words }
    let base := index * 4
    let _ := words.set base value.w0
    let _ := words.set (base + 1) value.w1
    let _ := words.set (base + 2) value.w2
    words.set (base + 3) value.w3
  else
    record.getLimb index 0

/-- Read the last complete UInt256; empty is the existing bounded-index error. -/
@[pf_inline] def Vector256.last (vector : Vector256) : UInt256 :=
  let w0 := vector.record.lastLimb 0
  let w1 := vector.record.lastLimb 1
  let w2 := vector.record.lastLimb 2
  let w3 := vector.record.lastLimb 3
  { w0, w1, w2, w3 }

/-- Remove the last complete UInt256 with one record-aligned truncate; empty is the existing
bounded-index error. Consumers that need the value read it through typed `last` before dropping. -/
@[pf_inline] def Vector256.dropLast (vector : Vector256) : UInt64 :=
  vector.record.dropLast

/-- Shorten to at most `keep` complete UInt256 values. -/
@[pf_inline] def Vector256.truncate (vector : Vector256) (keep : UInt64) : UInt64 :=
  vector.record.truncateRecords keep

@[pf_inline] def Vector256.clear (vector : Vector256) : UInt64 := vector.record.clear

@[pf_inline] def Vector256.finish (vector : Vector256) : UInt64 := vector.record.finish

/-! ## Pubkey (fixed 32-byte identity schema) -/

open ProofForge.Svm.Sdk

/-- Compile-time geometry for one bounded invocation-local vector of complete `Sdk.Pubkey`
values. This is the svm-sdk-003 fixed-schema POD shape: four little-endian limbs per element,
composed over existing Record64 / Vector64 slots with no new Runtime leaf. -/
structure VectorPubkey where
  elements : Nat
  alternate : Bool
  deriving BEq, Repr, Inhabited

/-- Slot-0 typed Pubkey vector. -/
@[pf_inline] def VectorPubkey.bounded (elements : Nat) : VectorPubkey :=
  { elements, alternate := false }

/-- Slot-1 typed Pubkey vector with a private existing Vector64 metadata bank. -/
@[pf_inline] def VectorPubkey.boundedAlt (elements : Nat) : VectorPubkey :=
  { elements, alternate := true }

@[pf_inline] private def VectorPubkey.record (vector : VectorPubkey) : Record64 :=
  { limbs := 4, records := vector.elements, alternate := vector.alternate }

/-- Compile-time geometry gate inherited from the four-word Record64 shape. -/
def VectorPubkey.wellFormed (vector : VectorPubkey) : Bool := vector.record.wellFormed

@[pf_inline] def VectorPubkey.begin (vector : VectorPubkey) : UInt64 := vector.record.begin

/-- Number of live complete Pubkey values. -/
@[pf_inline] def VectorPubkey.length (vector : VectorPubkey) : UInt64 := vector.record.count

@[pf_inline] def VectorPubkey.isFull (vector : VectorPubkey) : Bool := vector.record.isFull

/-- Append one complete Pubkey after Record64 preflights all four words. -/
@[pf_inline] def VectorPubkey.push (vector : VectorPubkey) (value : Pubkey) : UInt64 :=
  let record := vector.record
  if record.hasRoom 1 then
    let words : Vector64 := { capacity := record.words }
    let _ := words.push value.word0
    let _ := words.push value.word1
    let _ := words.push value.word2
    words.push value.word3
  else
    record.getLimb record.count 0

/-- Read one complete Pubkey at a checked runtime index. -/
@[pf_inline] def VectorPubkey.get (vector : VectorPubkey) (index : UInt64) : Pubkey :=
  let word0 := vector.record.getLimb index 0
  let word1 := vector.record.getLimb index 1
  let word2 := vector.record.getLimb index 2
  let word3 := vector.record.getLimb index 3
  { word0, word1, word2, word3 }

/-- Replace one complete Pubkey. The whole record index is checked before the first word write. -/
@[pf_inline] def VectorPubkey.set (vector : VectorPubkey) (index : UInt64)
    (value : Pubkey) : UInt64 :=
  let record := vector.record
  let count := record.count
  if index < count then
    let words : Vector64 := { capacity := record.words }
    let base := index * 4
    let _ := words.set base value.word0
    let _ := words.set (base + 1) value.word1
    let _ := words.set (base + 2) value.word2
    words.set (base + 3) value.word3
  else
    record.getLimb index 0

/-- Read the last complete Pubkey; empty is the existing bounded-index error. -/
@[pf_inline] def VectorPubkey.last (vector : VectorPubkey) : Pubkey :=
  let word0 := vector.record.lastLimb 0
  let word1 := vector.record.lastLimb 1
  let word2 := vector.record.lastLimb 2
  let word3 := vector.record.lastLimb 3
  { word0, word1, word2, word3 }

/-- Remove the last complete Pubkey with one record-aligned truncate. -/
@[pf_inline] def VectorPubkey.dropLast (vector : VectorPubkey) : UInt64 :=
  vector.record.dropLast

/-- Shorten to at most `keep` complete Pubkey values. -/
@[pf_inline] def VectorPubkey.truncate (vector : VectorPubkey) (keep : UInt64) : UInt64 :=
  vector.record.truncateRecords keep

@[pf_inline] def VectorPubkey.clear (vector : VectorPubkey) : UInt64 := vector.record.clear

@[pf_inline] def VectorPubkey.finish (vector : VectorPubkey) : UInt64 := vector.record.finish

attribute [pf_inline] Vector128.elements Vector128.alternate
attribute [pf_inline] Vector256.elements Vector256.alternate
attribute [pf_inline] VectorPubkey.elements VectorPubkey.alternate

end ProofForge.Svm.Sdk.Transient
