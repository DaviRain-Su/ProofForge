import ProofForge
import ProofForge.Svm.Sdk.TransientRecord64

/-!
# Dedicated fixed-width POD record evidence: a second independent shape and policy

This example is the second independent non-Phoenix consumer for `Sdk.Transient.Record64`,
deliberately composed differently from `Examples.Svm.TransientLedger`: three-limb
`(price, quantity, sequence)` records instead of two, a clear-and-reuse capacity policy instead
of a reject-at-full sentinel, a two-record alternate slot, and an exact default-frame single-limb
alternate shape for the cross-slot OOM evidence. It composes only the existing two-slot
`Transient.Vector64` lifecycle: no pointer, no realloc, no new runtime leaf, no new Ops/IR op,
and no new component interpreter below the SDK. Every whole-record mutation uses the SDK's
fixed-arity preflight append, and pop/truncate/clear/finish stay record-aligned.
-/

namespace Examples.Svm.TransientOrderTape
open ProofForge.Svm.Sdk

/-- Minimal managed state, mirroring `Examples.Svm.TransientPair` so this module stays inside the
standard module profile while its methods exercise invocation-only heap effects. -/
structure State where
  dummy : UInt64
  deriving Repr, DecidableEq, Inhabited

inductive Error where
  | overflow
  deriving Repr, DecidableEq, Inhabited, BEq

private def u64Max : UInt64 := ~~~(0 : UInt64)

/-- Slot-0 tape: capacity 4, three `UInt64` limbs per record, 12 payload words. -/
@[pf_inline] private def tape4 : Transient.Record64 := Transient.Record64.bounded 3 4
/-- Slot-1 tape: same shape, private metadata bank and payload region, capacity 2 records. -/
@[pf_inline] private def tape2 : Transient.Record64 := Transient.Record64.boundedAlt 3 2
/-- Alternate-slot single-limb shape at the exact default-frame payload edge (4095 words). -/
@[pf_inline] private def tapeEdge : Transient.Record64 :=
  Transient.Record64.boundedAlt 1 4095
/-- A deliberately tiny slot-0 handle that cannot fit once `tapeEdge` owns the payload. -/
@[pf_inline] private def oneLimb : Transient.Record64 := Transient.Record64.bounded 1 3

@[pf_entry]
def init (initial : UInt64) : State :=
  { dummy := initial }

@[pf_entry]
def get (state : State) : UInt64 :=
  state.dummy

/-- Ordinary managed-state transition keeps this example inside the standard module profile;
transient effects below remain invocation-only heap operations. -/
@[pf_entry]
def touch (state : State) : Except Error (State × UInt64) :=
  if state.dummy < u64Max then
    let next := state.dummy + 1
    .ok ({ dummy := next }, next)
  else
    .error .overflow

/-- A whole three-limb record uses the SDK append; an application preflight chooses policy before
the second append, while SDK preflight still guarantees atomic record formation. -/
@[pf_entry]
def appendWithRoom (_state : State) (price quantity sequence : UInt64) : UInt64 :=
  let _ := tape2.begin
  let _ := tape2.append3 11 12 13
  if tape2.hasRoom 1 then
    let _ := tape2.append3 price quantity sequence
    let count := tape2.count
    let tail := tape2.lastLimb 0
    let _ := tape2.finish
    100 * count + tail
  else
    let _ := tape2.finish
    1

/-- Overwrite policy: the seeded 4-record capacity is full, so the next whole record reuses the
payload of record zero by clearing first. The SDK preflight branches between whole records;
the rewritten record 0 reads back intact afterwards. -/
@[pf_entry]
def appendOverwrite (_state : State) (price quantity sequence : UInt64) : UInt64 :=
  let _ := tape4.begin
  let _ := tape4.append3 111 112 113
  let _ := tape4.append3 121 122 123
  let _ := tape4.append3 131 132 133
  let _ := tape4.append3 141 142 143
  if tape4.isFull then
    let _ := tape4.clear
    let _ := tape4.append3 price quantity sequence
    let count := tape4.count
    let limb0 := tape4.getLimb 0 0
    let limb1 := tape4.getLimb 0 1
    let limb2 := tape4.getLimb 0 2
    let _ := tape4.finish
    count + limb0 + 100 * limb1 + 10000 * limb2
  else
    let _ := tape4.finish
    9

/-- Record-aligned read of a full 3-limb record through a runtime record index. -/
@[pf_entry]
def readQuote (_state : State) (index : UInt64) : UInt64 :=
  let _ := tape4.begin
  let _ := tape4.append3 41 42 43
  let _ := tape4.append3 51 52 53
  let price := tape4.getLimb index 0
  let quantity := tape4.getLimb index 1
  let sequence := tape4.getLimb index 2
  let _ := tape4.finish
  100 * price + 10 * quantity + sequence

/-- Same-kind slot isolation: both three-limb handles write disjoint payloads concurrently and
each reads only through its own length. Slot 0 rewrites record 0 limb 0 in place without leaking
into slot 1. -/
@[pf_entry]
def twinTapes (_state : State) (index : UInt64) : UInt64 :=
  let _ := tape4.begin
  let _ := tape2.begin
  let _ := tape4.append3 55 56 57
  let _ := tape4.append3 58 59 60
  let _ := tape2.append3 65 66 67
  let _ := tape2.append3 75 76 77
  let _ := tape4.setLimb 0 0 88
  let firstPrice := tape4.getLimb index 0
  let secondSequence := tape2.getLimb index 2
  let _ := tape2.finish
  let _ := tape4.finish
  firstPrice + 1000 * secondSequence

/-- Record-aligned pop composition: `lastLimb` reads the former top record and `dropLast`
removes it with one record-aligned shortening, so the count shrinks by exactly one record. -/
@[pf_entry]
def dropTopQuote (_state : State) : UInt64 :=
  let _ := tape4.begin
  let _ := tape4.append3 91 92 93
  let _ := tape4.append3 81 82 83
  let topPrice := tape4.lastLimb 0
  let _ := tape4.dropLast
  let count := tape4.count
  let _ := tape4.finish
  100 * topPrice + count

/-- Finishing the slot-0 tape invalidates only its own handle; the slot-1 tape stays live,
readable at its own last record, and closeable. -/
@[pf_entry]
def tapeFinishIsolated (_state : State) : UInt64 :=
  let _ := tape4.begin
  let _ := tape2.begin
  let _ := tape4.append3 91 92 93
  let _ := tape2.append3 7 8 9
  let _ := tape4.finish
  let staged := tape2.lastLimb 2
  let _ := tape2.finish
  staged

/-- A second-slot tape that was never begun stays inactive on its own state error. -/
@[pf_entry]
def unbegunAlternate (_state : State) : UInt64 :=
  let _ := tape4.begin
  let _ := tape2.append3 1 2 3
  0

/-- A limb index at or above the fixed stride terminates instead of silently reading the next
record's first limb. -/
@[pf_entry]
def oobLimb (_state : State) : UInt64 :=
  let _ := tape4.begin
  let _ := tape4.append3 1 2 3
  let staged := tape4.getLimb 0 3
  let _ := tape4.finish
  staged

/-- A record at or above the live count (after a whole-record shortening) terminates with the
bounded-index error even though it is still inside the compile-time payload. -/
@[pf_entry]
def oobAfterRewind (_state : State) (index : UInt64) : UInt64 :=
  let _ := tape4.begin
  let _ := tape4.append3 41 42 43
  let _ := tape4.append3 51 52 53
  let _ := tape4.truncateRecords 1
  let staged := tape4.getLimb index 0
  let _ := tape4.finish
  staged

/-- `finish` invalidates the record handle even though the bump allocation is not reclaimed. -/
@[pf_entry]
def staleAfterFinish (_state : State) : UInt64 :=
  let _ := tape4.begin
  let _ := tape4.append3 1 2 3
  let _ := tape4.finish
  let count := tape4.count
  let _ := tape4.finish
  count

/-- Two same-kind record slots share the bounded invocation heap: an almost-full alternate-slot
allocation (4095 payload words) plus a slot-0 allocation that no longer fits propagates the
dedicated OOM program error. -/
@[pf_entry]
def crossSlotOom (_state : State) : UInt64 :=
  let _ := tapeEdge.begin
  let _ := oneLimb.begin
  0

end Examples.Svm.TransientOrderTape