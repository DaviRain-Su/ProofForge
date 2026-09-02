import ProofForge
import ProofForge.Svm.Sdk.TransientRecord64

/-!
# Dedicated fixed-width POD record evidence

This example is an independent non-Phoenix consumer for the new `Sdk.Transient.Record64` layer
(fixed 2-limb `(holder, amount)` records; capacity is a compile-time record count). It composes
the existing two-slot `Transient.Vector64` lifecycle only - no pointer, no new runtime leaf, no
new low-level op - and stays independent from `MemoryOps`/`TransientPair`. Its shape and policies
differ from `Examples.Svm.TransientOrderTape` (3-limb records, clear-on-full policy) so both can be
registered independently by the coordinator.
-/

namespace Examples.Svm.TransientLedger
open ProofForge.Svm.Sdk

/-- Minimal managed state, mirroring `Examples.Svm.MemoryOps` so this module stays inside the standard
module profile while its methods exercise invocation-only heap effects. -/
structure State where
  dummy : UInt64
  deriving Repr, DecidableEq, Inhabited

inductive Error where
  | overflow
  deriving Repr, DecidableEq, Inhabited, BEq

private def u64Max : UInt64 := ~~~(0 : UInt64)

/-- Slot-0 ledger: capacity 8 two-limb records over 16 payload words. -/
@[pf_inline] private def ledgerA : Transient.Record64 := Transient.Record64.bounded 2 8
/-- Slot-1 ledger: same kind and record shape, private metadata bank and payload region. -/
@[pf_inline] private def ledgerB : Transient.Record64 := Transient.Record64.boundedAlt 2 4
/-- Two-record ledger for the explicit preflight-full policy. -/
@[pf_inline] private def ledgerSmall : Transient.Record64 := Transient.Record64.bounded 2 2
/-- Alternate-slot geometry sized just below the default frame edge: 2047 * 2 = 4094 payload
words, the largest two-limb shape the handle envelope admits. -/
@[pf_inline] private def ledgerFullB : Transient.Record64 :=
  Transient.Record64.boundedAlt 2 2047
/-- Deliberately tiny slot-0 handle that cannot fit once `ledgerFullB` owns the payload budget. -/
@[pf_inline] private def oneWord : Transient.Record64 := Transient.Record64.bounded 1 2

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

/-- The SDK preflights and appends one complete two-limb record; no single-limb mutation is
available at this abstraction boundary. -/
@[pf_entry]
def appendEntry (_state : State) (holder amount : UInt64) : UInt64 :=
  let _ := ledgerA.begin
  let _ := ledgerA.append2 holder amount
  let count := ledgerA.count
  let _ := ledgerA.finish
  count

/-- Record-aligned in-place write then read: the limb indexes select fields inside the
`index`-th record, never bytes of the neighboring record. -/
@[pf_entry]
def rewriteAmount (_state : State) (index amount : UInt64) : UInt64 :=
  let _ := ledgerA.begin
  let _ := ledgerA.append2 101 1001
  let _ := ledgerA.append2 202 2002
  let _ := ledgerA.setLimb index 1 amount
  let holder := ledgerA.getLimb index 0
  let amount := ledgerA.getLimb index 1
  let _ := ledgerA.finish
  1000 * holder + amount

/-- `truncateRecords` shortens in whole records only; the saturated keep-count never stops inside
a record and `lastLimb` reads the surviving tail. -/
@[pf_entry]
def truncateLedger (_state : State) (keep : UInt64) : UInt64 :=
  let _ := ledgerA.begin
  let _ := ledgerA.append2 11 12
  let _ := ledgerA.append2 21 22
  let _ := ledgerA.truncateRecords keep
  let count := ledgerA.count
  let head := ledgerA.getLimb 0 0
  let _ := ledgerA.finish
  100 * count + head

/-- Record-aligned pop composition: `lastLimb` reads the former top record, `dropLast` removes it
with one record-aligned shortening, and the count shrinks by exactly one. -/
@[pf_entry]
def dropTopEntry (_state : State) : UInt64 :=
  let _ := ledgerA.begin
  let _ := ledgerA.append2 7 70
  let _ := ledgerA.append2 8 80
  let _ := ledgerA.append2 9 90
  let topAmount := ledgerA.lastLimb 1
  let _ := ledgerA.dropLast
  let count := ledgerA.count
  let _ := ledgerA.finish
  1000 * topAmount + count

/-- Two-record preflight-full policy: after the capacity is reached the consumer branches on the
SDK preflight and rejects the whole third record, so the payload never holds a partial one. -/
@[pf_entry]
def rejectWhenFull (_state : State) (holder amount : UInt64) : UInt64 :=
  let _ := ledgerSmall.begin
  let _ := ledgerSmall.append2 1 2
  let _ := ledgerSmall.append2 21 22
  if ledgerSmall.hasRoom 1 then
    let _ := ledgerSmall.append2 holder amount
    let count := ledgerSmall.count
    let _ := ledgerSmall.finish
    count
  else
    let _ := ledgerSmall.finish
    999

/-- One handle's `count` and limbs stay independent of a second same-shape handle in the other
slot: both slots 0 and 1 are active with disjoint private metadata banks and payloads. -/
@[pf_entry]
def twinLedgers (_state : State) (index : UInt64) : UInt64 :=
  let _ := ledgerA.begin
  let _ := ledgerB.begin
  let _ := ledgerA.append2 1 2
  let _ := ledgerA.append2 3 4
  let _ := ledgerB.append2 11 22
  let _ := ledgerB.append2 33 44
  let _ := ledgerA.setLimb 0 1 55
  let fromFirst := ledgerA.getLimb index 1
  let fromSecond := ledgerB.getLimb index 1
  let _ := ledgerA.finish
  let _ := ledgerB.finish
  100000 + 1000 * fromFirst + fromSecond

/-- Same-kind record isolation across truncate: slot 0 rewrites its own prefix while slot 1's
records keep their values. -/
@[pf_entry]
def twinRewriteIsolated (_state : State) : UInt64 :=
  let _ := ledgerA.begin
  let _ := ledgerB.begin
  let _ := ledgerA.append2 1 2
  let _ := ledgerB.append2 8 9
  let _ := ledgerA.truncateRecords 0
  let _ := ledgerA.append2 4 5
  let a := ledgerA.getLimb 0 0
  let b := ledgerB.getLimb 0 0
  let ca := ledgerA.count
  let cb := ledgerB.count
  let _ := ledgerA.finish
  let _ := ledgerB.finish
  100000 * a + 100 * b + 10 * ca + cb

/-- Finishing the slot-0 ledger invalidates only its own handle; the slot-1 ledger stays live,
readable at its own last record, and closeable. The consumed count is read into an explicit
scalar step before the checked read, which also documents the extraction boundary: several
component queries consumed inside one arithmetic expression (instead of one explicit step each)
would otherwise be lowered at the return position, after this handle closes. -/
@[pf_entry]
def finishIsolation (_state : State) : UInt64 :=
  let _ := ledgerA.begin
  let _ := ledgerB.begin
  let _ := ledgerA.append2 91 92
  let _ := ledgerB.append2 93 94
  let _ := ledgerA.finish
  let count := ledgerB.count
  let staged := ledgerB.getLimb (count - 1) 0
  let _ := ledgerB.finish
  staged

/-- A second-slot ledger that was never begun stays inactive on its own state error. -/
@[pf_entry]
def unbegunAlternate (_state : State) : UInt64 :=
  let _ := ledgerA.begin
  let _ := ledgerB.append2 1 2
  0

/-- A record index at or above the live count terminates with the bounded-index error even though
it is still inside the compile-time payload. -/
@[pf_entry]
def oobRecord (_state : State) (index : UInt64) : UInt64 :=
  let _ := ledgerA.begin
  let _ := ledgerA.append2 5 6
  let staged := ledgerA.getLimb index 0
  let _ := ledgerA.finish
  staged

/-- A limb index at or above the fixed stride terminates instead of silently reading the next
record's first limb. -/
@[pf_entry]
def oobLimb (_state : State) : UInt64 :=
  let _ := ledgerA.begin
  let _ := ledgerA.append2 5 6
  let staged := ledgerA.getLimb 0 2
  let _ := ledgerA.finish
  staged

/-- `finish` invalidates the record handle even though the bump allocation is not reclaimed. -/
@[pf_entry]
def staleAfterFinish (_state : State) : UInt64 :=
  let _ := ledgerA.begin
  let _ := ledgerA.append2 1 2
  let _ := ledgerA.finish
  let count := ledgerA.count
  let _ := ledgerA.finish
  count

/-- Two same-kind record slots share one bounded invocation heap: an almost-full alternate-slot
allocation plus a slot-0 allocation that no longer fits propagates the dedicated OOM program
error. -/
@[pf_entry]
def crossSlotOom (_state : State) : UInt64 :=
  let _ := ledgerFullB.begin
  let _ := oneWord.begin
  0

end Examples.Svm.TransientLedger