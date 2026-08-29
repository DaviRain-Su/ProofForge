import ProofForge

/-!
# Dedicated same-kind transient multi-handle evidence

This example is the non-Phoenix consumer for the two compile-time handle slots of each bounded
transient container kind (`ProofForge.Svm.Sdk.Transient`: two `Vector64` slots, two `Bytes`
slots). It is deliberately unaggregated: `Examples.lean`, the registries, and the `MemoryOps`
digest fixtures are coordinator-owned wiring, so this module stays independent until integration.

Every method here composes the same shared downward bump heap and the same target-owned lifecycle
interpreter as `Examples.MemoryOps`; only the same-kind slot isolation, unbegun-slot, and
cross-slot OOM evidence is new. No pointer, descriptor, allocator, or syscall appears in source.
-/

namespace Examples.TransientPair

open ProofForge.Svm.Sdk

/-- Minimal managed state, mirroring `Examples.MemoryOps` so this module stays inside the standard
module profile while its methods exercise invocation-only heap effects. -/
structure State where
  dummy : UInt64
  deriving Repr, DecidableEq, Inhabited

inductive Error where
  | overflow
  deriving Repr, DecidableEq, Inhabited, BEq

private def u64Max : UInt64 := ~~~(0 : UInt64)

@[pf_inline] private def vector2 : Transient.Vector64 := Transient.Vector64.bounded 2
@[pf_inline] private def vector2B : Transient.Vector64 := Transient.Vector64.boundedAlt 2
@[pf_inline] private def vectorFullB : Transient.Vector64 := Transient.Vector64.boundedAlt 4000
@[pf_inline] private def vectorHundred : Transient.Vector64 := Transient.Vector64.bounded 100
@[pf_inline] private def bytes4 : Transient.Bytes := Transient.Bytes.bounded 4
@[pf_inline] private def bytes4B : Transient.Bytes := Transient.Bytes.boundedAlt 4
@[pf_inline] private def bytesFullB : Transient.Bytes := Transient.Bytes.boundedAlt 32760
@[pf_inline] private def bytesFull : Transient.Bytes := Transient.Bytes.bounded 32760

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

/-- Two compile-time `Vector64` handles of the same kind are active together. Slot 0 and slot 1 own
private metadata banks and disjoint payload regions, so slot 0's in-place write never leaks into
slot 1's payload and each handle reads through its own runtime length. -/
@[pf_entry]
def vectorPairSetGet (_state : State) (index : UInt64) : UInt64 :=
  let _ := vector2.begin
  let _ := vector2B.begin
  let _ := vector2.push 11
  let _ := vector2.push 22
  let _ := vector2B.push 33
  let _ := vector2B.push 44
  let _ := vector2.set 1 55
  let fromFirst := vector2.get 1
  let fromSecond := vector2B.get index
  let _ := vector2.finish
  let _ := vector2B.finish
  fromFirst + fromSecond

/-- Same-kind slot isolation across clear: resetting slot 0's logical length keeps slot 1's active
prefix untouched. -/
@[pf_entry]
def vectorPairClearIsolated (_state : State) : UInt64 :=
  let _ := vector2.begin
  let _ := vector2B.begin
  let _ := vector2.push 1
  let _ := vector2B.push 2
  let _ := vector2B.push 3
  let _ := vector2.clear
  let firstLength := vector2.length
  let secondLength := vector2B.length
  let _ := vector2.finish
  let _ := vector2B.finish
  firstLength + 10 * secondLength

/-- Same-kind slot isolation across truncate and in-place element writes: slot 0 may shorten and
rewrite its own live prefix while slot 1's payload and length keep their values. -/
@[pf_entry]
def vectorPairTruncateIsolated (_state : State) : UInt64 :=
  let _ := vector2.begin
  let _ := vector2B.begin
  let _ := vector2.push 1
  let _ := vector2.push 2
  let _ := vector2B.push 3
  let _ := vector2B.push 4
  let _ := vector2.truncate 1
  let firstLength := vector2.length
  let secondLength := vector2B.length
  let secondTail := vector2B.get 1
  let _ := vector2.finish
  let _ := vector2B.finish
  firstLength + 10 * secondLength + secondTail

/-- Same-kind slot isolation across pop: each handle returns its own former tail element. If the
slots aliased one buffer, both pops would read the same memory and the results would coincide. -/
@[pf_entry]
def vectorPairPopIsolated (_state : State) : UInt64 :=
  let _ := vector2.begin
  let _ := vector2B.begin
  let _ := vector2.push 1
  let _ := vector2.push 2
  let _ := vector2B.push 3
  let _ := vector2B.push 4
  let secondPop := vector2B.pop
  let firstPop := vector2.pop
  let _ := vector2.finish
  let _ := vector2B.finish
  secondPop * 10 + firstPop

/-- Same-kind slot isolation across finish: closing slot 0 invalidates only its own metadata; the
slot-1 handle stays live, readable, and closeable. -/
@[pf_entry]
def vectorPairFinishIsolated (_state : State) : UInt64 :=
  let _ := vector2.begin
  let _ := vector2B.begin
  let _ := vector2B.push 66
  let _ := vector2.finish
  let staged := vector2B.get 0
  let _ := vector2B.finish
  staged

/-- Two `Vector64` slots and two `Bytes` slots share one invocation and one bump heap while every
handle keeps its own payload. -/
@[pf_entry]
def fourTransientPairs (_state : State) : UInt64 :=
  let _ := vector2.begin
  let _ := vector2B.begin
  let _ := bytes4.begin
  let _ := bytes4B.begin
  let _ := vector2.push 5
  let _ := vector2B.push 6
  let _ := bytes4.push 7
  let _ := bytes4B.push 8
  let stagedVector := vector2.get 0
  let stagedVectorB := vector2B.get 0
  let stagedBytes := bytes4.get 0
  let stagedBytesB := bytes4B.get 0
  let _ := bytes4B.finish
  let _ := bytes4.finish
  let _ := vector2B.finish
  let _ := vector2.finish
  stagedVector + stagedVectorB + stagedBytes + stagedBytesB

/-- A second-slot handle that was never begun stays inactive: the active marker belongs to the
slot's own metadata bank, not to one kind-wide cell. -/
@[pf_entry]
def vectorPairUnbegunSlot (_state : State) : UInt64 :=
  let _ := vector2.begin
  let _ := vector2B.push 1
  0

/-- Two same-kind vector slots share the bounded invocation heap: an almost-full slot-1 allocation
plus a slot-0 allocation that no longer fits propagates the dedicated OOM program error. -/
@[pf_entry]
def vectorPairOom (_state : State) : UInt64 :=
  let _ := vectorFullB.begin
  let _ := vectorHundred.begin
  0

/-- Two compile-time `Bytes` handles of the same kind are active together. Slot 0's in-place byte
store never leaks into slot 1's payload, and each handle reads through its own pointer and
length. -/
@[pf_entry]
def bytesPairSetGet (_state : State) (index : UInt64) : UInt64 :=
  let _ := bytes4.begin
  let _ := bytes4B.begin
  let _ := bytes4.push 0x11
  let _ := bytes4.push 0x22
  let _ := bytes4B.push 0x33
  let _ := bytes4B.push 0x44
  let _ := bytes4.set 1 0x99
  let fromFirst := bytes4.get index
  let fromSecond := bytes4B.get 1
  let _ := bytes4.finish
  let _ := bytes4B.finish
  fromSecond * 256 + fromFirst

/-- Same-kind slot isolation across truncate: slot 1's logical byte length survives slot 0's
independent lifecycle. -/
@[pf_entry]
def bytesPairTruncateIsolated (_state : State) : UInt64 :=
  let _ := bytes4.begin
  let _ := bytes4B.begin
  let _ := bytes4.push 1
  let _ := bytes4.push 2
  let _ := bytes4B.push 3
  let _ := bytes4B.truncate 0
  let firstLength := bytes4.length
  let secondLength := bytes4B.length
  let _ := bytes4.finish
  let _ := bytes4B.finish
  firstLength + 10 * secondLength

/-- A second-slot byte handle that was never begun stays inactive on its own state error. -/
@[pf_entry]
def bytesPairUnbegunSlot (_state : State) : UInt64 :=
  let _ := bytes4.begin
  let _ := bytes4B.push 1
  0

/-- Two same-kind byte slots share the same bump heap; a second almost-full allocation that no
longer fits propagates the dedicated OOM program error. -/
@[pf_entry]
def bytesPairOom (_state : State) : UInt64 :=
  let _ := bytesFullB.begin
  let _ := bytesFull.begin
  0

end Examples.TransientPair
