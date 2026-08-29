import ProofForge

namespace Examples.MemoryOps

open ProofForge.Svm.Sdk

/-- Minimal managed state. Program-memory operations target physical account 1, whose byte
geometry is described once below and remains independent of the application state layout. -/
structure State where
  dummy : UInt64
  deriving Repr, DecidableEq, Inhabited

inductive Error where
  | overflow
  deriving Repr, DecidableEq, Inhabited, BEq

private def u64Max : UInt64 := ~~~(0 : UInt64)

@[pf_inline] private def first : Memory.Span := Memory.Span.accountData 1 0 8
@[pf_inline] private def second : Memory.Span := Memory.Span.accountData 1 8 8
@[pf_inline] private def overlappingDestination : Memory.Span := Memory.Span.accountData 1 4 8
@[pf_inline] private def vector2 : Transient.Vector64 := Transient.Vector64.bounded 2
@[pf_inline] private def vector1 : Transient.Vector64 := Transient.Vector64.bounded 1
@[pf_inline] private def vectorMax : Transient.Vector64 := Transient.Vector64.bounded 4095

@[pf_entry]
def init (initial : UInt64) : State :=
  { dummy := initial }

@[pf_entry]
def get (state : State) : UInt64 :=
  state.dummy

/-- Ordinary managed-state transition keeps this example inside the standard module profile;
memory effects below remain independent external-account operations. -/
@[pf_entry]
def touch (state : State) : Except Error (State × UInt64) :=
  if state.dummy < u64Max then
    let next := state.dummy + 1
    .ok ({ dummy := next }, next)
  else
    .error .overflow

/-- Fill the first fixed span with the low byte of `byte`. -/
@[pf_entry]
def fillBytes (_state : State) (byte : UInt64) : UInt64 :=
  Memory.set first byte

/-- Copy between statically disjoint equal-length spans. -/
@[pf_entry]
def copyBytes (_state : State) : UInt64 :=
  Memory.copyNonoverlapping second first

/-- Exercise the overlap-safe host contract: `[0,8)` moves to `[4,12)`. -/
@[pf_entry]
def moveBytes (_state : State) : UInt64 :=
  Memory.move overlappingDestination first

/-- Return the official signed-i32 comparison result as a zero-extended 32-bit bit pattern. -/
@[pf_entry]
def compareBytes (_state : State) : UInt64 :=
  Memory.compareI32Bits first second

/-- Allocate one bounded invocation vector, mutate an existing element, read through a runtime
index, and close the source handle. `finish` deliberately does not reclaim the bump heap. -/
@[pf_entry]
def vectorSetGet (_state : State) (firstValue secondValue replacement index : UInt64) : UInt64 :=
  let _ := vector2.begin
  let _ := vector2.push firstValue
  let _ := vector2.push secondValue
  let _ := vector2.set 1 replacement
  let selected := vector2.get index
  let _ := vector2.finish
  selected

/-- `clear` resets logical length without reallocating or exposing the underlying pointer. -/
@[pf_entry]
def vectorLengthAfterClear (_state : State) (value : UInt64) : UInt64 :=
  let _ := vector2.begin
  let _ := vector2.push value
  let _ := vector2.clear
  let length := vector2.length
  let _ := vector2.finish
  length

/-- Third push must terminate with the vector's explicit capacity error. -/
@[pf_entry]
def vectorOverflow (_state : State) : UInt64 :=
  let _ := vector2.begin
  let _ := vector2.push 1
  let _ := vector2.push 2
  let _ := vector2.push 3
  0

/-- Runtime get uses current length rather than static capacity. -/
@[pf_entry]
def vectorOutOfBounds (_state : State) : UInt64 :=
  let _ := vector2.begin
  let _ := vector2.push 1
  vector2.get 1

/-- A different compile-time handle cannot consume the active vector allocation. -/
@[pf_entry]
def vectorWrongCapacity (_state : State) : UInt64 :=
  let _ := vector2.begin
  let _ := vector1.push 1
  0

/-- `finish` invalidates the invocation handle even though the bump allocation is not reclaimed. -/
@[pf_entry]
def vectorAfterFinish (_state : State) : UInt64 :=
  let _ := vector2.begin
  let _ := vector2.finish
  vector2.length

/-- Fill the complete default heap payload, then prove that the next allocation propagates the
dedicated OOM program error. The first allocation itself remains constant-size assembly. -/
@[pf_entry]
def vectorOom (_state : State) : UInt64 :=
  let _ := vectorMax.begin
  let _ := vector1.begin
  0

end Examples.MemoryOps
