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

end Examples.MemoryOps
