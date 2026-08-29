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
@[pf_inline] private def bytes4 : Transient.Bytes := Transient.Bytes.bounded 4
@[pf_inline] private def bytes1 : Transient.Bytes := Transient.Bytes.bounded 1
@[pf_inline] private def bytes3 : Transient.Bytes := Transient.Bytes.bounded 3
@[pf_inline] private def bytes12 : Transient.Bytes := Transient.Bytes.bounded 12
@[pf_inline] private def bytesFull : Transient.Bytes := Transient.Bytes.bounded 32760

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

/-- Open one bounded byte buffer, mutate an existing byte, read through a runtime index, and close
the source handle. `finish` deliberately does not reclaim the bump heap. -/
@[pf_entry]
def bytesSetGet (_state : State) (firstByte secondByte replacement index : UInt64) : UInt64 :=
  let _ := bytes4.begin
  let _ := bytes4.push firstByte
  let _ := bytes4.push secondByte
  let _ := bytes4.set 1 replacement
  let selected := bytes4.get index
  let _ := bytes4.finish
  selected

/-- `clear` resets logical byte length without reallocating or exposing the underlying pointer. -/
@[pf_entry]
def bytesLengthAfterClear (_state : State) (byte : UInt64) : UInt64 :=
  let _ := bytes4.begin
  let _ := bytes4.push byte
  let _ := bytes4.clear
  let length := bytes4.length
  let _ := bytes4.finish
  length

/-- One fixed-width little-endian append, then read byte `index` back. `index = 0` must be the
lowest byte and `index = 7` the highest, pinning the canonical little-endian record. -/
@[pf_entry]
def bytesAppendLe64 (_state : State) (value index : UInt64) : UInt64 :=
  let _ := bytes12.begin
  let _ := bytes12.appendLe64 value
  let selected := bytes12.get index
  let _ := bytes12.finish
  selected

/-- One `Vector64` handle and one byte-buffer handle may be active at the same time. The vector
and the bytes buffer compose through the same bump allocator with disjoint invocation metadata. -/
@[pf_entry]
def vectorWithBytes (_state : State) (word byte : UInt64) : UInt64 :=
  let _ := vector2.begin
  let _ := bytes4.begin
  let _ := bytes4.push byte
  let _ := vector2.push word
  let stagedByte := bytes4.get 0
  let stagedWord := vector2.get 0
  let _ := vector2.finish
  let _ := bytes4.finish
  stagedByte + stagedWord

/-- Fifth push must terminate with the byte buffer's explicit capacity error. -/
@[pf_entry]
def bytesOverflow (_state : State) : UInt64 :=
  let _ := bytes3.begin
  let _ := bytes3.push 1
  let _ := bytes3.push 2
  let _ := bytes3.push 3
  let _ := bytes3.push 4
  0

/-- Runtime byte read uses current length rather than static capacity. -/
@[pf_entry]
def bytesOutOfBounds (_state : State) : UInt64 :=
  let _ := bytes4.begin
  let _ := bytes4.push 1
  bytes4.get 1

/-- A different compile-time handle cannot consume the active byte-buffer allocation. -/
@[pf_entry]
def bytesWrongCapacity (_state : State) : UInt64 :=
  let _ := bytes4.begin
  let _ := bytes1.push 1
  0

/-- `finish` invalidates the invocation handle even though the bump allocation is not reclaimed. -/
@[pf_entry]
def bytesAfterFinish (_state : State) : UInt64 :=
  let _ := bytes4.begin
  let _ := bytes4.finish
  bytes4.length

/-- Byte pushes must carry canonical `≤ 255` values; `256` terminates with the dedicated
byte-range error instead of silently truncating. -/
@[pf_entry]
def bytesPushOverRange (_state : State) : UInt64 :=
  let _ := bytes4.begin
  let _ := bytes4.push 256
  0

/-- Byte stores validate the canonical range exactly like pushes. -/
@[pf_entry]
def bytesSetOverRange (_state : State) : UInt64 :=
  let _ := bytes4.begin
  let _ := bytes4.push 1
  let _ := bytes4.set 0 256
  0

/-- Fill the complete usable default heap payload with one byte buffer, then prove that the next
buffer allocation propagates the dedicated OOM program error. -/
@[pf_entry]
def bytesOom (_state : State) : UInt64 :=
  let _ := bytesFull.begin
  let _ := bytesFull.begin
  0

end Examples.MemoryOps
