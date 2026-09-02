import ProofForge

namespace Examples.Near.NearMemory
open ProofForge.Wasm.Near.Sdk

structure State where
  marker : UInt64
  deriving Repr, DecidableEq, Inhabited

inductive Error where
  | overflow
  deriving Repr, DecidableEq, Inhabited, BEq

@[pf_entry]
def init (marker : UInt64) : State :=
  { marker }

@[pf_entry]
def get (state : State) : UInt64 :=
  state.marker

@[pf_entry]
def touch (_state : State) : Except Error (State × UInt64) :=
  if (0 : UInt64) ≠ 1 then
    .ok ({ marker := 1 }, 1)
  else
    .error .overflow

/-- Allocate, initialize, mutate, and read without exposing the physical Wasm pointer. -/
@[pf_entry]
def roundTrip (_state : State) (value : UInt64) : UInt64 :=
  let _ := (4 : Transient.Buffer64).begin
  let _ := (4 : Transient.Buffer64).set 2 value
  (4 : Transient.Buffer64).get 2

/-- Every new buffer is initialized independently of reused instance memory. -/
@[pf_entry]
def startsZero (_state : State) : UInt64 :=
  let _ := (4 : Transient.Buffer64).begin
  (4 : Transient.Buffer64).get 3

/-- Two non-reclaiming allocations cross the source module's first 64-KiB page and therefore
keep the `memory.grow` path live. nearcore may normalize a larger initial memory. -/
@[pf_entry]
def growAndReuse (_state : State) (value : UInt64) : UInt64 :=
  let _ := (4096 : Transient.Buffer64).begin
  let _ := (4096 : Transient.Buffer64).finish
  let _ := (4096 : Transient.Buffer64).begin
  let _ := (4096 : Transient.Buffer64).set 4095 value
  (4096 : Transient.Buffer64).get 4095

@[pf_entry]
def outOfBounds (_state : State) : UInt64 :=
  let _ := (2 : Transient.Buffer64).begin
  (2 : Transient.Buffer64).get 2

@[pf_entry]
def staleHandle (_state : State) : UInt64 :=
  let _ := (2 : Transient.Buffer64).begin
  let _ := (2 : Transient.Buffer64).finish
  (2 : Transient.Buffer64).get 0

@[pf_entry]
def wrongCapacity (_state : State) : UInt64 :=
  let _ := (2 : Transient.Buffer64).begin
  (1 : Transient.Buffer64).get 0

@[pf_entry]
def doubleBegin (_state : State) : UInt64 :=
  let _ := (2 : Transient.Buffer64).begin
  let _ := (1 : Transient.Buffer64).begin
  0

end Examples.Near.NearMemory