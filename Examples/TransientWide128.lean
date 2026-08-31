import ProofForge
import ProofForge.Svm.Sdk.TransientWideVec

/-!
# Invocation-local UInt128 rejection policy

This independent non-Phoenix consumer treats a full typed vector as a rejected candidate and keeps
the existing tail. All limb construction is confined to scalar ABI boundaries; vector policy uses
`Core.Value.UInt128` values only.
-/

namespace Examples.TransientWide128

open ProofForge.Core.Value
open ProofForge.Svm.Sdk

structure State where
  dummy : UInt64
  deriving Repr, DecidableEq, Inhabited

inductive Error where
  | overflow
  deriving Repr, DecidableEq, Inhabited, BEq

private def u64Max : UInt64 := ~~~(0 : UInt64)

@[pf_inline] private def values3 : Transient.Vector128 := Transient.Vector128.bounded 3
@[pf_inline] private def values2Alt : Transient.Vector128 := Transient.Vector128.boundedAlt 2

@[pf_entry]
def init (initial : UInt64) : State := { dummy := initial }

@[pf_entry]
def get (state : State) : UInt64 := state.dummy

@[pf_entry]
def touch (state : State) : Except Error (State × UInt64) :=
  if state.dummy < u64Max then
    let next := state.dummy + 1
    .ok ({ dummy := next }, next)
  else
    .error .overflow

/-- Fill the exact three-value boundary and return the typed final value. Invocation completion
ends the allocation; explicit `finish` behavior is exercised separately. -/
@[pf_entry]
def pushExact (_state : State) (w0 w1 : UInt64) : UInt128 :=
  let candidate : UInt128 := { w0, w1 }
  let _ := values3.begin
  let _ := values3.push { w0 := 1, w1 := 2 }
  let _ := values3.push { w0 := 3, w1 := 4 }
  let _ := values3.push candidate
  values3.last

/-- Application policy: reject a candidate at full capacity without invoking a word write, and
return the intact typed tail. -/
@[pf_entry]
def rejectAtFull (_state : State) (_w0 _w1 : UInt64) : UInt128 :=
  let _ := values3.begin
  let _ := values3.push { w0 := 11, w1 := 12 }
  let _ := values3.push { w0 := 21, w1 := 22 }
  let _ := values3.push { w0 := 31, w1 := 32 }
  if values3.isFull then
    values3.last
  else
    let candidate : UInt128 := { w0 := _w0, w1 := _w1 }
    let _ := values3.push candidate
    values3.last

/-- The SDK's own full-capacity gate terminates before either candidate word is written. -/
@[pf_entry]
def overflowAtFull (_state : State) (w0 w1 : UInt64) : UInt64 :=
  let candidate : UInt128 := { w0, w1 }
  let _ := values3.begin
  let _ := values3.push { w0 := 1, w1 := 2 }
  let _ := values3.push { w0 := 3, w1 := 4 }
  let _ := values3.push { w0 := 5, w1 := 6 }
  values3.push candidate

/-- Whole-value replacement and runtime-indexed read. -/
@[pf_entry]
def setAndGet (_state : State) (index w0 w1 : UInt64) : UInt128 :=
  let replacement : UInt128 := { w0, w1 }
  let _ := values3.begin
  let _ := values3.push { w0 := 10, w1 := 20 }
  let _ := values3.push { w0 := 30, w1 := 40 }
  let _ := values3.set index replacement
  values3.get index

/-- Typed `last` plus whole-element drop, truncate, and clear permit reuse without a new
allocation. -/
@[pf_entry]
def rewindAndReuse (_state : State) (w0 w1 : UInt64) : UInt128 :=
  let candidate : UInt128 := { w0, w1 }
  let _ := values3.begin
  let _ := values3.push { w0 := 7, w1 := 8 }
  let _ := values3.push { w0 := 9, w1 := 10 }
  let _ := values3.dropLast
  let _ := values3.truncate 0
  let _ := values3.push candidate
  let _ := values3.clear
  let _ := values3.push { w0 := 9, w1 := 10 }
  let count := values3.length
  values3.get (count - 1)

/-- A runtime index at the live-length boundary fails through Record64/Vector64 bounds. -/
@[pf_entry]
def readAt (_state : State) (index : UInt64) : UInt128 :=
  let _ := values3.begin
  let _ := values3.push { w0 := 41, w1 := 42 }
  let _ := values3.push { w0 := 51, w1 := 52 }
  values3.get index

/-- Two typed handles reuse the existing Vector64 slots and retain disjoint lengths/payloads. -/
@[pf_entry]
def twoSlotIsolation (_state : State) : UInt128 :=
  let _ := values3.begin
  let _ := values2Alt.begin
  let _ := values3.push { w0 := 101, w1 := 102 }
  let _ := values2Alt.push { w0 := 201, w1 := 202 }
  let _ := values3.set 0 { w0 := 301, w1 := 302 }
  values2Alt.get 0

/-- Finish invalidates the typed handle without reclaiming its bump allocation. -/
@[pf_entry]
def staleAfterFinish (_state : State) : UInt64 :=
  let _ := values3.begin
  let _ := values3.push { w0 := 1, w1 := 2 }
  let _ := values3.finish
  values3.length

end Examples.TransientWide128
