import ProofForge
import ProofForge.Svm.Sdk.TransientWideVec

/-!
# Invocation-local UInt256 clear-and-reuse policy

This independent non-Phoenix consumer deliberately differs from `TransientWide128`: full capacity
causes a whole-vector clear followed by typed replacement. Scalar limbs appear only where the
external generated ABI constructs a `Core.Value.UInt256`.
-/

namespace Examples.TransientWide256

open ProofForge.Core.Value
open ProofForge.Svm.Sdk

structure State where
  dummy : UInt64
  deriving Repr, DecidableEq, Inhabited

inductive Error where
  | overflow
  deriving Repr, DecidableEq, Inhabited, BEq

private def u64Max : UInt64 := ~~~(0 : UInt64)

@[pf_inline] private def values2 : Transient.Vector256 := Transient.Vector256.bounded 2
@[pf_inline] private def edgeAlt : Transient.Vector256 := Transient.Vector256.boundedAlt 1023

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

/-- Fill the exact two-value boundary and return the typed final value. Invocation completion ends
the allocation; explicit `finish` behavior is exercised separately. -/
@[pf_entry]
def pushExact (_state : State) (w0 w1 w2 w3 : UInt64) : UInt256 :=
  let candidate : UInt256 := { w0, w1, w2, w3 }
  let _ := values2.begin
  let _ := values2.push { w0 := 1, w1 := 2, w2 := 3, w3 := 4 }
  let _ := values2.push candidate
  values2.last

/-- Application policy: clear a full vector and then install one complete typed replacement. -/
@[pf_entry]
def clearWhenFull (_state : State) (w0 w1 w2 w3 : UInt64) : UInt256 :=
  let candidate : UInt256 := { w0, w1, w2, w3 }
  let _ := values2.begin
  let _ := values2.push { w0 := 11, w1 := 12, w2 := 13, w3 := 14 }
  let _ := values2.push { w0 := 21, w1 := 22, w2 := 23, w3 := 24 }
  if values2.isFull then
    let _ := values2.clear
    let _ := values2.push candidate
    values2.get 0
  else
    values2.last

/-- The SDK's own full-capacity gate terminates before any candidate word is written. -/
@[pf_entry]
def overflowAtFull (_state : State) (w0 w1 w2 w3 : UInt64) : UInt64 :=
  let candidate : UInt256 := { w0, w1, w2, w3 }
  let _ := values2.begin
  let _ := values2.push { w0 := 1, w1 := 2, w2 := 3, w3 := 4 }
  let _ := values2.push { w0 := 5, w1 := 6, w2 := 7, w3 := 8 }
  values2.push candidate

/-- Whole-value replacement and runtime-indexed read. -/
@[pf_entry]
def setAndGet (_state : State) (index w0 w1 w2 w3 : UInt64) : UInt256 :=
  let replacement : UInt256 := { w0, w1, w2, w3 }
  let _ := values2.begin
  let _ := values2.push { w0 := 10, w1 := 20, w2 := 30, w3 := 40 }
  let _ := values2.push { w0 := 50, w1 := 60, w2 := 70, w3 := 80 }
  let _ := values2.set index replacement
  values2.get index

/-- Typed `last` plus whole-element drop; truncation and length remain in complete UInt256
elements. -/
@[pf_entry]
def dropAndRewind (_state : State) : UInt256 :=
  let _ := values2.begin
  let _ := values2.push { w0 := 7, w1 := 8, w2 := 9, w3 := 10 }
  let _ := values2.push { w0 := 17, w1 := 18, w2 := 19, w3 := 20 }
  let _ := values2.dropLast
  let _ := values2.truncate 0
  let _ := values2.push { w0 := 17, w1 := 18, w2 := 19, w3 := 20 }
  let count := values2.length
  values2.get (count - 1)

/-- A runtime index at the live-length boundary fails through Record64/Vector64 bounds. -/
@[pf_entry]
def readAt (_state : State) (index : UInt64) : UInt256 :=
  let _ := values2.begin
  let _ := values2.push { w0 := 41, w1 := 42, w2 := 43, w3 := 44 }
  values2.get index

/-- Finish invalidates the typed handle without reclaiming its bump allocation. -/
@[pf_entry]
def staleAfterFinish (_state : State) : UInt64 :=
  let _ := values2.begin
  let _ := values2.push { w0 := 1, w1 := 2, w2 := 3, w3 := 4 }
  let _ := values2.finish
  values2.length

/-- A 4092-word alternate UInt256 payload leaves too little room for this eight-word slot-0
payload, preserving the existing shared bump-heap OOM behavior. -/
@[pf_entry]
def crossSlotOom (_state : State) : UInt64 :=
  let _ := edgeAlt.begin
  let _ := values2.begin
  0

end Examples.TransientWide256
