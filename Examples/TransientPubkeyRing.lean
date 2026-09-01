import ProofForge
import ProofForge.Svm.Sdk.TransientWideVec

/-!
# Invocation-local Pubkey clear-and-reuse policy (`svm-sdk-003` consumer B)

Deliberately differs from `TransientPubkeyBatch`: full capacity clears the vector then installs
one complete typed replacement. Scalar limbs appear only where the generated ABI constructs a
`Pubkey`.
-/

namespace Examples.TransientPubkeyRing

open ProofForge.Svm.Sdk

structure State where
  dummy : UInt64
  deriving Repr, DecidableEq, Inhabited

inductive Error where
  | overflow
  deriving Repr, DecidableEq, Inhabited, BEq

private def u64Max : UInt64 := ~~~(0 : UInt64)

@[pf_inline] private def keys2 : Transient.VectorPubkey := Transient.VectorPubkey.bounded 2
@[pf_inline] private def edgeAlt : Transient.VectorPubkey := Transient.VectorPubkey.boundedAlt 1023

@[pf_inline] private def key (w0 w1 w2 w3 : UInt64) : Pubkey :=
  { word0 := w0, word1 := w1, word2 := w2, word3 := w3 }

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

/-- Fill the exact two-key boundary and return the typed final Pubkey. -/
@[pf_entry]
def pushExact (_state : State) (w0 w1 w2 w3 : UInt64) : Pubkey :=
  let candidate := key w0 w1 w2 w3
  let _ := keys2.begin
  let _ := keys2.push (key 1 2 3 4)
  let _ := keys2.push candidate
  keys2.last

/-- Application policy: clear a full vector and install one complete typed replacement. -/
@[pf_entry]
def clearWhenFull (_state : State) (w0 w1 w2 w3 : UInt64) : Pubkey :=
  let candidate := key w0 w1 w2 w3
  let _ := keys2.begin
  let _ := keys2.push (key 11 12 13 14)
  let _ := keys2.push (key 21 22 23 24)
  if keys2.isFull then
    let _ := keys2.clear
    let _ := keys2.push candidate
    keys2.get 0
  else
    keys2.last

/-- SDK full-capacity gate terminates before any candidate word is written. -/
@[pf_entry]
def overflowAtFull (_state : State) (w0 w1 w2 w3 : UInt64) : UInt64 :=
  let candidate := key w0 w1 w2 w3
  let _ := keys2.begin
  let _ := keys2.push (key 1 2 3 4)
  let _ := keys2.push (key 5 6 7 8)
  keys2.push candidate

/-- Whole-value replacement and runtime-indexed read. -/
@[pf_entry]
def setAndGet (_state : State) (index w0 w1 w2 w3 : UInt64) : Pubkey :=
  let replacement := key w0 w1 w2 w3
  let _ := keys2.begin
  let _ := keys2.push (key 10 20 30 40)
  let _ := keys2.push (key 50 60 70 80)
  let _ := keys2.set index replacement
  keys2.get index

/-- Typed `last` plus whole-element drop; truncation stays in complete Pubkey elements. -/
@[pf_entry]
def dropAndRewind (_state : State) : Pubkey :=
  let _ := keys2.begin
  let _ := keys2.push (key 7 8 9 10)
  let _ := keys2.push (key 17 18 19 20)
  let _ := keys2.dropLast
  let _ := keys2.truncate 0
  let _ := keys2.push (key 17 18 19 20)
  let count := keys2.length
  keys2.get (count - 1)

/-- A runtime index at the live-length boundary fails through Record64/Vector64 bounds. -/
@[pf_entry]
def readAt (_state : State) (index : UInt64) : Pubkey :=
  let _ := keys2.begin
  let _ := keys2.push (key 41 42 43 44)
  keys2.get index

/-- Finish invalidates the typed handle; the large alternate slot can still OOM independently. -/
@[pf_entry]
def staleAndCrossSlotOom (_state : State) : UInt64 :=
  let _ := keys2.begin
  let _ := keys2.push (key 1 2 3 4)
  let _ := keys2.finish
  let stale := keys2.length
  let _ := edgeAlt.begin
  stale

end Examples.TransientPubkeyRing
