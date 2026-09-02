import ProofForge
import ProofForge.Svm.Sdk.TransientWideVec

/-!
# Invocation-local Pubkey rejection policy (`svm-sdk-003` consumer A)

Treats a full typed Pubkey vector as a rejected candidate and keeps the existing tail. Key words
appear only at the scalar ABI boundary; vector policy uses complete `Sdk.Pubkey` values.
-/

namespace Examples.Svm.TransientPubkeyBatch

open ProofForge.Svm.Sdk

structure State where
  dummy : UInt64
  deriving Repr, DecidableEq, Inhabited

inductive Error where
  | overflow
  deriving Repr, DecidableEq, Inhabited, BEq

private def u64Max : UInt64 := ~~~(0 : UInt64)

@[pf_inline] private def keys3 : Transient.VectorPubkey := Transient.VectorPubkey.bounded 3
@[pf_inline] private def keys2Alt : Transient.VectorPubkey := Transient.VectorPubkey.boundedAlt 2

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

/-- Fill the exact three-key boundary and return the typed final Pubkey. -/
@[pf_entry]
def pushExact (_state : State) (w0 w1 w2 w3 : UInt64) : Pubkey :=
  let candidate := key w0 w1 w2 w3
  let _ := keys3.begin
  let _ := keys3.push (key 1 2 3 4)
  let _ := keys3.push (key 5 6 7 8)
  let _ := keys3.push candidate
  keys3.last

/-- Application policy: reject a candidate at full capacity without a word write. -/
@[pf_entry]
def rejectAtFull (_state : State) (_w0 _w1 _w2 _w3 : UInt64) : Pubkey :=
  let _ := keys3.begin
  let _ := keys3.push (key 11 12 13 14)
  let _ := keys3.push (key 21 22 23 24)
  let _ := keys3.push (key 31 32 33 34)
  if keys3.isFull then
    keys3.last
  else
    let _ := keys3.push (key _w0 _w1 _w2 _w3)
    keys3.last

/-- SDK full-capacity gate terminates before any candidate word is written. -/
@[pf_entry]
def overflowAtFull (_state : State) (w0 w1 w2 w3 : UInt64) : UInt64 :=
  let candidate := key w0 w1 w2 w3
  let _ := keys3.begin
  let _ := keys3.push (key 1 2 3 4)
  let _ := keys3.push (key 5 6 7 8)
  let _ := keys3.push (key 9 10 11 12)
  keys3.push candidate

/-- Whole-value replacement and runtime-indexed read. -/
@[pf_entry]
def setAndGet (_state : State) (index w0 w1 w2 w3 : UInt64) : Pubkey :=
  let replacement := key w0 w1 w2 w3
  let _ := keys3.begin
  let _ := keys3.push (key 10 20 30 40)
  let _ := keys3.push (key 50 60 70 80)
  let _ := keys3.set index replacement
  keys3.get index

/-- Typed `last` plus whole-element drop/truncate/clear reuse without a new allocation. -/
@[pf_entry]
def rewindAndReuse (_state : State) (w0 w1 w2 w3 : UInt64) : Pubkey :=
  let candidate := key w0 w1 w2 w3
  let _ := keys3.begin
  let _ := keys3.push (key 7 8 9 10)
  let _ := keys3.push (key 17 18 19 20)
  let _ := keys3.dropLast
  let _ := keys3.truncate 0
  let _ := keys3.push candidate
  let _ := keys3.clear
  let _ := keys3.push (key 17 18 19 20)
  let count := keys3.length
  keys3.get (count - 1)

/-- A runtime index at the live-length boundary fails through Record64/Vector64 bounds. -/
@[pf_entry]
def readAt (_state : State) (index : UInt64) : Pubkey :=
  let _ := keys3.begin
  let _ := keys3.push (key 41 42 43 44)
  let _ := keys3.push (key 51 52 53 54)
  keys3.get index

/-- Two typed handles reuse the existing Vector64 slots and retain disjoint lengths/payloads. -/
@[pf_entry]
def twoSlotIsolation (_state : State) : Pubkey :=
  let _ := keys3.begin
  let _ := keys2Alt.begin
  let _ := keys3.push (key 101 102 103 104)
  let _ := keys2Alt.push (key 201 202 203 204)
  let _ := keys3.set 0 (key 301 302 303 304)
  keys2Alt.get 0

/-- Finish invalidates the typed handle without reclaiming its bump allocation. -/
@[pf_entry]
def staleAfterFinish (_state : State) : UInt64 :=
  let _ := keys3.begin
  let _ := keys3.push (key 1 2 3 4)
  let _ := keys3.finish
  keys3.length

end Examples.Svm.TransientPubkeyBatch
