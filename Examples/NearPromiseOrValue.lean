import ProofForge

namespace Examples.NearPromiseOrValue

open ProofForge.Core.Value
open ProofForge.Wasm.Near.Runtime
open ProofForge.Wasm.Near.Sdk
open ProofForge.Wasm.Near.Sdk.Store

structure State where
  marker : UInt64
  high : UInt64
  deriving Repr, DecidableEq, Inhabited

inductive Error where
  | overflow
  deriving Repr, DecidableEq, Inhabited, BEq

@[pf_entry] def init (high : UInt64) : State := { marker := 0, high }
@[pf_entry] def get (state : State) : UInt64 := state.marker
@[pf_entry] def high (state : State) : UInt64 := state.high

/-- Diagnostic dual terminal. Nonzero input returns an immediate quoted U128; zero schedules and
returns one static child Promise. Both branches persist independent state first. -/
@[pf_entry, pf_near_promise_or_value]
def choose (_state : State) (value : UInt64) : Except Error (State × UInt128) :=
  if value == 0 then
    let promise := Promises.callReturned "receiver.test.near" "recordValue" (borshUInt64 77)
      ({ w0 := 0, w1 := 0 } : NearToken) 20_000_000_000_000
    .ok ({ marker := 9, high := 0x1122334455667788 }, ⟨promise, 0⟩)
  else
    .ok ({ marker := value, high := 0x8877665544332211 },
      ({ w0 := value, w1 := 0x123456789abcdef0 } : UInt128))

end Examples.NearPromiseOrValue
