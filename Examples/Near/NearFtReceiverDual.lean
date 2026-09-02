import ProofForge

namespace Examples.Near.NearFtReceiverDual
open ProofForge.Core.Value
open ProofForge.Wasm.Near.Runtime
open ProofForge.Wasm.Near.Sdk
open ProofForge.Wasm.Near.Sdk.Store

structure State where
  calls : UInt64
  lastMsgLength : UInt64
  deriving Repr, DecidableEq, Inhabited

inductive Error where
  | overflow
  deriving Repr, DecidableEq, Inhabited, BEq

@[pf_entry] def init : State := { calls := 0, lastMsgLength := 0 }
@[pf_entry] def get (state : State) : UInt64 := state.calls
@[pf_entry] def lastMsgLength (state : State) : UInt64 := state.lastMsgLength
@[pf_entry] def fixtureSetCallsMax (_state : State) : Except Error (State × UInt64) :=
  .ok ({ calls := 18446744073709551615, lastMsgLength := 63 }, 0)

/-- Standards-shaped receiver diagnostic with a genuine runtime `PromiseOrValue<U128>` choice.
Message lengths 0/1/2 return full/zero/three unused tokens immediately. Lengths 3/4/≥5 return
successful-three/failed/malformed child receipts. The bounded input remains narrower than serde. -/
@[pf_entry, pf_near_promise_or_value]
def ft_on_transfer (state : State) (args : FtOnTransferArgs) : Except Error (State × UInt128) :=
  if state.calls < 18446744073709551615 then
    let next : State := { calls := state.calls + 1, lastMsgLength := args.msg.length }
    if args.msg.length == 0 then
      .ok (next, ⟨args.amount.w0, args.amount.w1⟩)
    else if args.msg.length == 1 then
      .ok (next, ⟨0, 0⟩)
    else if args.msg.length == 2 then
      .ok (next, ⟨3, 0⟩)
    else if args.msg.length == 3 then
      let promise := Promises.callReturned "json-result.test.near" "unusedThree" (borshUInt64 0)
        ({ w0 := 0, w1 := 0 } : NearToken) 20_000_000_000_000
      .ok (next, ⟨promise, 0⟩)
    else if args.msg.length == 4 then
      let promise := Promises.callReturned "json-result.test.near" "failed" (borshUInt64 0)
        ({ w0 := 0, w1 := 0 } : NearToken) 20_000_000_000_000
      .ok (next, ⟨promise, 0⟩)
    else
      let promise := Promises.callReturned "json-result.test.near" "malformed" (borshUInt64 0)
        ({ w0 := 0, w1 := 0 } : NearToken) 20_000_000_000_000
      .ok (next, ⟨promise, 0⟩)
  else .error .overflow

end Examples.Near.NearFtReceiverDual