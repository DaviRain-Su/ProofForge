import ProofForge

namespace Examples.NearPromiseHandle

open ProofForge.Core.Value
open ProofForge.Wasm.Near.Runtime
open ProofForge.Wasm.Near.Sdk
open ProofForge.Wasm.Near.Sdk.Store

structure State where
  marker : UInt64
  depth : UInt64
  deriving Repr, DecidableEq, Inhabited

inductive Error where
  | depth
  deriving Repr, DecidableEq, Inhabited, BEq

@[pf_inline] private def receiver : String := "receiver.test.near"
@[pf_inline] private def callGas : UInt64 := 20_000_000_000_000
@[pf_inline] private def callbackGas : UInt64 := 20_000_000_000_000

@[pf_entry]
def init (_seed : UInt64) : State :=
  { marker := 0, depth := 0 }

@[pf_entry]
def get (state : State) : UInt64 :=
  state.marker

@[pf_entry]
def trackedDepth (state : State) : UInt64 :=
  state.depth

/-- Private callback reused from the NearPromise fixture pattern. -/
@[pf_entry, pf_near_private]
def callbackSuccess (state : State) (callbackValue : UInt64) : Except Error (State × UInt64) :=
  let result : Promises.ResultBuffer := 8
  let _ := result.read 0
  let childValue := result.borshUInt64D 0
  .ok ({ state with marker := callbackValue }, childValue)

/-- Same DAG as `NearPromise.sendThenSuccess`; persisted depth models N13 handle metadata. -/
@[pf_entry]
def sendHandleThen (state : State) (value : UInt64) : Except Error (State × UInt64) :=
  let _ := Promises.callThenReturned receiver "recordValue" (borshUInt64 123)
    ({ w0 := 0, w1 := 0 } : NearToken) callGas
    "callbackSuccess" (borshUInt64 77) ({ w0 := 0, w1 := 0 } : NearToken) callbackGas
  .ok ({ state with marker := value, depth := 1 }, value)

/-- SDK-only smoke for `PromiseHandle` depth tracking; not extracted into target IR. -/
def handleDepthSmoke : Bool :=
  let root := Promises.PromiseHandle.createReturned receiver "recordValue" (borshUInt64 0)
    ({ w0 := 0, w1 := 0 } : NearToken) callGas
  let chained := root.thenReturned receiver "recordValue" (borshUInt64 0)
    ({ w0 := 0, w1 := 0 } : NearToken) callGas
    "callbackSuccess" (borshUInt64 0) ({ w0 := 0, w1 := 0 } : NearToken) callbackGas
  root.depthOk && chained.depthOk && chained.depth.toNat == 1

#guard handleDepthSmoke

end Examples.NearPromiseHandle
