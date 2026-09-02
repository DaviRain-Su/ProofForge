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

@[pf_inline] private def joinedChildGas : UInt64 := 8_000_000_000_000

/-- Zero-cost root handle for extracted entries; real scheduling happens in `thenReturned` / `and3Returned`. -/
@[pf_inline] private def promiseRoot : Promises.PromiseHandle :=
  { id := 0, depth := 0, fanIn := 0 }

/-- Fan-in 5 root for `and5Returned` entry bodies (`defaultMaxFanIn` is 4). -/
@[pf_inline] private def promiseRoot5 : Promises.PromiseHandle 5 :=
  { id := 0, depth := 0, fanIn := 0 }

/-- Fan-in 6 root for `and6Returned` entry bodies (`defaultMaxFanIn` is 4). -/
private def promiseRoot6 : Promises.PromiseHandle 6 :=
  { id := 0, depth := 0, fanIn := 0 }

/-- Fan-in 7 root for `and7Returned` entry bodies (`defaultMaxFanIn` is 4). -/
private def promiseRoot7 : Promises.PromiseHandle 7 :=
  { id := 0, depth := 0, fanIn := 0 }

/-- Fan-in 8 root for `and8Returned` entry bodies (`defaultMaxFanIn` is 4). -/
private def promiseRoot8 : Promises.PromiseHandle 8 :=
  { id := 0, depth := 0, fanIn := 0 }

/-- Pure child used by join fixtures to observe echoed UInt64 results. -/
@[pf_entry]
def echo (_state : State) (value : UInt64) : UInt64 :=
  value

/-- Same DAG as `NearPromise.sendAnd8Success`; uses `promiseRoot8` for fan-in 8. -/
@[pf_entry]
def sendHandleAnd8 (state : State) (value : UInt64) : Except Error (State × UInt64) :=
  let _ := promiseRoot8.and8Returned
    receiver "echo" (borshUInt64 111) ({ w0 := 0, w1 := 0 } : NearToken) joinedChildGas
    receiver "echo" (borshUInt64 222) ({ w0 := 0, w1 := 0 } : NearToken) joinedChildGas
    receiver "echo" (borshUInt64 333) ({ w0 := 0, w1 := 0 } : NearToken) joinedChildGas
    receiver "echo" (borshUInt64 444) ({ w0 := 0, w1 := 0 } : NearToken) joinedChildGas
    receiver "echo" (borshUInt64 555) ({ w0 := 0, w1 := 0 } : NearToken) joinedChildGas
    receiver "echo" (borshUInt64 666) ({ w0 := 0, w1 := 0 } : NearToken) joinedChildGas
    receiver "echo" (borshUInt64 777) ({ w0 := 0, w1 := 0 } : NearToken) joinedChildGas
    receiver "echo" (borshUInt64 888) ({ w0 := 0, w1 := 0 } : NearToken) joinedChildGas
    "callbackSuccess" (borshUInt64 93) ({ w0 := 0, w1 := 0 } : NearToken) callbackGas
  .ok ({ state with marker := value, depth := 1 }, value)

/-- Same DAG as `NearPromise.sendAnd7Success`; uses `promiseRoot7` for fan-in 7. -/
@[pf_entry]
def sendHandleAnd7 (state : State) (value : UInt64) : Except Error (State × UInt64) :=
  let _ := promiseRoot7.and7Returned
    receiver "echo" (borshUInt64 111) ({ w0 := 0, w1 := 0 } : NearToken) joinedChildGas
    receiver "echo" (borshUInt64 222) ({ w0 := 0, w1 := 0 } : NearToken) joinedChildGas
    receiver "echo" (borshUInt64 333) ({ w0 := 0, w1 := 0 } : NearToken) joinedChildGas
    receiver "echo" (borshUInt64 444) ({ w0 := 0, w1 := 0 } : NearToken) joinedChildGas
    receiver "echo" (borshUInt64 555) ({ w0 := 0, w1 := 0 } : NearToken) joinedChildGas
    receiver "echo" (borshUInt64 666) ({ w0 := 0, w1 := 0 } : NearToken) joinedChildGas
    receiver "echo" (borshUInt64 777) ({ w0 := 0, w1 := 0 } : NearToken) joinedChildGas
    "callbackSuccess" (borshUInt64 91) ({ w0 := 0, w1 := 0 } : NearToken) callbackGas
  .ok ({ state with marker := value, depth := 1 }, value)

/-- Same DAG as `NearPromise.sendAnd6Success`; uses `promiseRoot6` for fan-in 6. -/
@[pf_entry]
def sendHandleAnd6 (state : State) (value : UInt64) : Except Error (State × UInt64) :=
  let _ := promiseRoot6.and6Returned
    receiver "echo" (borshUInt64 111) ({ w0 := 0, w1 := 0 } : NearToken) joinedChildGas
    receiver "echo" (borshUInt64 222) ({ w0 := 0, w1 := 0 } : NearToken) joinedChildGas
    receiver "echo" (borshUInt64 333) ({ w0 := 0, w1 := 0 } : NearToken) joinedChildGas
    receiver "echo" (borshUInt64 444) ({ w0 := 0, w1 := 0 } : NearToken) joinedChildGas
    receiver "echo" (borshUInt64 555) ({ w0 := 0, w1 := 0 } : NearToken) joinedChildGas
    receiver "echo" (borshUInt64 666) ({ w0 := 0, w1 := 0 } : NearToken) joinedChildGas
    "callbackSuccess" (borshUInt64 89) ({ w0 := 0, w1 := 0 } : NearToken) callbackGas
  .ok ({ state with marker := value, depth := 1 }, value)

/-- Same DAG as `NearPromise.sendAnd5Success`; uses `promiseRoot5` for fan-in 5. -/
@[pf_entry]
def sendHandleAnd5 (state : State) (value : UInt64) : Except Error (State × UInt64) :=
  let _ := promiseRoot5.and5Returned
    receiver "echo" (borshUInt64 111) ({ w0 := 0, w1 := 0 } : NearToken) joinedChildGas
    receiver "echo" (borshUInt64 222) ({ w0 := 0, w1 := 0 } : NearToken) joinedChildGas
    receiver "echo" (borshUInt64 333) ({ w0 := 0, w1 := 0 } : NearToken) joinedChildGas
    receiver "echo" (borshUInt64 444) ({ w0 := 0, w1 := 0 } : NearToken) joinedChildGas
    receiver "echo" (borshUInt64 555) ({ w0 := 0, w1 := 0 } : NearToken) joinedChildGas
    "callbackSuccess" (borshUInt64 87) ({ w0 := 0, w1 := 0 } : NearToken) callbackGas
  .ok ({ state with marker := value, depth := 1 }, value)

/-- Same DAG as `NearPromise.sendAnd4Success`; persisted depth models N13 handle metadata. -/
@[pf_entry]
def sendHandleAnd4 (state : State) (value : UInt64) : Except Error (State × UInt64) :=
  let _ := promiseRoot.and4Returned
    receiver "echo" (borshUInt64 111) ({ w0 := 0, w1 := 0 } : NearToken) joinedChildGas
    receiver "echo" (borshUInt64 222) ({ w0 := 0, w1 := 0 } : NearToken) joinedChildGas
    receiver "echo" (borshUInt64 333) ({ w0 := 0, w1 := 0 } : NearToken) joinedChildGas
    receiver "echo" (borshUInt64 444) ({ w0 := 0, w1 := 0 } : NearToken) joinedChildGas
    "callbackSuccess" (borshUInt64 85) ({ w0 := 0, w1 := 0 } : NearToken) callbackGas
  .ok ({ state with marker := value, depth := 1 }, value)

/-- Same DAG as `NearPromise.sendAnd3Success`; persisted depth models N13 handle metadata. -/
@[pf_entry]
def sendHandleAnd3 (state : State) (value : UInt64) : Except Error (State × UInt64) :=
  let _ := promiseRoot.and3Returned
    receiver "echo" (borshUInt64 111) ({ w0 := 0, w1 := 0 } : NearToken) joinedChildGas
    receiver "echo" (borshUInt64 222) ({ w0 := 0, w1 := 0 } : NearToken) joinedChildGas
    receiver "echo" (borshUInt64 333) ({ w0 := 0, w1 := 0 } : NearToken) joinedChildGas
    "callbackSuccess" (borshUInt64 83) ({ w0 := 0, w1 := 0 } : NearToken) callbackGas
  .ok ({ state with marker := value, depth := 1 }, value)

/-- Same DAG as `NearPromise.sendThenSuccess`; persisted depth models N13 handle metadata. -/
@[pf_entry]
def sendHandleThen (state : State) (value : UInt64) : Except Error (State × UInt64) :=
  let _ := promiseRoot.thenReturned receiver "recordValue" (borshUInt64 123)
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

-- Compile-time maxFanIn ceiling: ladder supports 4..8, rejects 9+.
#guard Promises.maxFanInWithinCeiling Promises.defaultMaxFanIn
#guard Promises.maxFanInWithinCeiling 6
#guard Promises.maxFanInWithinCeiling Promises.maxFanInCompileCeiling
#guard (Promises.maxFanInWithinCeiling 9) == false

-- Custom PromiseHandle 6 can join six edges and stays within the compile ceiling.
def handleFanInSmoke : Bool :=
  let root : Promises.PromiseHandle 6 := {
    id := Promises.callReturned receiver "recordValue" (borshUInt64 0)
      ({ w0 := 0, w1 := 0 } : NearToken) callGas
    depth := 0
    fanIn := 0
  }
  let joined := root.and6Returned
    receiver "echo" (borshUInt64 1) ({ w0 := 0, w1 := 0 } : NearToken) joinedChildGas
    receiver "echo" (borshUInt64 2) ({ w0 := 0, w1 := 0 } : NearToken) joinedChildGas
    receiver "echo" (borshUInt64 3) ({ w0 := 0, w1 := 0 } : NearToken) joinedChildGas
    receiver "echo" (borshUInt64 4) ({ w0 := 0, w1 := 0 } : NearToken) joinedChildGas
    receiver "echo" (borshUInt64 5) ({ w0 := 0, w1 := 0 } : NearToken) joinedChildGas
    receiver "echo" (borshUInt64 6) ({ w0 := 0, w1 := 0 } : NearToken) joinedChildGas
    "callbackSuccess" (borshUInt64 0) ({ w0 := 0, w1 := 0 } : NearToken) callbackGas
  root.withinCompileCeiling && joined.withinCompileCeiling && joined.fanInOk && joined.fanIn.toNat == 6

#guard handleFanInSmoke

-- and3Returned ladder smoke (SDK + Extract entry bodies use `promiseRoot.and3Returned`).
def handleAnd3Smoke : Bool :=
  let joined := promiseRoot.and3Returned
    receiver "echo" (borshUInt64 1) ({ w0 := 0, w1 := 0 } : NearToken) joinedChildGas
    receiver "echo" (borshUInt64 2) ({ w0 := 0, w1 := 0 } : NearToken) joinedChildGas
    receiver "echo" (borshUInt64 3) ({ w0 := 0, w1 := 0 } : NearToken) joinedChildGas
    "callbackSuccess" (borshUInt64 0) ({ w0 := 0, w1 := 0 } : NearToken) callbackGas
  joined.fanInOk && joined.fanIn.toNat == 3

#guard handleAnd3Smoke

def handleAnd5Smoke : Bool :=
  let joined := promiseRoot5.and5Returned
    receiver "echo" (borshUInt64 1) ({ w0 := 0, w1 := 0 } : NearToken) joinedChildGas
    receiver "echo" (borshUInt64 2) ({ w0 := 0, w1 := 0 } : NearToken) joinedChildGas
    receiver "echo" (borshUInt64 3) ({ w0 := 0, w1 := 0 } : NearToken) joinedChildGas
    receiver "echo" (borshUInt64 4) ({ w0 := 0, w1 := 0 } : NearToken) joinedChildGas
    receiver "echo" (borshUInt64 5) ({ w0 := 0, w1 := 0 } : NearToken) joinedChildGas
    "callbackSuccess" (borshUInt64 0) ({ w0 := 0, w1 := 0 } : NearToken) callbackGas
  joined.fanInOk && joined.fanIn.toNat == 5

#guard handleAnd5Smoke

def handleAnd8Smoke : Bool :=
  let joined := promiseRoot8.and8Returned
    receiver "echo" (borshUInt64 1) ({ w0 := 0, w1 := 0 } : NearToken) joinedChildGas
    receiver "echo" (borshUInt64 2) ({ w0 := 0, w1 := 0 } : NearToken) joinedChildGas
    receiver "echo" (borshUInt64 3) ({ w0 := 0, w1 := 0 } : NearToken) joinedChildGas
    receiver "echo" (borshUInt64 4) ({ w0 := 0, w1 := 0 } : NearToken) joinedChildGas
    receiver "echo" (borshUInt64 5) ({ w0 := 0, w1 := 0 } : NearToken) joinedChildGas
    receiver "echo" (borshUInt64 6) ({ w0 := 0, w1 := 0 } : NearToken) joinedChildGas
    receiver "echo" (borshUInt64 7) ({ w0 := 0, w1 := 0 } : NearToken) joinedChildGas
    receiver "echo" (borshUInt64 8) ({ w0 := 0, w1 := 0 } : NearToken) joinedChildGas
    "callbackSuccess" (borshUInt64 0) ({ w0 := 0, w1 := 0 } : NearToken) callbackGas
  joined.fanInOk && joined.fanIn.toNat == 8

#guard handleAnd8Smoke

end Examples.NearPromiseHandle
