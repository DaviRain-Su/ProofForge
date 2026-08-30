import ProofForge

namespace Examples.NearPromise

open ProofForge.Core.Value
open ProofForge.Wasm.Near.Runtime
open ProofForge.Wasm.Near.Sdk
open ProofForge.Wasm.Near.Sdk.Store

structure State where
  marker : UInt64
  depositLo : UInt64
  depositHi : UInt64
  deriving Repr, DecidableEq, Inhabited

inductive Error where
  | overflow
  deriving Repr, DecidableEq, Inhabited, BEq

@[pf_inline] private def receiver : String := "receiver.test.near"
@[pf_inline] private def callGas : UInt64 := 20_000_000_000_000
@[pf_inline] private def callbackGas : UInt64 := 20_000_000_000_000
@[pf_inline] private def joinedChildGas : UInt64 := 8_000_000_000_000

@[pf_entry]
def init (_seed : UInt64) : State :=
  { marker := 0, depositLo := 0, depositHi := 0 }

@[pf_entry]
def get (state : State) : UInt64 :=
  state.marker

@[pf_entry]
def receivedDepositLo (state : State) : UInt64 :=
  state.depositLo

@[pf_entry]
def receivedDepositHi (state : State) : UInt64 :=
  state.depositHi

/-- Receiver entry used by the sandbox to pin exact UInt64 argument and u128 deposit staging. -/
@[pf_entry]
def record (_state : State) (value : UInt64) : Except Error (State × UInt64) :=
  let deposit := Context.attachedDeposit
  .ok ({ marker := value, depositLo := deposit.w0, depositHi := deposit.w1 }, value)

/-- Receiver entry whose scalar result is forwarded by `sendReturned`. -/
@[pf_entry]
def recordValue (state : State) (value : UInt64) : Except Error (State × UInt64) :=
  .ok ({ state with marker := value }, value)

/-- Pure child used to observe joined Promise results without coupling receiver state updates. -/
@[pf_entry]
def echo (_state : State) (value : UInt64) : UInt64 :=
  value

/-- Self-callback success branch: child bytes and normal callback input are separate channels. -/
@[pf_entry]
def callbackSuccess (state : State) (callbackValue : UInt64) : Except Error (State × UInt64) :=
  if Access.isSelfCall then
    let result : Promises.ResultBuffer := 8
    let _ := result.read 0
    let childValue := result.borshUInt64D 0
    .ok ({ state with marker := callbackValue }, childValue)
  else
    .error .overflow

/-- Self-callback failure branch: failed dependencies have status 2 and no bytes. -/
@[pf_entry]
def callbackFailure (state : State) (callbackValue : UInt64) : Except Error (State × UInt64) :=
  if Access.isSelfCall then
    let result : Promises.ResultBuffer := 8
    let _ := result.read 0
    let childValue := result.borshUInt64D 999
    .ok ({ state with marker := callbackValue }, childValue)
  else
    .error .overflow

/-- A successful eight-byte child result is intentionally oversized for this four-byte buffer. -/
@[pf_entry]
def callbackOversized (state : State) (callbackValue : UInt64) : Except Error (State × UInt64) :=
  if Access.isSelfCall then
    let result : Promises.ResultBuffer := 4
    let _ := result.read 0
    let childValue := result.borshUInt64D 999
    .ok ({ state with marker := callbackValue }, childValue)
  else
    .error .overflow

/-- Authenticated two-input callback. Reads remain ordered and independent, so one failed child
cannot prevent observation of the other successful child. -/
@[pf_entry]
def callbackJoined (state : State) (callbackValue : UInt64) : Except Error (State × UInt64) :=
  if Access.isSelfCall then
    if Promises.resultsCount == 2 then
      let result : Promises.ResultBuffer := 8
      let _ := result.read 0
      let left := result.borshUInt64D 999
      let _ := result.read 1
      let right := result.borshUInt64D 999
      .ok ({ state with marker := callbackValue, depositLo := left, depositHi := right }, right)
    else
      .error .overflow
  else
    .error .overflow

/-- Schedule a detached native transfer carrying `2^64 + 7` yoctoNEAR. -/
@[pf_entry]
def transferDetached (state : State) (value : UInt64) : Except Error (State × UInt64) :=
  let _ := Promises.transferDetached receiver ({ w0 := 7, w1 := 1 } : NearToken)
  .ok ({ state with marker := value }, value)

/-- Persist caller state and forward a transfer-only receipt carrying 11 yoctoNEAR. -/
@[pf_entry]
def transferReturned (state : State) (value : UInt64) : Except Error (State × UInt64) :=
  let _ := Promises.transferReturned receiver ({ w0 := 11, w1 := 0 } : NearToken)
  .ok ({ state with marker := value }, value)

/-- Synchronous balance validation must abort before this transfer or state update can commit. -/
@[pf_entry]
def transferTooMuch (state : State) (value : UInt64) : Except Error (State × UInt64) :=
  let _ := Promises.transferDetached receiver
    ({ w0 := 0xffffffffffffffff, w1 := 0xffffffffffffffff } : NearToken)
  .ok ({ state with marker := value }, value)

/-- Schedule a detached call carrying `2^64 + 7` yoctoNEAR. -/
@[pf_entry]
def send (state : State) (value : UInt64) : Except Error (State × UInt64) :=
  let _ := Promises.callDetached receiver "record" (borshUInt64 value)
    ({ w0 := 7, w1 := 1 } : NearToken) callGas
  .ok ({ state with marker := value }, value)

@[pf_entry]
def sendZero (state : State) (value : UInt64) : Except Error (State × UInt64) :=
  let _ := Promises.callDetached receiver "record" (borshUInt64 value)
    ({ w0 := 0, w1 := 0 } : NearToken) callGas
  .ok ({ state with marker := value }, value)

/-- Commit caller state and forward the receiver's eventual UInt64 result. -/
@[pf_entry]
def sendReturned (state : State) (value : UInt64) : Except Error (State × UInt64) :=
  let _ := Promises.callReturned receiver "recordValue" (borshUInt64 value)
    ({ w0 := 0, w1 := 0 } : NearToken) callGas
  .ok ({ state with marker := value }, value)

/-- Commit caller state, but surface the absent remote method as the final transaction failure. -/
@[pf_entry]
def sendReturnedMissing (state : State) (value : UInt64) : Except Error (State × UInt64) :=
  let _ := Promises.callReturned receiver "missing" (borshUInt64 value)
    ({ w0 := 0, w1 := 0 } : NearToken) callGas
  .ok ({ state with marker := value }, value)

/-- Return a self callback that sees the successful child's exact eight-byte result. -/
@[pf_entry]
def sendThenSuccess (state : State) (value : UInt64) : Except Error (State × UInt64) :=
  let _ := Promises.callThenReturned receiver "recordValue" (borshUInt64 123)
    ({ w0 := 0, w1 := 0 } : NearToken) callGas
    "callbackSuccess" (borshUInt64 77) ({ w0 := 0, w1 := 0 } : NearToken) callbackGas
  .ok ({ state with marker := value }, value)

/-- A missing child method still resolves the dependency and runs the status-2 callback branch. -/
@[pf_entry]
def sendThenMissing (state : State) (value : UInt64) : Except Error (State × UInt64) :=
  let _ := Promises.callThenReturned receiver "missing" (borshUInt64 124)
    ({ w0 := 0, w1 := 0 } : NearToken) callGas
    "callbackFailure" (borshUInt64 78) ({ w0 := 0, w1 := 0 } : NearToken) callbackGas
  .ok ({ state with marker := value }, value)

/-- The callback observes actual length eight without copying into its four-byte result buffer. -/
@[pf_entry]
def sendThenOversized (state : State) (value : UInt64) : Except Error (State × UInt64) :=
  let _ := Promises.callThenReturned receiver "recordValue" (borshUInt64 456)
    ({ w0 := 0, w1 := 0 } : NearToken) callGas
    "callbackOversized" (borshUInt64 79) ({ w0 := 0, w1 := 0 } : NearToken) callbackGas
  .ok ({ state with marker := value }, value)

/-- Join two successful ordered child calls, then return the self callback receipt. -/
@[pf_entry]
def sendAndSuccess (state : State) (value : UInt64) : Except Error (State × UInt64) :=
  let _ := Promises.callAndThenReturned
    receiver "echo" (borshUInt64 123) ({ w0 := 0, w1 := 0 } : NearToken) joinedChildGas
    receiver "echo" (borshUInt64 456) ({ w0 := 0, w1 := 0 } : NearToken) joinedChildGas
    "callbackJoined" (borshUInt64 80) ({ w0 := 0, w1 := 0 } : NearToken) callbackGas
  .ok ({ state with marker := value }, value)

/-- A failed right child retains left/right callback-result ordering. -/
@[pf_entry]
def sendAndRightMissing (state : State) (value : UInt64) : Except Error (State × UInt64) :=
  let _ := Promises.callAndThenReturned
    receiver "echo" (borshUInt64 123) ({ w0 := 0, w1 := 0 } : NearToken) joinedChildGas
    receiver "missing" (borshUInt64 456) ({ w0 := 0, w1 := 0 } : NearToken) joinedChildGas
    "callbackJoined" (borshUInt64 81) ({ w0 := 0, w1 := 0 } : NearToken) callbackGas
  .ok ({ state with marker := value }, value)

/-- A failed left child does not short-circuit the successful right child read. -/
@[pf_entry]
def sendAndLeftMissing (state : State) (value : UInt64) : Except Error (State × UInt64) :=
  let _ := Promises.callAndThenReturned
    receiver "missing" (borshUInt64 123) ({ w0 := 0, w1 := 0 } : NearToken) joinedChildGas
    receiver "echo" (borshUInt64 456) ({ w0 := 0, w1 := 0 } : NearToken) joinedChildGas
    "callbackJoined" (borshUInt64 82) ({ w0 := 0, w1 := 0 } : NearToken) callbackGas
  .ok ({ state with marker := value }, value)

/-- The caller succeeds while this detached receipt fails remotely on an absent method. -/
@[pf_entry]
def sendMissing (state : State) (value : UInt64) : Except Error (State × UInt64) :=
  let _ := Promises.callDetached receiver "missing" (borshUInt64 value)
    ({ w0 := 0, w1 := 0 } : NearToken) callGas
  .ok ({ state with marker := value }, value)

/-- A caller trap after scheduling must discard the staged outgoing receipt. -/
@[pf_entry]
def sendThenFail (_state : State) (value : UInt64) : Except Error (State × UInt64) :=
  let _ := Promises.callDetached receiver "record" (borshUInt64 value)
    ({ w0 := 0, w1 := 0 } : NearToken) callGas
  .error .overflow

/-- Synchronous balance validation must abort before this state update can commit. -/
@[pf_entry]
def sendTooMuch (state : State) (value : UInt64) : Except Error (State × UInt64) :=
  let _ := Promises.callDetached receiver "record" (borshUInt64 value)
    ({ w0 := 0xffffffffffffffff, w1 := 0xffffffffffffffff } : NearToken) callGas
  .ok ({ state with marker := value }, value)

end Examples.NearPromise
