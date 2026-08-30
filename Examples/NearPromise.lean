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
