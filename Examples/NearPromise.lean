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
@[pf_inline] private def jsonResultReceiver : String := "json-result.test.near"
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

/-- Fixture-only setters let the sandbox exercise arbitrary two-limb FT amounts without baking
one amount into the specialized Promise operation. -/
@[pf_entry]
def setFtAmountLo (state : State) (value : UInt64) : Except Error (State × UInt64) :=
  .ok ({ state with depositLo := value }, value)

@[pf_entry]
def setFtAmountHi (state : State) (value : UInt64) : Except Error (State × UInt64) :=
  .ok ({ state with depositHi := value }, value)

/-- Return one weighted `ft_on_transfer` receipt to the padded dynamic receiver. The exact child
JSON is target-owned; this nonstandard fixture is not an `ft_transfer_call` implementation. -/
@[pf_entry]
def inspectFtOnTransfer (state : State) (msg : BoundedMessage64) : Except Error (State × UInt64) :=
  -- Inactive carrier padding is intentionally nonzero. Only the first 18 bytes encode
  -- `observer.test.near` and may reach `promise_batch_create`.
  let target : ProofForge.Wasm.Near.Runtime.AccountId :=
    ⟨18, 0x726576726573626f, 0x656e2e747365742e, 0xa5a5a5a5a5a57261,
      0x1111111111111111, 0x2222222222222222, 0x3333333333333333,
      0x4444444444444444, 0x5555555555555555⟩
  let _ := Promises.ftOnTransferReturned target Context.caller
    ({ w0 := state.depositLo, w1 := state.depositHi } : NearToken)
    msg
  .ok ({ state with marker := msg.length }, msg.length)

/-- Return a child call to an absent dynamic account. Promise creation is synchronous and succeeds;
the returned child receipt fails asynchronously after this caller receipt has persisted state. -/
@[pf_entry]
def inspectFtOnTransferMissing
    (state : State) (msg : BoundedMessage64) : Except Error (State × UInt64) :=
  let target : ProofForge.Wasm.Near.Runtime.AccountId :=
    ⟨17, 0x2e676e697373696d, 0x61656e2e74736574, 0x72, 0, 0, 0, 0, 0⟩
  let _ := Promises.ftOnTransferReturned target Context.caller
    ({ w0 := state.depositLo, w1 := state.depositHi } : NearToken)
    msg
  .ok ({ state with marker := msg.length }, msg.length)

/-- Nonstandard fixture for the fixed receiver→resolver DAG; no FT ledger mutation is implied. -/
@[pf_entry]
def inspectFtOnTransferThenResolve
    (state : State) (msg : BoundedMessage64) : Except Error (State × UInt64) :=
  let target : ProofForge.Wasm.Near.Runtime.AccountId :=
    ⟨18, 0x726576726573626f, 0x656e2e747365742e, 0x7261, 0, 0, 0, 0, 0⟩
  let _ := Promises.ftOnTransferThenResolveReturned target Context.caller
    ({ w0 := state.depositLo, w1 := state.depositHi } : NearToken) msg
  .ok ({ state with marker := msg.length }, msg.length)

/-- Private diagnostic callback matching the specialized operation's fixed method and JSON schema. -/
@[pf_entry, pf_near_private]
def ft_resolve_transfer (state : State) (args : FtResolveTransferArgs) :
    Except Error (State × UInt128) :=
  .ok ({ state with marker := args.receiverId.length },
    ({ w0 := state.depositLo, w1 := state.depositHi } : UInt128))

/-- Receiver entry used by the sandbox to pin exact UInt64 argument and u128 deposit staging. -/
@[pf_entry]
def record (_state : State) (value : UInt64) : Except Error (State × UInt64) :=
  let deposit := Context.attachedDeposit
  .ok ({ marker := value, depositLo := deposit.w0, depositHi := deposit.w1 }, value)

/-- Receiver entry whose scalar result is forwarded by `sendReturned`. Explicit payable metadata
permits attached donations without forcing the body to observe their amount. -/
@[pf_entry, pf_near_payable]
def recordValue (state : State) (value : UInt64) : Except Error (State × UInt64) :=
  .ok ({ state with marker := value }, value)

/-- Pure child used to observe joined Promise results without coupling receiver state updates. -/
@[pf_entry]
def echo (_state : State) (value : UInt64) : UInt64 :=
  value

/-- Self-callback success branch: child bytes and normal callback input are separate channels. -/
@[pf_entry, pf_near_private]
def callbackSuccess (state : State) (callbackValue : UInt64) : Except Error (State × UInt64) :=
  let result : Promises.ResultBuffer := 8
  let _ := result.read 0
  let childValue := result.borshUInt64D 0
  .ok ({ state with marker := callbackValue }, childValue)

/-- Self-callback failure branch: failed dependencies have status 2 and no bytes. -/
@[pf_entry, pf_near_private]
def callbackFailure (state : State) (callbackValue : UInt64) : Except Error (State × UInt64) :=
  let result : Promises.ResultBuffer := 8
  let _ := result.read 0
  let childValue := result.borshUInt64D 999
  .ok ({ state with marker := callbackValue }, childValue)

/-- A successful eight-byte child result is intentionally oversized for this four-byte buffer. -/
@[pf_entry, pf_near_private]
def callbackOversized (state : State) (callbackValue : UInt64) : Except Error (State × UInt64) :=
  let result : Promises.ResultBuffer := 4
  let _ := result.read 0
  let childValue := result.borshUInt64D 999
  .ok ({ state with marker := callbackValue }, childValue)

/-- Authenticated two-input callback. Reads remain ordered and independent, so one failed child
cannot prevent observation of the other successful child. -/
@[pf_entry, pf_near_private]
def callbackJoined (state : State) (callbackValue : UInt64) : Except Error (State × UInt64) :=
  if Promises.resultsCount == 2 then
    let result : Promises.ResultBuffer := 8
    let _ := result.read 0
    let left := result.borshUInt64D 999
    let _ := result.read 1
    let right := result.borshUInt64D 999
    .ok ({ state with marker := callbackValue, depositLo := left, depositHi := right }, right)
  else
    .error .overflow

/-- Authenticated three-input callback. Reads remain ordered and independent. -/
@[pf_entry, pf_near_private]
def callbackJoined3 (state : State) (callbackValue : UInt64) : Except Error (State × UInt64) :=
  if Promises.resultsCount == 3 then
    let result : Promises.ResultBuffer := 8
    let _ := result.read 0
    let left := result.borshUInt64D 999
    let _ := result.read 1
    let mid := result.borshUInt64D 999
    let _ := result.read 2
    let right := result.borshUInt64D 999
    .ok ({ state with marker := callbackValue, depositLo := left, depositHi := mid }, right)
  else
    .error .overflow

/-- Authenticated four-input callback. Reads remain ordered and independent. -/
@[pf_entry, pf_near_private]
def callbackJoined4 (state : State) (callbackValue : UInt64) : Except Error (State × UInt64) :=
  if Promises.resultsCount == 4 then
    let result : Promises.ResultBuffer := 8
    let _ := result.read 0
    let left := result.borshUInt64D 999
    let _ := result.read 1
    let mid := result.borshUInt64D 999
    let _ := result.read 2
    let _ := result.borshUInt64D 999
    let _ := result.read 3
    let fourth := result.borshUInt64D 999
    .ok ({ state with marker := callbackValue, depositLo := left, depositHi := mid }, fourth)
  else
    .error .overflow

/-- Authenticated five-input callback. Reads remain ordered and independent. -/
@[pf_entry, pf_near_private]
def callbackJoined5 (state : State) (callbackValue : UInt64) : Except Error (State × UInt64) :=
  if Promises.resultsCount == 5 then
    let result : Promises.ResultBuffer := 8
    let _ := result.read 0
    let left := result.borshUInt64D 999
    let _ := result.read 1
    let mid := result.borshUInt64D 999
    let _ := result.read 2
    let _ := result.borshUInt64D 999
    let _ := result.read 3
    let _ := result.borshUInt64D 999
    let _ := result.read 4
    let fifth := result.borshUInt64D 999
    .ok ({ state with marker := callbackValue, depositLo := left, depositHi := mid }, fifth)
  else
    .error .overflow

/-- Diagnostic callback for the strict standalone quoted-u128 result codec. This callback owns the
exact one-result guard and index zero read. Status is returned while validity and both limbs are persisted
for sandbox observation; this is not the FT resolver. -/
@[pf_entry, pf_near_private]
def callbackQuotedU128 (state : State) (_callbackValue : UInt64) : Except Error (State × UInt64) :=
  if Promises.resultsCount == 1 then
    let buffer : Promises.ResultBuffer := 41
    let _ := buffer.read 0
    let result := buffer.quotedU128
    .ok ({ state with marker := result.valid, depositLo := result.w0, depositHi := result.w1 },
      result.status)
  else
    .ok ({ state with marker := 0, depositLo := 0, depositHi := 0 }, 0)

@[pf_inline] private def callQuotedResult
    (childMethod : String) (callbackValue : UInt64) : UInt64 :=
  Promises.callThenReturned jsonResultReceiver childMethod (borshUInt64 0)
    ({ w0 := 0, w1 := 0 } : NearToken) callGas
    "callbackQuotedU128" (borshUInt64 callbackValue)
    ({ w0 := 0, w1 := 0 } : NearToken) callbackGas

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

/-- Transfer to the complete dynamic predecessor AccountId without returning the child receipt. -/
@[pf_entry]
def transferCallerDetached (state : State) (value : UInt64) : Except Error (State × UInt64) :=
  let _ := Promises.transferAccountDetached Context.caller ({ w0 := 13, w1 := 0 } : NearToken)
  .ok ({ state with marker := value }, value)

/-- Transfer to the complete dynamic predecessor AccountId and return the exact created receipt. -/
@[pf_entry]
def transferCallerReturned (state : State) (value : UInt64) : Except Error (State × UInt64) :=
  let _ := Promises.transferAccountReturned Context.caller ({ w0 := 17, w1 := 0 } : NearToken)
  .ok ({ state with marker := value }, value)

/-- Exercise the complete dynamic current-account carrier without creating a distinct identity. -/
@[pf_entry]
def transferSelfDetached (state : State) (value : UInt64) : Except Error (State × UInt64) :=
  let _ := Promises.transferAccountDetached Context.self ({ w0 := 0, w1 := 0 } : NearToken)
  .ok ({ state with marker := value }, value)

/-- Structural minimum-geometry fixture. The synthetic receiver need not exist in the sandbox. -/
@[pf_entry]
def transferShortDetached (state : State) (value : UInt64) : Except Error (State × UInt64) :=
  let shortReceiver : ProofForge.Wasm.Near.Runtime.AccountId :=
    ⟨2, 0x6161, 0, 0, 0, 0, 0, 0, 0⟩
  let _ := Promises.transferAccountDetached shortReceiver ({ w0 := 0, w1 := 0 } : NearToken)
  .ok ({ state with marker := value }, value)

/-- Fixture-only receiver with nonzero bytes above length, including within its last active limb.
Only the first 18 bytes encode `receiver.test.near`; inactive carrier padding is not identity. -/
@[pf_entry]
def transferPaddedDetached (state : State) (value : UInt64) : Except Error (State × UInt64) :=
  let dynamicReceiver : ProofForge.Wasm.Near.Runtime.AccountId :=
    ⟨18, 0x7265766965636572, 0x656e2e747365742e, 0xdeadbeefcafe7261,
      0x1111111111111111, 0x2222222222222222, 0x3333333333333333,
      0x4444444444444444, 0x5555555555555555⟩
  let _ := Promises.transferAccountDetached dynamicReceiver ({ w0 := 19, w1 := 0 } : NearToken)
  .ok ({ state with marker := value }, value)

/-- Structural maximum-geometry/high-limb fixture. Sandbox does not execute the unaffordable
amount or require the synthetic 64-byte account to exist. -/
@[pf_entry]
def transferMaxAccountReturned (state : State) (value : UInt64) : Except Error (State × UInt64) :=
  let maxReceiver : ProofForge.Wasm.Near.Runtime.AccountId :=
    ⟨64, 0x6161616161616161, 0x6161616161616161, 0x6161616161616161,
      0x6161616161616161, 0x6161616161616161, 0x6161616161616161,
      0x6161616161616161, 0x6161616161616161⟩
  let _ := Promises.transferAccountReturned maxReceiver
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

/-- Fixture-only child result scenes for the closed quoted-u128 decoder. -/
@[pf_entry] def decodeJsonZero (state : State) (value : UInt64) : Except Error (State × UInt64) :=
  let _ := callQuotedResult "jsonZero" value
  .ok ({ state with marker := value }, value)

@[pf_entry] def decodeJsonHigh (state : State) (value : UInt64) : Except Error (State × UInt64) :=
  let _ := callQuotedResult "jsonHigh" value
  .ok ({ state with marker := value }, value)

@[pf_entry] def decodeJsonMixed (state : State) (value : UInt64) : Except Error (State × UInt64) :=
  let _ := callQuotedResult "jsonMixed" value
  .ok ({ state with marker := value }, value)

@[pf_entry] def decodeJsonMax (state : State) (value : UInt64) : Except Error (State × UInt64) :=
  let _ := callQuotedResult "jsonMax" value
  .ok ({ state with marker := value }, value)

@[pf_entry] def decodeJsonLeadingZero (state : State) (value : UInt64) : Except Error (State × UInt64) :=
  let _ := callQuotedResult "jsonLeadingZero" value
  .ok ({ state with marker := value }, value)

@[pf_entry] def decodeJsonPlus (state : State) (value : UInt64) : Except Error (State × UInt64) :=
  let _ := callQuotedResult "jsonPlus" value
  .ok ({ state with marker := value }, value)

@[pf_entry] def decodeJsonWhitespace (state : State) (value : UInt64) : Except Error (State × UInt64) :=
  let _ := callQuotedResult "jsonWhitespace" value
  .ok ({ state with marker := value }, value)

@[pf_entry] def decodeJsonUnquoted (state : State) (value : UInt64) : Except Error (State × UInt64) :=
  let _ := callQuotedResult "jsonUnquoted" value
  .ok ({ state with marker := value }, value)

@[pf_entry] def decodeJsonOverflow (state : State) (value : UInt64) : Except Error (State × UInt64) :=
  let _ := callQuotedResult "jsonOverflow" value
  .ok ({ state with marker := value }, value)

@[pf_entry] def decodeJsonWrongType (state : State) (value : UInt64) : Except Error (State × UInt64) :=
  let _ := callQuotedResult "jsonWrongType" value
  .ok ({ state with marker := value }, value)

@[pf_entry] def decodeJsonEmpty (state : State) (value : UInt64) : Except Error (State × UInt64) :=
  let _ := callQuotedResult "jsonEmpty" value
  .ok ({ state with marker := value }, value)

@[pf_entry] def decodeJsonMalformedUtf8 (state : State) (value : UInt64) : Except Error (State × UInt64) :=
  let _ := callQuotedResult "jsonMalformedUtf8" value
  .ok ({ state with marker := value }, value)

@[pf_entry] def decodeJsonOversized (state : State) (value : UInt64) : Except Error (State × UInt64) :=
  let _ := callQuotedResult "jsonOversized" value
  .ok ({ state with marker := value }, value)

@[pf_entry] def decodeJsonFailed (state : State) (value : UInt64) : Except Error (State × UInt64) :=
  let _ := callQuotedResult "jsonFailed" value
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

/-- Join three successful ordered child calls, then return the self callback receipt. -/
@[pf_entry]
def sendAnd3Success (state : State) (value : UInt64) : Except Error (State × UInt64) :=
  let _ := Promises.callAnd3ThenReturned
    receiver "echo" (borshUInt64 111) ({ w0 := 0, w1 := 0 } : NearToken) joinedChildGas
    receiver "echo" (borshUInt64 222) ({ w0 := 0, w1 := 0 } : NearToken) joinedChildGas
    receiver "echo" (borshUInt64 333) ({ w0 := 0, w1 := 0 } : NearToken) joinedChildGas
    "callbackJoined3" (borshUInt64 83) ({ w0 := 0, w1 := 0 } : NearToken) callbackGas
  .ok ({ state with marker := value }, value)

/-- A failed right child retains left/middle/right callback-result ordering. -/
@[pf_entry]
def sendAnd3RightMissing (state : State) (value : UInt64) : Except Error (State × UInt64) :=
  let _ := Promises.callAnd3ThenReturned
    receiver "echo" (borshUInt64 111) ({ w0 := 0, w1 := 0 } : NearToken) joinedChildGas
    receiver "echo" (borshUInt64 222) ({ w0 := 0, w1 := 0 } : NearToken) joinedChildGas
    receiver "missing" (borshUInt64 333) ({ w0 := 0, w1 := 0 } : NearToken) joinedChildGas
    "callbackJoined3" (borshUInt64 84) ({ w0 := 0, w1 := 0 } : NearToken) callbackGas
  .ok ({ state with marker := value }, value)

/-- Join four successful ordered child calls, then return the self callback receipt. -/
@[pf_entry]
def sendAnd4Success (state : State) (value : UInt64) : Except Error (State × UInt64) :=
  let _ := Promises.callAnd4ThenReturned
    receiver "echo" (borshUInt64 111) ({ w0 := 0, w1 := 0 } : NearToken) joinedChildGas
    receiver "echo" (borshUInt64 222) ({ w0 := 0, w1 := 0 } : NearToken) joinedChildGas
    receiver "echo" (borshUInt64 333) ({ w0 := 0, w1 := 0 } : NearToken) joinedChildGas
    receiver "echo" (borshUInt64 444) ({ w0 := 0, w1 := 0 } : NearToken) joinedChildGas
    "callbackJoined4" (borshUInt64 85) ({ w0 := 0, w1 := 0 } : NearToken) callbackGas
  .ok ({ state with marker := value }, value)

/-- A failed fourth child retains left/middle/right/fourth callback-result ordering. -/
@[pf_entry]
def sendAnd4FourthMissing (state : State) (value : UInt64) : Except Error (State × UInt64) :=
  let _ := Promises.callAnd4ThenReturned
    receiver "echo" (borshUInt64 111) ({ w0 := 0, w1 := 0 } : NearToken) joinedChildGas
    receiver "echo" (borshUInt64 222) ({ w0 := 0, w1 := 0 } : NearToken) joinedChildGas
    receiver "echo" (borshUInt64 333) ({ w0 := 0, w1 := 0 } : NearToken) joinedChildGas
    receiver "missing" (borshUInt64 444) ({ w0 := 0, w1 := 0 } : NearToken) joinedChildGas
    "callbackJoined4" (borshUInt64 86) ({ w0 := 0, w1 := 0 } : NearToken) callbackGas
  .ok ({ state with marker := value }, value)

/-- Join five successful ordered child calls, then return the self callback receipt. -/
@[pf_entry]
def sendAnd5Success (state : State) (value : UInt64) : Except Error (State × UInt64) :=
  let _ := Promises.callAnd5ThenReturned
    receiver "echo" (borshUInt64 111) ({ w0 := 0, w1 := 0 } : NearToken) joinedChildGas
    receiver "echo" (borshUInt64 222) ({ w0 := 0, w1 := 0 } : NearToken) joinedChildGas
    receiver "echo" (borshUInt64 333) ({ w0 := 0, w1 := 0 } : NearToken) joinedChildGas
    receiver "echo" (borshUInt64 444) ({ w0 := 0, w1 := 0 } : NearToken) joinedChildGas
    receiver "echo" (borshUInt64 555) ({ w0 := 0, w1 := 0 } : NearToken) joinedChildGas
    "callbackJoined5" (borshUInt64 87) ({ w0 := 0, w1 := 0 } : NearToken) callbackGas
  .ok ({ state with marker := value }, value)

/-- A failed fifth child retains left/middle/right/fourth/fifth callback-result ordering. -/
@[pf_entry]
def sendAnd5FifthMissing (state : State) (value : UInt64) : Except Error (State × UInt64) :=
  let _ := Promises.callAnd5ThenReturned
    receiver "echo" (borshUInt64 111) ({ w0 := 0, w1 := 0 } : NearToken) joinedChildGas
    receiver "echo" (borshUInt64 222) ({ w0 := 0, w1 := 0 } : NearToken) joinedChildGas
    receiver "echo" (borshUInt64 333) ({ w0 := 0, w1 := 0 } : NearToken) joinedChildGas
    receiver "echo" (borshUInt64 444) ({ w0 := 0, w1 := 0 } : NearToken) joinedChildGas
    receiver "missing" (borshUInt64 555) ({ w0 := 0, w1 := 0 } : NearToken) joinedChildGas
    "callbackJoined5" (borshUInt64 88) ({ w0 := 0, w1 := 0 } : NearToken) callbackGas
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
