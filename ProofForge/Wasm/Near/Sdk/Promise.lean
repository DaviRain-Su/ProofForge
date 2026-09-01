import ProofForge.Attr
import ProofForge.Core.Value
import ProofForge.Wasm.Near.Codec
import ProofForge.Wasm.Near.Runtime

/-!
# Bounded NEAR Promise calls

The Promise foundation schedules a cross-contract function call with a static receiver and method,
bounded byte arguments, lossless u128 deposit, and explicit gas. The emitter follows near-sdk-rs
with `promise_batch_create` plus `promise_batch_action_function_call`.
Native transfer uses the same static receiver and lossless u128 amount with
`promise_batch_action_transfer`.

Detached means no `promise_return`: the remote receipt still executes, but its success and result
do not become the current call's result. Returned means `promise_return` forwards the remote
receipt's eventual success, failure, and result. Synchronous host validation failures still abort
and roll back the caller.

`ResultBuffer` provides bounded callback-result observation. Result count and reads are prohibited
by nearcore in views. `read` preserves nearcore's 0 not-ready / 1 successful / 2 failed status;
only success has bytes. An out-of-range result index aborts. `callThenReturned` adds one static
self-callback edge; its explicit callback arguments are independent of the child result channel.
`callAndThenReturned` closes two ordered static children through one internal join and self callback.
Strict fixed-width Borsh UInt64 decoding remains SDK policy over the active descriptor; additional
scalar decoders and general Promise handles remain outside this slice.

`PromiseHandle` (N13) wraps the opaque host promise index with bounded depth and fan-in metadata.
Depth and fan-in ceilings are enforced via `depthOk` / `fanInOk` before chaining further edges.
-/

namespace ProofForge.Wasm.Near.Sdk.Promises

open ProofForge.Core.Value

/-- Default compile-time fan-in capacity for bounded Promise joins (N13). -/
def defaultMaxFanIn : Nat := 4

/-- Hard ceiling on Promise DAG depth tracked by source handles. -/
def maxPromiseDepth : Nat := 8

/-- Source-visible bounded Promise handle. The host index remains opaque to applications. -/
structure PromiseHandle (maxFanIn : Nat := defaultMaxFanIn) where
  id : UInt64
  depth : UInt8
  fanIn : UInt8
  deriving Repr, Inhabited

/-- Schedule one detached cross-contract function call. `receiver` and `method` must be static
literals accepted by the NEAR target. -/
@[pf_inline] def callDetached {argsCapacity : Nat}
    (receiver method : String) (arguments : BoundedBytes argsCapacity)
    (deposit : Runtime.NearToken) (gas : UInt64) : UInt64 :=
  Runtime.promiseFunctionCallDetached argsCapacity receiver method arguments
    deposit.w0 deposit.w1 gas

/-- Schedule one cross-contract function call and forward its eventual result. `receiver` and
`method` must be static literals accepted by the NEAR target. -/
@[pf_inline] def callReturned {argsCapacity : Nat}
    (receiver method : String) (arguments : BoundedBytes argsCapacity)
    (deposit : Runtime.NearToken) (gas : UInt64) : UInt64 :=
  Runtime.promiseFunctionCallReturned argsCapacity receiver method arguments
    deposit.w0 deposit.w1 gas

/-- Schedule one detached native transfer. `receiver` must be a static AccountId literal. -/
@[pf_inline] def transferDetached
    (receiver : String) (amount : Runtime.NearToken) : UInt64 :=
  Runtime.promiseTransferDetached receiver amount.w0 amount.w1

/-- Schedule one native transfer and forward its eventual success or failure. -/
@[pf_inline] def transferReturned
    (receiver : String) (amount : Runtime.NearToken) : UInt64 :=
  Runtime.promiseTransferReturned receiver amount.w0 amount.w1

/-- Schedule one detached native transfer to a complete dynamic AccountId. Context-sourced
AccountIds are nominally valid; this closed API enforces only the protocol's 2..64 byte geometry. -/
@[pf_inline] def transferAccountDetached
    (receiver : Runtime.AccountId) (amount : Runtime.NearToken) : UInt64 :=
  Runtime.promiseTransferAccountDetached receiver amount.w0 amount.w1

/-- Schedule one native transfer to a complete dynamic AccountId and forward its eventual receipt
success or failure. -/
@[pf_inline] def transferAccountReturned
    (receiver : Runtime.AccountId) (amount : Runtime.NearToken) : UInt64 :=
  Runtime.promiseTransferAccountReturned receiver amount.w0 amount.w1

/-- Schedule and return one specialized dynamic `ft_on_transfer` receipt. The target composes
`{"sender_id":"...","amount":"...","msg":"..."}`, attaches zero NEAR, and uses the weighted
function-call host action. This is not a generic dynamic JSON Promise API. -/
@[pf_inline] def ftOnTransferReturned
    (receiver sender : Runtime.AccountId) (amount : Runtime.NearToken)
    (msg : Runtime.BoundedMessage64) : UInt64 :=
  Runtime.promiseFtOnTransferReturned receiver sender amount msg

/-- Return the fixed weighted `ft_on_transfer` → private `ft_resolve_transfer` DAG. This specialized
operation composes both JSON payloads and exposes no arbitrary method, gas, deposit, or weight. -/
@[pf_inline] def ftOnTransferThenResolveReturned
    (receiver sender : Runtime.AccountId) (amount : Runtime.NearToken)
    (msg : Runtime.BoundedMessage64) : UInt64 :=
  Runtime.promiseFtOnTransferThenResolveReturned receiver sender amount msg

/-- Schedule one child call, then one callback on the current contract, and forward the callback's
eventual result. Both methods are static literals; the two bounded argument frames, deposits, and
gas budgets are independent. The callback runs after either child success or child failure. -/
@[pf_inline] def callThenReturned {childArgsCapacity callbackArgsCapacity : Nat}
    (receiver childMethod : String)
    (childArguments : BoundedBytes childArgsCapacity)
    (childDeposit : Runtime.NearToken) (childGas : UInt64)
    (callbackMethod : String)
    (callbackArguments : BoundedBytes callbackArgsCapacity)
    (callbackDeposit : Runtime.NearToken) (callbackGas : UInt64) : UInt64 :=
  Runtime.promiseFunctionCallThenReturned childArgsCapacity callbackArgsCapacity
    receiver childMethod callbackMethod childArguments callbackArguments
    childDeposit.w0 childDeposit.w1 childGas
    callbackDeposit.w0 callbackDeposit.w1 callbackGas

/-- Schedule two ordered independent child calls, join them, then run one callback on the current
contract and forward only the callback receipt. Callback result indices 0 and 1 preserve left/right
input order even when either child fails. -/
@[pf_inline] def callAndThenReturned
    {leftArgsCapacity rightArgsCapacity callbackArgsCapacity : Nat}
    (leftReceiver leftMethod : String)
    (leftArguments : BoundedBytes leftArgsCapacity)
    (leftDeposit : Runtime.NearToken) (leftGas : UInt64)
    (rightReceiver rightMethod : String)
    (rightArguments : BoundedBytes rightArgsCapacity)
    (rightDeposit : Runtime.NearToken) (rightGas : UInt64)
    (callbackMethod : String)
    (callbackArguments : BoundedBytes callbackArgsCapacity)
    (callbackDeposit : Runtime.NearToken) (callbackGas : UInt64) : UInt64 :=
  Runtime.promiseFunctionCallAndThenReturned
    leftArgsCapacity rightArgsCapacity callbackArgsCapacity
    leftReceiver leftMethod rightReceiver rightMethod callbackMethod
    leftArguments rightArguments callbackArguments
    leftDeposit.w0 leftDeposit.w1 leftGas
    rightDeposit.w0 rightDeposit.w1 rightGas
    callbackDeposit.w0 callbackDeposit.w1 callbackGas

/-- Schedule three ordered independent child calls, join them, then run one callback on the current
contract and forward only the callback receipt. Callback result indices 0..2 preserve
left/middle/right input order even when any child fails. -/
@[pf_inline] def callAnd3ThenReturned
    {leftArgsCapacity midArgsCapacity rightArgsCapacity callbackArgsCapacity : Nat}
    (leftReceiver leftMethod : String)
    (leftArguments : BoundedBytes leftArgsCapacity)
    (leftDeposit : Runtime.NearToken) (leftGas : UInt64)
    (midReceiver midMethod : String)
    (midArguments : BoundedBytes midArgsCapacity)
    (midDeposit : Runtime.NearToken) (midGas : UInt64)
    (rightReceiver rightMethod : String)
    (rightArguments : BoundedBytes rightArgsCapacity)
    (rightDeposit : Runtime.NearToken) (rightGas : UInt64)
    (callbackMethod : String)
    (callbackArguments : BoundedBytes callbackArgsCapacity)
    (callbackDeposit : Runtime.NearToken) (callbackGas : UInt64) : UInt64 :=
  Runtime.promiseFunctionCallAnd3ThenReturned
    leftArgsCapacity midArgsCapacity rightArgsCapacity callbackArgsCapacity
    leftReceiver leftMethod midReceiver midMethod rightReceiver rightMethod callbackMethod
    leftArguments midArguments rightArguments callbackArguments
    leftDeposit.w0 leftDeposit.w1 leftGas
    midDeposit.w0 midDeposit.w1 midGas
    rightDeposit.w0 rightDeposit.w1 rightGas
    callbackDeposit.w0 callbackDeposit.w1 callbackGas

namespace PromiseHandle

@[pf_inline] def depthOk {maxFanIn : Nat} (handle : PromiseHandle maxFanIn) : Bool :=
  handle.depth.toNat ≤ maxPromiseDepth

@[pf_inline] def fanInOk {maxFanIn : Nat} (handle : PromiseHandle maxFanIn) : Bool :=
  handle.fanIn.toNat ≤ maxFanIn

/-- Schedule one returned child call and expose it as a root handle (`depth = 0`). -/
@[pf_inline] def createReturned {argsCapacity : Nat}
    (receiver method : String) (arguments : BoundedBytes argsCapacity)
    (deposit : Runtime.NearToken) (gas : UInt64) : PromiseHandle :=
  { id := callReturned receiver method arguments deposit gas
    depth := 0, fanIn := 0 }

/-- Attach one self callback edge; increments tracked depth. Callers must check `depthOk`. -/
@[pf_inline] def thenReturned {maxFanIn : Nat}
    {childArgsCapacity callbackArgsCapacity : Nat}
    (handle : PromiseHandle maxFanIn)
    (receiver childMethod : String)
    (childArguments : BoundedBytes childArgsCapacity)
    (childDeposit : Runtime.NearToken) (childGas : UInt64)
    (callbackMethod : String)
    (callbackArguments : BoundedBytes callbackArgsCapacity)
    (callbackDeposit : Runtime.NearToken) (callbackGas : UInt64) : PromiseHandle maxFanIn :=
  { id := callThenReturned receiver childMethod childArguments childDeposit childGas
      callbackMethod callbackArguments callbackDeposit callbackGas
    depth := handle.depth + 1, fanIn := handle.fanIn }

end PromiseHandle

/-- Number of callback inputs for this invocation. Ordinary calls report zero. -/
@[pf_inline] def resultsCount : UInt64 :=
  Runtime.promiseResultsCount

/-- Compile-time bound for one invocation-local Promise-result copy. -/
abbrev ResultBuffer := Nat

def ResultBuffer.wellFormed (buffer : ResultBuffer) : Bool :=
  ProofForge.Wasm.Near.Codec.storageCapacityValid buffer

@[pf_inline] def ResultBuffer.bounded (capacity : Nat) : ResultBuffer :=
  capacity

/-- Read one callback input into this bounded descriptor. An index outside `resultsCount` aborts. -/
@[pf_inline] def ResultBuffer.read (buffer : ResultBuffer) (index : UInt64) : UInt64 :=
  Runtime.promiseResultRead buffer index

@[pf_inline] def ResultBuffer.status (buffer : ResultBuffer) : UInt64 :=
  Runtime.promiseResultStatus buffer

@[pf_inline] def ResultBuffer.length (buffer : ResultBuffer) : UInt64 :=
  Runtime.promiseResultLength buffer

/-- Whether a successful result fit. Status 0/2 have no bytes and retain the neutral value true. -/
@[pf_inline] def ResultBuffer.fits (buffer : ResultBuffer) : Bool :=
  Runtime.promiseResultFits buffer != 0

@[pf_inline] def ResultBuffer.byte (buffer : ResultBuffer) (index : UInt64) : UInt8 :=
  (Runtime.promiseResultByte buffer index).toUInt8

/-- Decode one exact eight-byte little-endian Borsh `UInt64`. Any unavailable or malformed result
returns `fallback`. Call `read` immediately before decoding this descriptor. -/
@[pf_inline] def ResultBuffer.borshUInt64D
    (buffer : ResultBuffer) (fallback : UInt64) : UInt64 :=
  Runtime.promiseResultBorshUInt64D buffer fallback

/-- Decode the strict canonical standalone JSON u128 subset from the active 41-byte descriptor.
The resolver boundary owns the exact `resultsCount == 1` guard and index-zero read immediately
before this call. Failed, oversized, and malformed results preserve their status but return
`valid = 0` and zero limbs. -/
@[pf_inline] def ResultBuffer.quotedU128
    (buffer : ResultBuffer) : Runtime.QuotedU128Result :=
  { status := buffer.status
    valid := Runtime.promiseResultQuotedU128Valid buffer
    w0 := Runtime.promiseResultQuotedU128W0 buffer
    w1 := Runtime.promiseResultQuotedU128W1 buffer }

end ProofForge.Wasm.Near.Sdk.Promises
