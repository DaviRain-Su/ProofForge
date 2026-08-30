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
Strict fixed-width Borsh UInt64 decoding remains SDK policy over the active descriptor; additional
scalar decoders and joins remain outside this slice.
-/

namespace ProofForge.Wasm.Near.Sdk.Promises

open ProofForge.Core.Value

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

end ProofForge.Wasm.Near.Sdk.Promises
