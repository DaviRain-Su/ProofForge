import ProofForge.Attr
import ProofForge.Core.Value
import ProofForge.Wasm.Near.Runtime

/-!
# Bounded NEAR Promise calls

The Promise foundation schedules a cross-contract function call with a static receiver and method,
bounded byte arguments, lossless u128 deposit, and explicit gas. The emitter follows near-sdk-rs
with `promise_batch_create` plus `promise_batch_action_function_call`.

Detached means no `promise_return`: the remote receipt still executes, but its success and result
do not become the current call's result. Returned means `promise_return` forwards the remote
receipt's eventual success, failure, and result. Synchronous host validation failures still abort
and roll back the caller. Chaining, callbacks/results, joins, and transfer actions remain outside
this slice.
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

end ProofForge.Wasm.Near.Sdk.Promises
