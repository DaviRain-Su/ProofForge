import ProofForge.Attr
import ProofForge.Wasm.Near.Runtime
import ProofForge.Wasm.Near.Sdk.Storage
import ProofForge.Wasm.Near.Sdk.Store.Codec

/-!
# Closed storage-registration economics helpers

These pure descriptor helpers support caller-only measured-cost registration and zero-balance
unregister policies. They do not perform storage or Promise effects, define the public NEP-145 ABI
or force-unregister, or choose the trusted source of `storage_amount_per_byte`.
-/

namespace ProofForge.Wasm.Near.Sdk.Fungible.Registration

open ProofForge.Wasm.Near.Sdk.Storage
open ProofForge.Wasm.Near.Sdk.Store

/-- The active exact-value storage read observed no entry. -/
@[pf_inline] def readWasMissing : Bool :=
  let result : ResultBuffer := 16
  result.status = 0

/-- The active storage read observed one well-formed Borsh-u128 value. -/
@[pf_inline] def readWasValidPresent : Bool :=
  let result : ResultBuffer := 16
  result.status = 1 && result.fits && result.length = 16

/-- This first policy rejects a zero trusted per-byte price rather than silently making storage
free. The price itself must come from trusted immutable/configured state. -/
@[pf_inline] def trustedCostValid
    (cost : ProofForge.Wasm.Near.Runtime.NearToken) : Bool :=
  cost.w0 != 0 || cost.w1 != 0

/-- `storage_usage` deltas are unsigned and must not wrap. -/
@[pf_inline] def usageDeltaValid (before after : UInt64) : Bool := before ≤ after

@[pf_inline] def tokenIsZero
    (value : ProofForge.Wasm.Near.Runtime.NearToken) : Bool :=
  value.w0 = 0 && value.w1 = 0

/-- True exactly when subtraction can produce the excess deposit without u128 underflow. -/
@[pf_inline] def depositCovers
    (deposit cost : ProofForge.Wasm.Near.Runtime.NearToken) : Bool :=
  ProofForge.Wasm.Near.Runtime.nearTokenSubOk
    deposit.w0 deposit.w1 cost.w0 cost.w1 != 0

/-- Closed unregister calls mirror near-sdk's strict one-yocto security deposit. -/
@[pf_inline] def attachedIsOne
    (deposit : ProofForge.Wasm.Near.Runtime.NearToken) : Bool :=
  deposit.w0 = 1 && deposit.w1 = 0

/-- Only an exact decoded zero balance is eligible for the first non-force unregister policy. -/
@[pf_inline] def loadedBalanceIsZero : Bool :=
  resultNearTokenW0D 1 = 0 && resultNearTokenW1D 1 = 0

end ProofForge.Wasm.Near.Sdk.Fungible.Registration
