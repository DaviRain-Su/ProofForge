import ProofForge.Attr
import ProofForge.Wasm.Near.Runtime
import ProofForge.Wasm.Near.Sdk.Storage

/-!
# Closed storage-registration economics helpers

These pure descriptor helpers support a caller-only measured-cost registration policy. They do not
perform storage or Promise effects and do not define the public NEP-145 ABI, unregister policy, or
the trusted source of `storage_amount_per_byte`.
-/

namespace ProofForge.Wasm.Near.Sdk.Fungible.Registration

open ProofForge.Wasm.Near.Sdk.Storage

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

end ProofForge.Wasm.Near.Sdk.Fungible.Registration
