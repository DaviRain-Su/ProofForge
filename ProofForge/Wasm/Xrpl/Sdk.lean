import ProofForge.Attr
import ProofForge.Wasm.Xrpl.Runtime

/-!
# XRPL Bedrock SDK

Contract-facing names over existing Runtime leaves. Every public definition is
`@[pf_inline]` and erases to `ProofForge.Wasm.Xrpl.Runtime.*`. No new host import,
Op, or storage layout. Ownable remains a source `if` on three AccountId limbs.
-/

namespace ProofForge.Wasm.Xrpl.Sdk

notation "AccountId" => Runtime.AccountId

namespace Context

@[pf_inline] def caller : AccountId := Runtime.xrplCaller20

/-- Low 8 bytes of the current `ContractCall` account. Not an identity. -/
@[pf_inline] def callerLo : UInt64 := Runtime.xrplCallerW0

@[pf_inline] def callerW0 : UInt64 := Runtime.xrplCallerW0
@[pf_inline] def callerW1 : UInt64 := Runtime.xrplCallerW1
@[pf_inline] def callerW2 : UInt64 := Runtime.xrplCallerW2

@[pf_inline] def self : AccountId := Runtime.xrplSelf20

/-- Low 8 bytes of `sfContractAccount`. Not an identity. -/
@[pf_inline] def selfLo : UInt64 := Runtime.xrplSelfW0

@[pf_inline] def selfW0 : UInt64 := Runtime.xrplSelfW0
@[pf_inline] def selfW1 : UInt64 := Runtime.xrplSelfW1
@[pf_inline] def selfW2 : UInt64 := Runtime.xrplSelfW2

/-- `host_lib.get_ledger_sqn`. Not `clockSlot`. -/
@[pf_inline] def ledgerSqn : UInt64 := Runtime.xrplLedgerSqn

/-- `host_lib.get_parent_ledger_time`. Not `evmTimestamp`. -/
@[pf_inline] def parentTime : UInt64 := Runtime.xrplParentTime

end Context

namespace Hash

/-- Compile-time ASCII SHA-512Half, first little-endian UInt64. Not `sha256Lit`. -/
@[pf_inline] def sha512HalfLit (seed : String) : UInt64 :=
  Runtime.xrplSha512HalfLit seed

end Hash

end ProofForge.Wasm.Xrpl.Sdk
