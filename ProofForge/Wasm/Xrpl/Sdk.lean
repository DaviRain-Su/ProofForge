import ProofForge.Attr
import ProofForge.Wasm.Xrpl.Runtime

/-!
# XRPL Bedrock SDK

Contract-facing names over existing Runtime leaves. Every public definition is
`@[pf_inline]` and erases to `ProofForge.Wasm.Xrpl.Runtime.*`. No new host import,
Op, or storage layout. Ownable and Pausable remain source `if`s on AccountId
limbs and a UInt64 flag.
-/

namespace ProofForge.Wasm.Xrpl.Sdk

notation "AccountId" => Runtime.AccountId

namespace «AccountId»

/-- Three-limb equality. Nested `if`, not `&&` (wasm v0 rejects `bitAnd`).
Not EVM `eq20`, not a host. -/
@[pf_inline] def eq (left right : AccountId) : Bool :=
  if left.w0 = right.w0 then
    if left.w1 = right.w1 then
      left.w2 = right.w2
    else
      false
  else
    false

@[pf_inline] def ofLimbs (w0 w1 w2 : UInt64) : AccountId :=
  { w0, w1, w2 }

end «AccountId»

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

/-- First little-endian UInt64 of parent ledger hash. Not EVM `blockhash`. -/
@[pf_inline] def parentHashLo : UInt64 := Runtime.xrplParentHashW0

/-- `host_lib.get_base_fee`. Not EVM `baseFee` UInt256. -/
@[pf_inline] def baseFee : UInt64 := Runtime.xrplBaseFee

/-- Caller's XRP AccountRoot.Balance in drops. Not EVM `selfBalance`. -/
@[pf_inline] def callerBalanceDrops : UInt64 := Runtime.xrplCallerBalanceDrops

/-- AccountRoot.Sequence. Not SVM `clockSlot`. -/
@[pf_inline] def callerSequence : UInt64 := Runtime.xrplCallerSequence

/-- AccountRoot.Flags. -/
@[pf_inline] def callerFlags : UInt64 := Runtime.xrplCallerFlags

/-- AccountRoot.OwnerCount at cache_le. Creating ContractData may bump the live count. -/
@[pf_inline] def callerOwnerCount : UInt64 := Runtime.xrplCallerOwnerCount

/-- Current `ContractCall` Sequence. Not AccountRoot.Sequence. -/
@[pf_inline] def txSequence : UInt64 := Runtime.xrplTxSequence

/-- Current `ContractCall` Fee in drops. Not EVM `gasprice`. -/
@[pf_inline] def txFeeDrops : UInt64 := Runtime.xrplTxFeeDrops

/-- Compile-time 20-byte AccountID from 40 hex chars. Not a host, not EVM `address(uint)`. -/
@[pf_inline] def accountLit (hex : String) : AccountId :=
  Runtime.xrplAccountLit hex

/-- Current `ContractCall` Flags. -/
@[pf_inline] def txFlags : UInt64 := Runtime.xrplTxFlags

/-- Compile-time AccountID's XRP Balance in drops. Persist owner stays the caller. -/
@[pf_inline] def litBalanceDrops (hex : String) : UInt64 :=
  Runtime.xrplLitBalanceDrops hex

/-- Persist the next store onto this AccountID's ContractData card.
Returns `id.w2`. Not `setUserData`, not a Map. -/
@[pf_inline] def storeOwner (id : AccountId) : UInt64 :=
  Runtime.xrplStoreOwner id.w0 id.w1 id.w2

/-- Same as `storeOwner`, three little-endian limbs. Extractor-friendly. -/
@[pf_inline] def storeOwnerLimbs (w0 w1 w2 : UInt64) : UInt64 :=
  Runtime.xrplStoreOwner w0 w1 w2

/-- Persist `v` onto the current Owner card. Then a later `peekOwnerLimbs`
can switch cards. Not a Payment. -/
@[pf_inline] def flushBal (v : UInt64) : UInt64 :=
  Runtime.xrplFlushBal v

/-- Load `bal` from the card owned by `(w0,w1,w2)` (missing → 0). Rewrites
persist Owner. Not `setUserData`. -/
@[pf_inline] def peekOwnerLimbs (w0 w1 w2 : UInt64) : UInt64 :=
  Runtime.xrplPeekOwner w0 w1 w2

/-- Persist `v` onto the current Owner card under JSON key `halt`.
Keep pause off the per-user `bal` slot. -/
@[pf_inline] def flushHalt (v : UInt64) : UInt64 :=
  Runtime.xrplFlushHalt v

/-- Load `halt` from `(w0,w1,w2)`'s card (missing → 0). Rewrites persist Owner. -/
@[pf_inline] def peekHaltLimbs (w0 w1 w2 : UInt64) : UInt64 :=
  Runtime.xrplPeekHalt w0 w1 w2

/-- `halt` on a compile-time AccountID. Hex is 40 lowercase chars. -/
@[pf_inline] def peekHaltLit (hex : String) : UInt64 :=
  Runtime.xrplPeekHalt
    (Runtime.xrplAccountLitW0 hex)
    (Runtime.xrplAccountLitW1 hex)
    (Runtime.xrplAccountLitW2 hex)

/-- Persist Owner := compile-time AccountID. Returns w2. -/
@[pf_inline] def storeOwnerLit (hex : String) : UInt64 :=
  Runtime.xrplStoreOwner
    (Runtime.xrplAccountLitW0 hex)
    (Runtime.xrplAccountLitW1 hex)
    (Runtime.xrplAccountLitW2 hex)

/-- Persist `v` onto the current Owner card under JSON key `supp`.
Total supply lives on the minter card, not per-user `bal`. -/
@[pf_inline] def flushSupp (v : UInt64) : UInt64 :=
  Runtime.xrplFlushSupp v

/-- Load `supp` from `(w0,w1,w2)`'s card (missing → 0). Rewrites persist Owner. -/
@[pf_inline] def peekSuppLimbs (w0 w1 w2 : UInt64) : UInt64 :=
  Runtime.xrplPeekSupp w0 w1 w2

/-- `supp` on a compile-time AccountID. Hex is 40 lowercase chars. -/
@[pf_inline] def peekSuppLit (hex : String) : UInt64 :=
  Runtime.xrplPeekSupp
    (Runtime.xrplAccountLitW0 hex)
    (Runtime.xrplAccountLitW1 hex)
    (Runtime.xrplAccountLitW2 hex)

/-- Persist `v` onto the current Owner card under JSON key `cap`.
`0` means unlimited (same as a missing field). -/
@[pf_inline] def flushCap (v : UInt64) : UInt64 :=
  Runtime.xrplFlushCap v

/-- Load `cap` from `(w0,w1,w2)`'s card (missing → 0). Rewrites persist Owner. -/
@[pf_inline] def peekCapLimbs (w0 w1 w2 : UInt64) : UInt64 :=
  Runtime.xrplPeekCap w0 w1 w2

/-- `cap` on a compile-time AccountID. Hex is 40 lowercase chars. -/
@[pf_inline] def peekCapLit (hex : String) : UInt64 :=
  Runtime.xrplPeekCap
    (Runtime.xrplAccountLitW0 hex)
    (Runtime.xrplAccountLitW1 hex)
    (Runtime.xrplAccountLitW2 hex)

end Context

namespace Pausable

/-- Canonical running flag. Not EVM `Pausable.running` UInt8; XRPL stores UInt64. -/
@[pf_inline] def running : UInt64 := 0

/-- Canonical paused flag. -/
@[pf_inline] def paused : UInt64 := 1

/-- True only for the canonical running flag. Unknown values fail closed. -/
@[pf_inline] def isRunning (flag : UInt64) : Bool :=
  flag = running

end Pausable

namespace Access

/-- Owner gate. Use as `if Access.requireOwner owner then … else .error .unauthorized`.
Not EVM `Revert.unauthorized(address)`. -/
@[pf_inline] def requireOwner (owner : AccountId) : Bool :=
  AccountId.eq Context.caller owner

/-- Owner or operator. Nested `if`, not `||` (wasm v0). -/
@[pf_inline] def requireOwnerOr (owner operator : AccountId) : Bool :=
  if AccountId.eq Context.caller owner then
    true
  else
    AccountId.eq Context.caller operator

end Access

namespace Hash

/-- Compile-time ASCII SHA-512Half, first little-endian UInt64. Not `sha256Lit`. -/
@[pf_inline] def sha512HalfLit (seed : String) : UInt64 :=
  Runtime.xrplSha512HalfLit seed

end Hash

end ProofForge.Wasm.Xrpl.Sdk
