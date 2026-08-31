import ProofForge.Attr
import ProofForge.Wasm.Xrpl.Runtime

/-!
# XRPL Bedrock SDK

Contract-facing names over existing Runtime leaves. Every public definition is
`@[pf_inline]` and erases to `ProofForge.Wasm.Xrpl.Runtime.*`. No new host import,
Op, or storage layout. Ownable and Pausable remain source `if`s on AccountId
limbs and a UInt64 flag.

wasm v0 rejects `bitAnd` / `bitOr`, so `&&` / `||` / `Bool.and` cannot
appear in an entry. Prefer else-if guards (`if !cond then .error …`) over a
then-pyramid. `!` is `Not`, which extracts. Sequential `flush*` /
`storeOwner` stay as later guards (`else if !Gate.ok …`) so effects keep
source order. Not Rust `?`, not `do` / `Except.bind`.
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

/-- Persist `v` onto the current Owner card under JSON key `allw`.
Allowance granted to the compile-time spender. Not a Map. -/
@[pf_inline] def flushAllw (v : UInt64) : UInt64 :=
  Runtime.xrplFlushAllw v

/-- Load `allw` from `(w0,w1,w2)`'s card (missing → 0). Rewrites persist Owner. -/
@[pf_inline] def peekAllwLimbs (w0 w1 w2 : UInt64) : UInt64 :=
  Runtime.xrplPeekAllw w0 w1 w2

/-- `allw` on a compile-time AccountID. Hex is 40 lowercase chars. -/
@[pf_inline] def peekAllwLit (hex : String) : UInt64 :=
  Runtime.xrplPeekAllw
    (Runtime.xrplAccountLitW0 hex)
    (Runtime.xrplAccountLitW1 hex)
    (Runtime.xrplAccountLitW2 hex)

/-- Persist `v` onto the current Owner card under JSON key `lock`.
Per-user freeze. Not global `halt`, not a Map. -/
@[pf_inline] def flushLock (v : UInt64) : UInt64 :=
  Runtime.xrplFlushLock v

/-- Load `lock` from `(w0,w1,w2)`'s card (missing → 0). Rewrites persist Owner. -/
@[pf_inline] def peekLockLimbs (w0 w1 w2 : UInt64) : UInt64 :=
  Runtime.xrplPeekLock w0 w1 w2

/-- Persist `v` onto the current Owner card under JSON key `esc`.
Escrow lives on the contract card, not per-user `bal`. -/
@[pf_inline] def flushEsc (v : UInt64) : UInt64 :=
  Runtime.xrplFlushEsc v

/-- Load `esc` from `(w0,w1,w2)`'s card (missing → 0). Rewrites persist Owner. -/
@[pf_inline] def peekEscLimbs (w0 w1 w2 : UInt64) : UInt64 :=
  Runtime.xrplPeekEsc w0 w1 w2

/-- Persist `v` onto the current Owner card under JSON key `due`.
Vesting height lives on the contract card. -/
@[pf_inline] def flushDue (v : UInt64) : UInt64 :=
  Runtime.xrplFlushDue v

/-- Load `due` from `(w0,w1,w2)`'s card (missing → 0). Rewrites persist Owner. -/
@[pf_inline] def peekDueLimbs (w0 w1 w2 : UInt64) : UInt64 :=
  Runtime.xrplPeekDue w0 w1 w2

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

namespace Gate

/-- Not `@[pf_inline]`: `~~~(0)` in an entry body is `bitNot`, which wasm v0
rejects. A named def is a UInt64 constant. -/
def u64Max : UInt64 := ~~~(0 : UInt64)

/-- Nested `if`, not `&&`. `Bool.and` extracts as `bitAnd` and wasm v0 rejects
it. Effects in `a` run before `b`. -/
@[pf_inline] def and2 (a b : Bool) : Bool :=
  if a then b else false

/-- Nested `if`, not `&&`. Effects run `a` then `b` then `c`. -/
@[pf_inline] def and3 (a b c : Bool) : Bool :=
  if a then
    if b then c else false
  else
    false

/-- `flush*` / `storeOwner` return the stored value. Compare against `u64Max`
to sequence the effect. Not a real overflow check on the host result. -/
@[pf_inline] def ok (v : UInt64) : Bool :=
  v ≤ u64Max

end Gate

namespace Card

/-- Load `bal` from `(w0,w1,w2)` (missing → 0). Rewrites persist Owner. -/
@[pf_inline] def peekBal (w0 w1 w2 : UInt64) : UInt64 :=
  Context.peekOwnerLimbs w0 w1 w2

/-- Persist Owner := `(w0,w1,w2)`. Returns `w2`. -/
@[pf_inline] def select (w0 w1 w2 : UInt64) : UInt64 :=
  Context.storeOwnerLimbs w0 w1 w2

/-- Persist Owner := current caller. Returns `callerW2`. -/
@[pf_inline] def restoreCaller : UInt64 :=
  Context.storeOwnerLimbs Context.callerW0 Context.callerW1 Context.callerW2

/-- Persist Owner := contract AccountID (`sfContractAccount`).
Local 2.6.1 funded Create writes this card (pokeSelf 0). Public AlphaNet
3.3.0 still returns host -22. Not a Map. -/
@[pf_inline] def storeSelf : UInt64 :=
  Context.storeOwnerLimbs Context.selfW0 Context.selfW1 Context.selfW2

/-- True when `(w0,w1,w2)`'s `lock` is missing or 0. Rewrites persist Owner. -/
@[pf_inline] def unlocked (w0 w1 w2 : UInt64) : Bool :=
  Context.peekLockLimbs w0 w1 w2 = (0 : UInt64)

/-- True when the current caller's `lock` is missing or 0. -/
@[pf_inline] def callerUnlocked : Bool :=
  Context.peekLockLimbs Context.callerW0 Context.callerW1 Context.callerW2 = (0 : UInt64)

/-- Persist `v` as `lock` on the current Owner card. Call `restoreCaller`
first so this is the caller card. Not a Map. -/
@[pf_inline] def flushCallerLock (v : UInt64) : UInt64 :=
  Context.flushLock v

/-- Load `bal` from the caller card after a dest `flushBal`.
`s.bal` is stale once `$bal` was overwritten. Not a Map. -/
@[pf_inline] def persistCaller : UInt64 :=
  Context.peekOwnerLimbs Context.callerW0 Context.callerW1 Context.callerW2

/-- Load `supp` from the contract AccountID card. Rewrites persist Owner. -/
@[pf_inline] def peekSelfSupp : UInt64 :=
  Context.peekSuppLimbs Context.selfW0 Context.selfW1 Context.selfW2

/-- Load `allw` from the caller card. Rewrites persist Owner. -/
@[pf_inline] def peekCallerAllw : UInt64 :=
  Context.peekAllwLimbs Context.callerW0 Context.callerW1 Context.callerW2

/-- Persist `v` as `allw` on the current Owner card. Call `restoreCaller`
first so this is the caller card. -/
@[pf_inline] def flushCallerAllw (v : UInt64) : UInt64 :=
  Context.flushAllw v

/-- Load `esc` from the contract AccountID card. Rewrites persist Owner. -/
@[pf_inline] def peekSelfEsc : UInt64 :=
  Context.peekEscLimbs Context.selfW0 Context.selfW1 Context.selfW2

/-- Load `due` from the contract AccountID card. Rewrites persist Owner. -/
@[pf_inline] def peekSelfDue : UInt64 :=
  Context.peekDueLimbs Context.selfW0 Context.selfW1 Context.selfW2

/-- True when contract `due` is missing/0 or `due ≤ ledgerSqn`.
Rewrites persist Owner to the contract card. Not a clock sysvar. -/
@[pf_inline] def selfDueReached : Bool :=
  Context.peekDueLimbs Context.selfW0 Context.selfW1 Context.selfW2 ≤ Context.ledgerSqn

/-- Select the contract card, then add `delta` to `esc`. Else-if, not `&&`.
Caller must `restoreCaller` afterwards. Not a Map. -/
@[pf_inline] def addSelfEsc (delta : UInt64) : Bool :=
  if !Gate.ok storeSelf then
    false
  else if !(peekSelfEsc ≤ Gate.u64Max - delta) then
    false
  else
    Gate.ok (Context.flushEsc (peekSelfEsc + delta))

/-- Select the contract card, then subtract `delta` from `esc`. Else-if, not `&&`.
Caller must `restoreCaller` afterwards. Not a Map. -/
@[pf_inline] def subSelfEsc (delta : UInt64) : Bool :=
  if !Gate.ok storeSelf then
    false
  else if !(delta ≤ peekSelfEsc) then
    false
  else
    Gate.ok (Context.flushEsc (peekSelfEsc - delta))

/-- Select the contract card, then add `delta` to `supp`. Else-if, not `&&`.
Caller must `restoreCaller` afterwards. Not a Map. -/
@[pf_inline] def addSelfSupp (delta : UInt64) : Bool :=
  if !Gate.ok storeSelf then
    false
  else if !(peekSelfSupp ≤ Gate.u64Max - delta) then
    false
  else
    Gate.ok (Context.flushSupp (peekSelfSupp + delta))

/-- Select the contract card, then subtract `delta` from `supp`. Else-if, not `&&`.
Caller must `restoreCaller` afterwards. Not a Map. -/
@[pf_inline] def subSelfSupp (delta : UInt64) : Bool :=
  if !Gate.ok storeSelf then
    false
  else if !(delta ≤ peekSelfSupp) then
    false
  else
    Gate.ok (Context.flushSupp (peekSelfSupp - delta))

/-- Select the contract card, then set `due = ledgerSqn + delta`. Else-if, not `&&`.
Caller must `restoreCaller` afterwards. Not a clock sysvar. -/
@[pf_inline] def setSelfDueAhead (delta : UInt64) : Bool :=
  if !Gate.ok storeSelf then
    false
  else if !(Context.ledgerSqn ≤ Gate.u64Max - delta) then
    false
  else
    Gate.ok (Context.flushDue (Context.ledgerSqn + delta))

/-- Persist `halt` onto the compile-time minter card. Else-if, not `&&`.
Hex is 40 lowercase chars. Caller must `restoreCaller` afterwards. -/
@[pf_inline] def flushHaltLit (hex : String) (v : UInt64) : Bool :=
  if !Gate.ok (Context.storeOwnerLit hex) then
    false
  else
    Gate.ok (Context.flushHalt v)

/-- Persist `allw` onto the compile-time minter card. Else-if, not `&&`.
Hex is 40 lowercase chars. Caller must `restoreCaller` afterwards.
Not a Map. -/
@[pf_inline] def flushAllwLit (hex : String) (v : UInt64) : Bool :=
  if !Gate.ok (Context.storeOwnerLit hex) then
    false
  else
    Gate.ok (Context.flushAllw v)

/-- True when compile-time minter `allw = 1`. Rewrites persist Owner. -/
@[pf_inline] def allwLitIsOne (hex : String) : Bool :=
  Context.peekAllwLit hex = (1 : UInt64)

end Card

namespace Pay

/-- Local 2.6.1: emit Payment 192 drops to the caller. Public AlphaNet
is tefBAD_AUTH -196. Not `Sdk.Payments`. -/
@[pf_inline] def emitToCaller : UInt64 :=
  Runtime.xrplEmitPay

/-- Local 2.6.1: emit Payment of `drops` to the caller. Public -196.
Not `Sdk.Payments`. -/
@[pf_inline] def emitToCallerDrops (drops : UInt64) : UInt64 :=
  Runtime.xrplEmitPayDrops drops

/-- Local 2.6.1: emit Payment 192 drops to a compile-time AccountID.
`hex` is 40 lowercase chars. Public -196. Not `Sdk.Payments`. -/
@[pf_inline] def emitToLit (hex : String) : UInt64 :=
  Runtime.xrplEmitPayToLit hex

end Pay

namespace Hash

/-- Compile-time ASCII SHA-512Half, first little-endian UInt64. Not `sha256Lit`. -/
@[pf_inline] def sha512HalfLit (seed : String) : UInt64 :=
  Runtime.xrplSha512HalfLit seed

end Hash

end ProofForge.Wasm.Xrpl.Sdk
