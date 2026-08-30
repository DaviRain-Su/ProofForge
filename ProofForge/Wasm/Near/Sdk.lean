import ProofForge.Attr
import ProofForge.Wasm.Near.Runtime
import ProofForge.Wasm.Near.Sdk.Transient
import ProofForge.Wasm.Near.Sdk.Storage
import ProofForge.Wasm.Near.Sdk.Promise
import ProofForge.Wasm.Near.Sdk.Store.Codec
import ProofForge.Wasm.Near.Sdk.Store.Iterable
import ProofForge.Wasm.Near.Sdk.Store.Lookup
import ProofForge.Wasm.Near.Sdk.Store.Queue
import ProofForge.Wasm.Near.Sdk.Store.Vector

namespace ProofForge.Wasm.Near.Sdk

/-!
Source-facing NEAR SDK. Names erase through `@[pf_inline]` to Runtime stubs;
they do not add Ops, IR nodes, or emitter cases unless explicitly documented as event effects.
Bounded Promise-result observation, strict Borsh UInt64 result decoding, full-AccountId
self-callback authentication, and exact NEP-141 mint/transfer/burn event serialization with
optional bounded memos are available; a fungible-token contract remains absent.
-/

notation "AccountId" => Runtime.AccountId
notation "NearToken" => Runtime.NearToken

namespace «NearToken»

@[pf_inline] def zero : NearToken := ⟨0, 0⟩

/-- True exactly when unsigned 128-bit addition is representable. -/
@[pf_inline] def canAdd (left right : NearToken) : Bool :=
  Runtime.nearTokenAddOk left.w0 left.w1 right.w0 right.w1 != 0

/-- Low modular result limb. Precondition: `canAdd left right`. -/
@[pf_inline] def addW0 (left right : NearToken) : UInt64 :=
  Runtime.nearTokenAddW0 left.w0 left.w1 right.w0 right.w1

/-- High result limb including the low-limb carry. Precondition: `canAdd left right`. -/
@[pf_inline] def addW1 (left right : NearToken) : UInt64 :=
  Runtime.nearTokenAddW1 left.w0 left.w1 right.w0 right.w1

/-- True exactly when `left ≥ right` as unsigned 128-bit values. -/
@[pf_inline] def canSub (left right : NearToken) : Bool :=
  Runtime.nearTokenSubOk left.w0 left.w1 right.w0 right.w1 != 0

/-- Low modular result limb. Precondition: `canSub left right`. -/
@[pf_inline] def subW0 (left right : NearToken) : UInt64 :=
  Runtime.nearTokenSubW0 left.w0 left.w1 right.w0 right.w1

/-- High result limb including the low-limb borrow. Precondition: `canSub left right`. -/
@[pf_inline] def subW1 (left right : NearToken) : UInt64 :=
  Runtime.nearTokenSubW1 left.w0 left.w1 right.w0 right.w1

end «NearToken»

namespace «AccountId»

/-- Lossless equality over the length and all 64 bytes. Nested `if` keeps the
comparison inside the current wasm scalar subset; this is not a host call. -/
@[pf_inline] def eq (left right : AccountId) : Bool :=
  if left.length = right.length then
    if left.w0 = right.w0 then
      if left.w1 = right.w1 then
        if left.w2 = right.w2 then
          if left.w3 = right.w3 then
            if left.w4 = right.w4 then
              if left.w5 = right.w5 then
                if left.w6 = right.w6 then
                  left.w7 = right.w7
                else false
              else false
            else false
          else false
        else false
      else false
    else false
  else false

end «AccountId»

namespace Context

@[pf_inline] def blockHeight : UInt64 :=
  Runtime.blockIndex

@[pf_inline] def unixTimeSeconds : UInt64 :=
  Runtime.blockTimestamp

/-- Complete immediate caller. Init/entry only; views fail closed at emit. -/
@[pf_inline] def caller : AccountId :=
  Runtime.predecessorAccountId

/-- Legacy low word. Not an identity; use `caller` for authorization. -/
@[pf_inline] def callerLo : UInt64 := Runtime.predecessor

/-- Complete attached yoctoNEAR amount. Init/entry only; views fail closed. -/
@[pf_inline] def attachedDeposit : NearToken :=
  Runtime.attachedDeposit128

/-- Legacy UInt64 projection. Traps if the attached amount exceeds UInt64. -/
@[pf_inline] def attachedDepositLo : UInt64 := Runtime.attachedDeposit

/-- Complete, view-safe current-account balance. -/
@[pf_inline] def balanceOfSelf : NearToken :=
  Runtime.accountBalance128

/-- Legacy UInt64 balance. Traps if the current balance exceeds UInt64. -/
@[pf_inline] def balanceOfSelfLo : UInt64 := Runtime.accountBalance

/-- Complete current contract account id. View-safe. -/
@[pf_inline] def self : AccountId :=
  Runtime.selfAccountId

/-- Legacy low word. Not an identity; use `self` for equality. -/
@[pf_inline] def selfLo : UInt64 := Runtime.currentAccountId

end Context

namespace Logs

/-- Log one compile-time UTF-8 string. The current static slice accepts at most 1024 UTF-8 bytes
and returns zero for source sequencing; receipt logging remains the observable effect. -/
@[pf_inline] def write (message : String) : UInt64 :=
  Runtime.logUtf8 message

/-- Log the active bytes of one bounded UTF-8 string. Canonical `BoundedString` input is validated
before source execution; internally constructed values must satisfy `BoundedString.wellFormed`. -/
@[pf_inline] def writeBounded (capacity : Nat)
    (message : ProofForge.Core.Value.BoundedString capacity) : UInt64 :=
  Runtime.logUtf8Bounded capacity message

end Logs

namespace Events

/-- Emit one compact NEP-297 `EVENT_JSON:` envelope with a bounded string `data` value. This is a
closed event serializer, not a generic JSON ABI. Metadata is compile-time and all strings receive
serde_json-compatible escaping in the target emitter. -/
@[pf_inline] def writeStringData (standard version event : String) (capacity : Nat)
    (data : ProofForge.Core.Value.BoundedString capacity) : UInt64 :=
  Runtime.nep297StringData capacity standard version event data

namespace FungibleToken

/-- Emit one exact NEP-141 v1.0.0 `ft_mint` event. Amount is a quoted full-u128 decimal and the
optional memo is deliberately omitted. Event support does not provide FT state or methods. -/
@[pf_inline] def mint (owner : AccountId) (amount : NearToken) : UInt64 :=
  Runtime.nep141FtMint owner amount

/-- Emit one exact NEP-141 v1.0.0 `ft_transfer` event. The record is ordered old owner, new owner,
then quoted full-u128 amount; optional memo is deliberately omitted. -/
@[pf_inline] def transfer
    (oldOwner newOwner : AccountId) (amount : NearToken) : UInt64 :=
  Runtime.nep141FtTransfer oldOwner newOwner amount

/-- Emit one exact NEP-141 v1.0.0 `ft_burn` event. Amount is quoted full-u128 decimal and the
optional memo is deliberately omitted. -/
@[pf_inline] def burn (owner : AccountId) (amount : NearToken) : UInt64 :=
  Runtime.nep141FtBurn owner amount

/-- Emit `ft_mint` with one bounded UTF-8 memo after the quoted amount field. -/
@[pf_inline] def mintWithMemo (owner : AccountId) (amount : NearToken) (memoCapacity : Nat)
    (memo : ProofForge.Core.Value.BoundedString memoCapacity) : UInt64 :=
  Runtime.nep141FtMintMemo memoCapacity owner amount memo

/-- Emit `ft_transfer` with one bounded UTF-8 memo after the quoted amount field. -/
@[pf_inline] def transferWithMemo (oldOwner newOwner : AccountId) (amount : NearToken)
    (memoCapacity : Nat) (memo : ProofForge.Core.Value.BoundedString memoCapacity) : UInt64 :=
  Runtime.nep141FtTransferMemo memoCapacity oldOwner newOwner amount memo

/-- Emit `ft_burn` with one bounded UTF-8 memo after the quoted amount field. -/
@[pf_inline] def burnWithMemo (owner : AccountId) (amount : NearToken) (memoCapacity : Nat)
    (memo : ProofForge.Core.Value.BoundedString memoCapacity) : UInt64 :=
  Runtime.nep141FtBurnMemo memoCapacity owner amount memo

end FungibleToken

end Events

namespace Access

/-- Callback/private-entry predicate. Promise callbacks should require the
immediate predecessor to equal the current contract account. -/
@[pf_inline] def isSelfCall : Bool :=
  AccountId.eq Context.caller Context.self

end Access

end ProofForge.Wasm.Near.Sdk
