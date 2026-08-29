import ProofForge.Attr
import ProofForge.Wasm.Near.Runtime
import ProofForge.Wasm.Near.Sdk.Transient
import ProofForge.Wasm.Near.Sdk.Storage
import ProofForge.Wasm.Near.Sdk.Store.Vector

namespace ProofForge.Wasm.Near.Sdk

/-!
Source-facing NEAR SDK. Names erase through `@[pf_inline]` to Runtime stubs;
they do not add Ops, IR nodes, or emitter cases. Promise / NEP-141 stay absent.
-/

notation "AccountId" => Runtime.AccountId
notation "NearToken" => Runtime.NearToken

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

end Logs

namespace Access

/-- Callback/private-entry predicate. Promise callbacks should require the
immediate predecessor to equal the current contract account. -/
@[pf_inline] def isSelfCall : Bool :=
  AccountId.eq Context.caller Context.self

end Access

end ProofForge.Wasm.Near.Sdk
