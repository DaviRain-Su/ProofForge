import ProofForge.Attr
import ProofForge.Wasm.Near.Runtime

namespace ProofForge.Wasm.Near.Sdk

/-!
Source-facing NEAR SDK. Names erase through `@[pf_inline]` to Runtime stubs;
they do not add Ops, IR nodes, or emitter cases. Promise / NEP-141 stay absent.
-/

notation "AccountId" => Runtime.AccountId

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

/-- Init/entry only. Views that mention this fail closed at emit. -/
@[pf_inline] def attachedDeposit : UInt64 :=
  Runtime.attachedDeposit

@[pf_inline] def balanceOfSelf : UInt64 :=
  Runtime.accountBalance

/-- Complete current contract account id. View-safe. -/
@[pf_inline] def self : AccountId :=
  Runtime.selfAccountId

/-- Legacy low word. Not an identity; use `self` for equality. -/
@[pf_inline] def selfLo : UInt64 := Runtime.currentAccountId

end Context

namespace Access

/-- Callback/private-entry predicate. Promise callbacks should require the
immediate predecessor to equal the current contract account. -/
@[pf_inline] def isSelfCall : Bool :=
  AccountId.eq Context.caller Context.self

end Access

end ProofForge.Wasm.Near.Sdk
