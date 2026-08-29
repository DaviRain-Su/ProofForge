import ProofForge.Attr
import ProofForge.Wasm.Near.Runtime

namespace ProofForge.Wasm.Near.Sdk

/-!
Source-facing NEAR SDK. Names erase through `@[pf_inline]` to Runtime stubs;
they do not add Ops, IR nodes, or emitter cases. Promise / NEP-141 / Principal
9-leaf identity stay absent.
-/

namespace Context

@[pf_inline] def blockHeight : UInt64 :=
  Runtime.blockIndex

@[pf_inline] def unixTimeSeconds : UInt64 :=
  Runtime.blockTimestamp

/-- Init/entry only. Views that mention this fail closed at emit. -/
@[pf_inline] def caller : UInt64 :=
  Runtime.predecessor

/-- Init/entry only. Views that mention this fail closed at emit. -/
@[pf_inline] def attachedDeposit : UInt64 :=
  Runtime.attachedDeposit

@[pf_inline] def balanceOfSelf : UInt64 :=
  Runtime.accountBalance

/-- View-safe. First 8 UTF-8 bytes of `current_account_id`, little-endian. -/
@[pf_inline] def self : UInt64 :=
  Runtime.currentAccountId

end Context

end ProofForge.Wasm.Near.Sdk
