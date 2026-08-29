import ProofForge.Core.Ops
import ProofForge.Core.CFG

/-!
# NEAR target dialect

Value/effect extensions owned by the NEAR Protocol chain. v0 admits scalar
context reads, lossless u128 token values, and lossless 64-byte account-id
leaves. Promise and hashing stay absent.
`reserved` is rejected by `wellFormed`.
-/

namespace ProofForge.Wasm.Near.Ops

/-- NEAR-owned value intrinsics. -/
inductive ValKind where
  | blockIndex
  | blockTimestamp
  /-- Legacy predecessor w0 plus the remaining lossless AccountId leaves. -/
  | predecessor
  | predecessorLen
  | predecessorW1 | predecessorW2 | predecessorW3 | predecessorW4
  | predecessorW5 | predecessorW6 | predecessorW7
  /-- Legacy checked UInt64 leaves plus lossless u128 low/high leaves. -/
  | attachedDeposit
  | attachedDepositW0 | attachedDepositW1
  | accountBalance
  | accountBalanceW0 | accountBalanceW1
  /-- Legacy current-account w0 plus the remaining lossless AccountId leaves. -/
  | currentAccountId
  | currentAccountIdLen
  | currentAccountIdW1 | currentAccountIdW2 | currentAccountIdW3 | currentAccountIdW4
  | currentAccountIdW5 | currentAccountIdW6 | currentAccountIdW7
  /-- Placeholder; never produced by the v0 lowering and rejected by `wellFormed`. -/
  | reserved
  deriving BEq, Repr, Inhabited

def ValKind.arity : ValKind → Nat
  | .reserved => 0
  | _ => 0

abbrev Val := ProofForge.Core.Ops.Val ValKind
abbrev Cmp := ProofForge.Core.Ops.Cmp

/-- NEAR-owned effects. v0 has none. -/
inductive OpExt (V : Type) where
  /-- Placeholder; never produced by the v0 lowering and rejected by `wellFormed`. -/
  | reserved
  deriving BEq, Repr, Inhabited

abbrev Op := ProofForge.Core.Ops.Op ValKind OpExt

def OpExt.wellFormed : OpExt Val → Bool
  | .reserved => false

def Op.wellFormed (op : Op) : Bool :=
  ProofForge.Core.Ops.Op.wellFormed ValKind.arity OpExt.wellFormed op

private def mapCfgPayload (_mapValue : Val → Val) : OpExt Val → OpExt Val
  | .reserved => .reserved

private def cfgPayloadValues : OpExt Val → Array Val
  | .reserved => #[]

def cfgDialect : Core.CFG.Dialect ValKind OpExt where
  mapValues := mapCfgPayload
  values := cfgPayloadValues
  payloadEq := fun left right => left == right

end ProofForge.Wasm.Near.Ops
