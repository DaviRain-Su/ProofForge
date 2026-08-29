import ProofForge.Core.Ops
import ProofForge.Core.CFG
import ProofForge.Wasm.Near.Memory

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
  /-- Read from the one active invocation-local UInt64 buffer. -/
  | transientBuffer64Get (capacity : Nat)
  /-- Placeholder; never produced by the v0 lowering and rejected by `wellFormed`. -/
  | reserved
  deriving BEq, Repr, Inhabited

def ValKind.arity : ValKind → Nat
  | .transientBuffer64Get _ => 1
  | .reserved => 0
  | _ => 0

abbrev Val := ProofForge.Core.Ops.Val ValKind
abbrev Cmp := ProofForge.Core.Ops.Cmp

/-- NEAR-owned effects. Dynamic byte spans remain absent; v0 logging owns a bounded static
UTF-8 literal that the emitter places in deterministic linear-memory data. -/
inductive OpExt (V : Type) where
  | logUtf8 (message : String)
  | transientBuffer64Begin (capacity : Nat)
  | transientBuffer64Set (capacity : Nat) (index value : V)
  | transientBuffer64Finish (capacity : Nat)
  /-- Placeholder; never produced by the v0 lowering and rejected by `wellFormed`. -/
  | reserved
  deriving BEq, Repr, Inhabited

abbrev Op := ProofForge.Core.Ops.Op ValKind OpExt

def OpExt.wellFormed : OpExt Val → Bool
  | .logUtf8 message => message.toUTF8.size ≤ 1024
  | .transientBuffer64Begin capacity | .transientBuffer64Finish capacity =>
      Memory.buffer64CapacityValid capacity
  | .transientBuffer64Set capacity index value =>
      Memory.buffer64CapacityValid capacity &&
        index.wellFormed ValKind.arity && value.wellFormed ValKind.arity
  | .reserved => false

def Op.wellFormed (op : Op) : Bool :=
  ProofForge.Core.Ops.Op.wellFormed ValKind.arity OpExt.wellFormed op

private def mapCfgPayload (mapValue : Val → Val) : OpExt Val → OpExt Val
  | .logUtf8 message => .logUtf8 message
  | .transientBuffer64Begin capacity => .transientBuffer64Begin capacity
  | .transientBuffer64Set capacity index value =>
      .transientBuffer64Set capacity (mapValue index) (mapValue value)
  | .transientBuffer64Finish capacity => .transientBuffer64Finish capacity
  | .reserved => .reserved

private def cfgPayloadValues : OpExt Val → Array Val
  | .logUtf8 _ => #[]
  | .transientBuffer64Begin _ | .transientBuffer64Finish _ => #[]
  | .transientBuffer64Set _ index value => #[index, value]
  | .reserved => #[]

def cfgDialect : Core.CFG.Dialect ValKind OpExt where
  mapValues := mapCfgPayload
  values := cfgPayloadValues
  payloadEq := fun left right => left == right

end ProofForge.Wasm.Near.Ops
