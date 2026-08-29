import ProofForge.Core.Ops
import ProofForge.Core.CFG

/-!
# XRPL target dialect

Value/effect extensions owned by XRPL Bedrock. Environment leaves are
`host_lib` reads (caller / self / ledger); SVM/EVM leaves are rejected by
registration. `reserved` stays rejected by `wellFormed`.
-/

namespace ProofForge.Wasm.Xrpl.Ops

inductive ValKind where
  /-- Placeholder; rejected by `wellFormed` on the effect side. -/
  | reserved
  | callerW0 | callerW1 | callerW2
  | selfW0 | selfW1 | selfW2
  | ledgerSqn
  | parentTime
  /-- First little-endian UInt64 of the 32-byte parent ledger hash. -/
  | parentHashW0
  /-- `get_base_fee` zero-extended to UInt64. Not EVM `baseFee` 256. -/
  | baseFee
  /-- Compile-time ASCII seed; first little-endian UInt64 of SHA-512Half. -/
  | sha512HalfLit (seed : String)
  /-- Caller's AccountRoot.Balance as XRP drops (STAmount 57-bit mantissa). -/
  | callerBalanceDrops
  /-- Caller's AccountRoot.Sequence, UInt32 zero-extended. -/
  | callerSequence
  /-- Caller's AccountRoot.Flags, UInt32 zero-extended. -/
  | callerFlags
  /-- Caller's AccountRoot.OwnerCount, UInt32 zero-extended. Cached snapshot. -/
  | callerOwnerCount
  /-- Current ContractCall `sfSequence`, UInt32 zero-extended. Not AccountRoot.Sequence. -/
  | txSequence
  /-- Current ContractCall `sfFee` as XRP drops (STAmount 57-bit mantissa). -/
  | txFeeDrops
  deriving BEq, Repr, Inhabited

def ValKind.arity : ValKind → Nat
  | _ => 0

abbrev Val := ProofForge.Core.Ops.Val ValKind
abbrev Cmp := ProofForge.Core.Ops.Cmp

inductive OpExt (V : Type) where
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

end ProofForge.Wasm.Xrpl.Ops
