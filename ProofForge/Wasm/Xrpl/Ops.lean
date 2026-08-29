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
