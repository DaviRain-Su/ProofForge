import ProofForge.Core.Ops
import ProofForge.Core.CFG

/-!
# WASM target dialect

Third-profile value/effect extensions for the WASM slice. v0 owns nothing: XRPL Bedrock
(XLS-0101) host capability keys — ledger time, caller account, hashing — are deliberately
absent until their wasm-level import ABI is pinned (see `docs/modules/wasm.md`). `reserved`
keeps the dialect inhabited and is rejected by `wellFormed`; the registration in
`ProofForge.Wasm.IR` fails closed on every svm/evm leaf instead.
-/

namespace ProofForge.Wasm.Ops

/-- WASM-owned value intrinsics. v0 has none. -/
inductive ValKind where
  /-- Placeholder; never produced by the v0 lowering and rejected by `wellFormed`. -/
  | reserved
  deriving BEq, Repr, Inhabited

def ValKind.arity : ValKind → Nat
  | .reserved => 0

abbrev Val := ProofForge.Core.Ops.Val ValKind
abbrev Cmp := ProofForge.Core.Ops.Cmp

/-- WASM-owned effects. v0 has none. -/
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

end ProofForge.Wasm.Ops