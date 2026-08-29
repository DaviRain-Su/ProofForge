/-!
# EVM execution environment queries

Target-owned component vocabulary for full-width environment observations. Generic EVM Ops, IR,
CFG, and the main emitter see only the existing Component query bridge; adding another bounded
environment opcode does not require another top-level value constructor or main-emitter recipe.

Every result is represented by allocation-free `UInt64` limbs. The emitter captures the EVM word
once and projects all address or UInt256 limbs from the same cached observation. These queries have
no storage, log, call, or allocation effect.
-/

namespace ProofForge.Evm.Environment

inductive Query where
  | gasLeft256 (limb : Nat)
  | baseFee256 (limb : Nat)
  | prevRandao256 (limb : Nat)
  | gasLimit256 (limb : Nat)
  | coinbase20 (limb : Nat)
  | blockHash256 (limb : Nat)
  deriving BEq, Repr, Inhabited

def Query.arity : Query → Nat
  | .blockHash256 _ => 1
  | _ => 0

def Query.wellFormed : Query → Bool
  | .gasLeft256 limb | .baseFee256 limb | .prevRandao256 limb | .gasLimit256 limb =>
      limb ≤ 3
  | .coinbase20 limb => limb ≤ 2
  | .blockHash256 limb => limb ≤ 3

/-- Preserve the pre-component canonical spelling so this ownership refactor does not change
program digests. -/
def Query.canonical (_renderValue : V → String) (operands : Array V) : Query → String
  | .gasLeft256 limb =>
      if operands.isEmpty then s!"egas.{limb}" else s!"invalid-egas.{limb}-{operands.size}"
  | .baseFee256 limb =>
      if operands.isEmpty then s!"ebasefee.{limb}"
      else s!"invalid-ebasefee.{limb}-{operands.size}"
  | .prevRandao256 limb =>
      if operands.isEmpty then s!"erandao.{limb}"
      else s!"invalid-erandao.{limb}-{operands.size}"
  | .gasLimit256 limb =>
      if operands.isEmpty then s!"egaslimit.{limb}"
      else s!"invalid-egaslimit.{limb}-{operands.size}"
  | .coinbase20 limb =>
      if operands.isEmpty then s!"env.coinbase20.{limb}"
      else s!"invalid-env.coinbase20.{limb}-{operands.size}"
  | .blockHash256 limb =>
      match operands with
      | #[number] => s!"env.blockHash256.{limb}({_renderValue number})"
      | _ => s!"invalid-env.blockHash256.{limb}-{operands.size}"

end ProofForge.Evm.Environment
