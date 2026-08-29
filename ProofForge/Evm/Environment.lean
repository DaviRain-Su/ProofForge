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
  | gasPrice256 (limb : Nat)
  | blobBaseFee256 (limb : Nat)
  | blobHash32 (limb : Nat)
  | selector4
  | calldataSize
  | coinbase20 (limb : Nat)
  | origin20 (limb : Nat)
  | blockHash256 (limb : Nat)
  | codeSize20
  | codeHash32 (limb : Nat)
  | balance256 (limb : Nat)
  deriving BEq, Repr, Inhabited

def Query.arity : Query → Nat
  | .blockHash256 _ | .blobHash32 _ => 1
  | .codeSize20 | .codeHash32 _ | .balance256 _ => 3
  | _ => 0

def Query.wellFormed : Query → Bool
  | .gasLeft256 limb | .baseFee256 limb | .prevRandao256 limb | .gasLimit256 limb
  | .gasPrice256 limb | .blobBaseFee256 limb | .blobHash32 limb =>
      limb ≤ 3
  | .selector4 | .calldataSize => true
  | .coinbase20 limb | .origin20 limb => limb ≤ 2
  | .blockHash256 limb => limb ≤ 3
  | .codeSize20 => true
  | .codeHash32 limb => limb ≤ 3
  | .balance256 limb => limb ≤ 3

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
  | .gasPrice256 limb =>
      if operands.isEmpty then s!"env.gasPrice256.{limb}"
      else s!"invalid-env.gasPrice256.{limb}-{operands.size}"
  | .blobBaseFee256 limb =>
      if operands.isEmpty then s!"env.blobBaseFee256.{limb}"
      else s!"invalid-env.blobBaseFee256.{limb}-{operands.size}"
  | .blobHash32 limb =>
      match operands with
      | #[index] => s!"env.blobHash32.{limb}({_renderValue index})"
      | _ => s!"invalid-env.blobHash32.{limb}-{operands.size}"
  | .selector4 =>
      if operands.isEmpty then "env.selector4"
      else s!"invalid-env.selector4-{operands.size}"
  | .calldataSize =>
      if operands.isEmpty then "env.calldataSize"
      else s!"invalid-env.calldataSize-{operands.size}"
  | .coinbase20 limb =>
      if operands.isEmpty then s!"env.coinbase20.{limb}"
      else s!"invalid-env.coinbase20.{limb}-{operands.size}"
  | .origin20 limb =>
      if operands.isEmpty then s!"env.origin20.{limb}"
      else s!"invalid-env.origin20.{limb}-{operands.size}"
  | .blockHash256 limb =>
      match operands with
      | #[number] => s!"env.blockHash256.{limb}({_renderValue number})"
      | _ => s!"invalid-env.blockHash256.{limb}-{operands.size}"
  | .codeSize20 =>
      match operands with
      | #[w0, w1, w2] => s!"env.codeSize20({_renderValue w0},{_renderValue w1},{_renderValue w2})"
      | _ => s!"invalid-env.codeSize20-{operands.size}"
  | .codeHash32 limb =>
      match operands with
      | #[w0, w1, w2] =>
          s!"env.codeHash32.{limb}({_renderValue w0},{_renderValue w1},{_renderValue w2})"
      | _ => s!"invalid-env.codeHash32.{limb}-{operands.size}"
  | .balance256 limb =>
      match operands with
      | #[w0, w1, w2] =>
          s!"env.balance256.{limb}({_renderValue w0},{_renderValue w1},{_renderValue w2})"
      | _ => s!"invalid-env.balance256.{limb}-{operands.size}"

end ProofForge.Evm.Environment
