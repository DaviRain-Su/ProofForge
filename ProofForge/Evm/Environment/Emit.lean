import ProofForge.Evm.Environment
import ProofForge.Evm.Ops

namespace ProofForge.Evm.Environment.Emit

private def nl : String := "\n"
private def u64MaxYul : String := "0xffffffffffffffff"

private def packU256Word (src : String) (limb : Nat) : String :=
  "and(shr(" ++ toString (64 * limb) ++ ", " ++ src ++ "), " ++ u64MaxYul ++ ")"

/-- The generic component emitter supplies the same fresh-name and wide-word cache used by all
other full-width target components. -/
structure Context (σ : Type) where
  fresh : σ → String × σ
  rememberWide : σ → String → String → σ
  lookupWide : σ → String → Option String
  indent : String

private def emitPackedWord (context : Context σ) (cacheKey expression : String) (limb : Nat)
    (st : σ) : String × String × σ :=
  match context.lookupWide st cacheKey with
  | some packed =>
      let (name, next) := context.fresh st
      (context.indent ++ "let " ++ name ++ " := " ++ packU256Word packed limb ++ nl,
        name, next)
  | none =>
      let (packed, afterPacked) := context.fresh st
      let remembered := context.rememberWide afterPacked cacheKey packed
      let (name, next) := context.fresh remembered
      (context.indent ++ "let " ++ packed ++ " := " ++ expression ++ nl ++
        context.indent ++ "let " ++ name ++ " := " ++ packU256Word packed limb ++ nl,
        name, next)

def emitQuery (context : Context σ) (query : Query) (operands : Array Ops.Val) (st : σ) :
    Except String (String × String × σ) := do
  unless operands.isEmpty && query.wellFormed do
    throw "extract/ir: malformed EVM environment query"
  return match query with
    | .gasLeft256 limb => emitPackedWord context "gas256" "gas()" limb st
    | .baseFee256 limb => emitPackedWord context "basefee256" "basefee()" limb st
    | .prevRandao256 limb => emitPackedWord context "randao256" "prevrandao()" limb st
    | .gasLimit256 limb => emitPackedWord context "gaslimit256" "gaslimit()" limb st

end ProofForge.Evm.Environment.Emit
