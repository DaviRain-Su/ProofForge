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
  materialize : Ops.Val → σ → Except String (String × String × σ)
  fresh : σ → String × σ
  rememberWide : σ → String → String → σ
  lookupWide : σ → String → Option String
  valKey : Ops.Val → String
  indent : String

private def emitCachedWord (context : Context σ) (project : String → Nat → String)
    (cacheKey expression : String) (limb : Nat)
    (st : σ) : String × String × σ :=
  match context.lookupWide st cacheKey with
  | some packed =>
      let (name, next) := context.fresh st
      (context.indent ++ "let " ++ name ++ " := " ++ project packed limb ++ nl,
        name, next)
  | none =>
      let (packed, afterPacked) := context.fresh st
      let remembered := context.rememberWide afterPacked cacheKey packed
      let (name, next) := context.fresh remembered
      (context.indent ++ "let " ++ packed ++ " := " ++ expression ++ nl ++
        context.indent ++ "let " ++ name ++ " := " ++ project packed limb ++ nl,
        name, next)

/-- Convert EVM's big-endian 20-byte address word into the source Addr20 little-endian limb
representation. This is the same physical convention used by caller/self. -/
private def packAddrWord (src : String) (word : Nat) : String :=
  let rec orBytes (index remaining : Nat) (acc : String) : String :=
    match remaining with
    | 0 => acc
    | count + 1 =>
        let byteExpr := "byte(" ++ toString (12 + 8 * word + index) ++ ", " ++ src ++ ")"
        let next :=
          if index == 0 then byteExpr
          else "or(" ++ acc ++ ", shl(" ++ toString (8 * index) ++ ", " ++ byteExpr ++ "))"
        orBytes (index + 1) count next
  orBytes 0 (if word == 2 then 4 else 8) "0"

def emitQuery (context : Context σ) (query : Query) (operands : Array Ops.Val) (st : σ) :
    Except String (String × String × σ) := do
  unless query.wellFormed do throw "extract/ir: malformed EVM environment query"
  match query, operands with
  | .gasLeft256 limb, #[] =>
      return emitCachedWord context packU256Word "gas256" "gas()" limb st
  | .baseFee256 limb, #[] =>
      return emitCachedWord context packU256Word "basefee256" "basefee()" limb st
  | .prevRandao256 limb, #[] =>
      return emitCachedWord context packU256Word "randao256" "prevrandao()" limb st
  | .gasLimit256 limb, #[] =>
      return emitCachedWord context packU256Word "gaslimit256" "gaslimit()" limb st
  | .coinbase20 limb, #[] =>
      return emitCachedWord context packAddrWord "coinbase20" "coinbase()" limb st
  | .blockHash256 limb, #[number] =>
      let (prelude, value, afterValue) ← context.materialize number st
      let cacheKey := "blockhash256|" ++ context.valKey number
      let (wordPrefix, result, next) :=
        emitCachedWord context packU256Word cacheKey ("blockhash(" ++ value ++ ")") limb afterValue
      return (prelude ++ wordPrefix, result, next)
  | _, _ => throw "extract/ir: malformed EVM environment query operands"

end ProofForge.Evm.Environment.Emit
