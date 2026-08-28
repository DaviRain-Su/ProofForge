import ProofForge.Evm.StaticStorage
import ProofForge.Evm.Ops

namespace ProofForge.Evm.StaticStorage.Emit

private def nl : String := "\n"

/-- Narrow resolver supplied by the main emitter. The component never sees the whole program and
cannot accept a raw source slot; the resolver validates both field membership and UInt64 width. -/
structure Context (σ : Type) where
  materialize : Ops.Val → σ → Except String (String × String × σ)
  resolveU64Slot : String → Except String Nat
  indent : String

def emitCall (context : Context σ) (call : StaticStorage.Call Ops.Val) (st : σ) :
    Except String (String × String × σ) := do
  match call with
  | .storeU64 field value =>
      let slot ← context.resolveU64Slot field
      let (pre, rendered, st') ← context.materialize value st
      return (pre ++ context.indent ++ "sstore(" ++ toString slot ++ ", " ++ rendered ++ ")" ++ nl,
        rendered, st')

end ProofForge.Evm.StaticStorage.Emit
