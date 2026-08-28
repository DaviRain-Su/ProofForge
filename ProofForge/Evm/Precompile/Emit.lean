import ProofForge.Evm.CallResult.Emit
import ProofForge.Evm.Precompile

namespace ProofForge.Evm.Precompile.Emit

/-!
Sole interpreter for the typed ecrecover precompile plan (EVM-RT-2d).

`emit` is the only spelling of the closed ecrecover contract:

1. the STATICCALL to the fixed precompile address with the fixed 128-byte input frame at
   `memory[0, 128)` and the fixed 32-byte output word at `memory[0, 32)`, the fail-closed
   success gate, and the exact-32-byte returndata gate — rendered by the shared
   `Evm.CallResult.Emit` interpreter (`Request.staticWord`) so the call, success, and
   return-size gates keep exactly one spelling across the target;
2. the fail-closed nonzero gate on the recovered address word, spelled here because it is
   precompile-specific and not part of the generic call-result policy.

The caller (the ClosedCall permit emitter) owns input-frame construction; the interpreter
consumes no operands and touches no memory beyond the fixed call geometry. Fresh-name
allocation order (`ok`, then the returned word) is inherited from `Evm.CallResult.Emit` so
consumers observe no naming drift beyond the plan itself. Malformed plans — any address,
input, or output geometry other than the fixed ecrecover contract, or any missing gate —
fail closed with an `extract/unsupported` error instead of emitting. Memory stays fixed and
compile-time planned: no dynamic allocation, unbounded bytes, or hidden persistent state.
-/

private def nl : String := "\n"
private def revert0 : String := "revert(0, 0)"

/-- Minimal emission context shared by component emitters: fresh Yul names and indentation. -/
structure Context (σ : Type) where
  fresh : σ → String × σ
  indent : String

/-- Emit one validated ecrecover plan: the STATICCALL, success, exact-output, and nonzero
gates, binding the recovered address word for the caller. -/
def emit (context : Context σ) (plan : Precompile.Plan) (st : σ) :
    Except String (String × String × σ) := do
  if !plan.wellFormed then
    throw "extract/unsupported: evm precompile plan shape"
  let (callTxt, word, st1) ← CallResult.Emit.emit
    { fresh := context.fresh, indent := context.indent }
    (.staticWord plan.inputBytes) (toString plan.address) none st
  let some ret := word
    | throw "extract/unsupported: evm precompile missing word"
  return (callTxt ++
    context.indent ++ "if iszero(" ++ ret ++ ") { " ++ revert0 ++ " }" ++ nl, ret, st1)

end ProofForge.Evm.Precompile.Emit
