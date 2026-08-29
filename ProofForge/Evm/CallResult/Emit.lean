import ProofForge.Evm.CallResult

namespace ProofForge.Evm.CallResult.Emit

/-!
Emitter interpreter for the typed call-result contract (EVM-RT-2a).

`emit` is the sole spelling of the closed external-call result gates:

1. the `call`/`staticcall` instruction itself, with calldata at `memory[0, inSize)` and
   returndata copied to `memory[0, retBound)` (`retBound ≤ 32`);
2. the fail-closed success gate `if iszero(ok) { revert(0, 0) }`;
3. the policy tail:
   - `canonicalTrueOrCodeBackedEmpty` binds `rds := returndatasize()`, accepts exactly one word only
     when it equals canonical ABI `true`, and accepts empty data only when the target still has
     runtime code after the call;
   - `exactWord` reverts unless `returndatasize() = 32` and binds the returned word;
   - `contractSuccess` never copies or consumes returndata, but an empty result requires runtime
     code at the target after the call.

Malformed requests (returndata beyond one word, msg.value on a STATICCALL, a missing or
unexpected value expression) fail closed with an `extract/unsupported` error instead of
emitting. Fresh-name allocation order (`ok`, then the policy temporaries) is part of the
contract so consumers observe no naming drift.
-/

private def nl : String := "\n"
private def revert0 : String := "revert(0, 0)"
private def abiWordSize : String := toString CallResult.abiWordBytes

/-- Minimal emission context shared by component emitters: fresh Yul names and indentation. -/
structure Context (σ : Type) where
  fresh : σ → String × σ
  indent : String

/-- Emit one closed external call and its typed fail-closed result gates. `target` is the
already-materialized callee word; `value` is the msg.value expression and must be present
exactly when `request.value` holds. -/
def emit (context : Context σ) (request : CallResult.Request) (target : String)
    (value : Option String) (st : σ) : Except String (String × Option String × σ) := do
  if !(request.wellFormed) then
    throw "extract/unsupported: evm call-result request shape"
  if request.value != value.isSome then
    throw "extract/unsupported: evm call-result value shape"
  let indent := context.indent
  let (ok, st1) := context.fresh st
  let invoke := match request.kind, value with
    | .call, some val =>
        "call(gas(), " ++ target ++ ", " ++ val ++ ", 0, " ++ toString request.inSize ++
          ", 0, " ++ toString request.retBound ++ ")"
    | .call, none =>
        "call(gas(), " ++ target ++ ", 0, 0, " ++ toString request.inSize ++
          ", 0, " ++ toString request.retBound ++ ")"
    | .staticcall, _ =>
        "staticcall(gas(), " ++ target ++ ", 0, " ++ toString request.inSize ++
          ", 0, " ++ toString request.retBound ++ ")"
  let head :=
    indent ++ "let " ++ ok ++ " := " ++ invoke ++ nl ++
    indent ++ "if iszero(" ++ ok ++ ") { " ++ revert0 ++ " }" ++ nl
  match request.policy with
  | .contractSuccess =>
      return (head ++
        indent ++ "if and(iszero(returndatasize()), iszero(extcodesize(" ++ target ++ "))) { " ++
          revert0 ++ " }" ++ nl, none, st1)
  | .exactWord =>
      let (word, st2) := context.fresh st1
      return (head ++
        indent ++ "if iszero(eq(returndatasize(), " ++ abiWordSize ++ ")) { " ++
          revert0 ++ " }" ++ nl ++
        indent ++ "let " ++ word ++ " := mload(0)" ++ nl, some word, st2)
  | .canonicalTrueOrCodeBackedEmpty =>
      let (rds, st2) := context.fresh st1
      return (head ++
        indent ++ "let " ++ rds ++ " := returndatasize()" ++ nl ++
        indent ++ "switch " ++ rds ++ nl ++
        indent ++ "case 0 { if iszero(extcodesize(" ++ target ++ ")) { " ++ revert0 ++ " } }" ++ nl ++
        indent ++ "case " ++ abiWordSize ++ " { if iszero(eq(mload(0), 1)) { " ++ revert0 ++
          " } }" ++ nl ++
        indent ++ "default { " ++ revert0 ++ " }" ++ nl, none, st2)

end ProofForge.Evm.CallResult.Emit
