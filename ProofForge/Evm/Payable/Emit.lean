import ProofForge.Evm.Payable

namespace ProofForge.Evm.Payable.Emit

/-!
Sole interpreter for the typed entry-value policy plans (EVM-RT-2c).

`emitValueGate` is the only spelling of the CALLVALUE gates:

1. `reject` — `if callvalue() { revert(0, 0) }` at the constructor prelude, the runtime-wide
   nonpayable guard, and each nonpayable selector case;
2. `acceptAny` — `let pf_recv := callvalue()`, the receive effect binding; the fixed name is
   part of the spelling and is handed back to the consumer;
3. `exact` — `if iszero(eq(callvalue(), amt)) { revert(0, 0) }`, the deposit effect gate.

`emitReceiveRoute` is the only spelling of the empty-calldata receive route: the plan must
name `acceptAny` on `receiveEmpty`, then the already-emitted body is wrapped in
`if iszero(calldatasize()) { .. }`. `emitSelectorHead` is the only spelling of the
selector-dispatch head: short calldata reverts, then the switch on the 4-byte selector.

Gates and routes consume already-materialized Yul words, so the interpreter allocates no
fresh names and threads no emitter state; the context is indentation only, which keeps every
consumer byte-exact with the previous inline spellings. Malformed requests (a missing or
empty amount on `exact`, an unexpected amount on `reject`/`acceptAny`, an impossible
gate/route pairing) fail closed with an `extract/unsupported` error instead of emitting.
-/

private def nl : String := "\n"
private def revert0 : String := "revert(0, 0)"

/-- Minimal emission context shared by entry and effect emitters: indentation only. Plans
consume already-materialized words, so no fresh-name or materialization state is required. -/
structure Context where
  indent : String

/-- Emit one validated CALLVALUE gate. `amount` is the already-materialized deposit amount
word and must be present exactly when `gate` is `.exact`. -/
def emitValueGate (context : Context) (gate : ValueGate) (amount : Option String := none) :
    Except String String := do
  let indent := context.indent
  match gate, amount with
  | .reject, none =>
      return indent ++ "if callvalue() { " ++ revert0 ++ " }" ++ nl
  | .acceptAny, none =>
      return indent ++ "let pf_recv := callvalue()" ++ nl
  | .exact, some amt =>
      if amt.isEmpty then
        throw "extract/unsupported: evm value gate shape"
      return indent ++ "if iszero(eq(callvalue(), " ++ amt ++ ")) { " ++ revert0 ++
        " }" ++ nl
  | _, _ => throw "extract/unsupported: evm value gate shape"

/-- Wrap an already-emitted receive body in the empty-calldata route named by `plan`. The
plan must pair the accept-any gate with the receive route; anything else fails closed. -/
def emitReceiveRoute (context : Context) (plan : EntryPlan) (body : String) :
    Except String String := do
  if !plan.wellFormed || plan.route != .receiveEmpty then
    throw "extract/unsupported: evm entry policy shape"
  return context.indent ++ "if iszero(calldatasize()) {" ++ nl ++ body ++
    context.indent ++ "}" ++ nl

/-- Emit the validated selector-dispatch route: calldata shorter than 4 bytes reverts, then
the switch on the 4-byte selector. The receive route is owned by `emitReceiveRoute` and fails
closed here rather than being silently rendered as selector dispatch. -/
def emitSelectorHead (context : Context) (route : CalldataRoute) : Except String String := do
  if route != .selectorDispatch then
    throw "extract/unsupported: evm calldata route shape"
  return context.indent ++ "if lt(calldatasize(), 4) { " ++ revert0 ++ " }" ++ nl ++
    context.indent ++ "switch shr(224, calldataload(0))" ++ nl

end ProofForge.Evm.Payable.Emit
