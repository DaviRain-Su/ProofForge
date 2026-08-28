namespace ProofForge.Evm.Payable

/-!
Target-local typed entry-value policy plan (EVM-RT-2c).

This module is the plan layer of the shared payable/receive policy. It names the CALLVALUE
guards and calldata routes that used to be inlined per entry in `Evm.Emit` and per effect in
`Evm.NativeFx.Emit`:

- `ValueGate.reject` — the nonpayable boundary: any nonzero CALLVALUE reverts
  (`if callvalue() { revert(0, 0) }`), spelled at the constructor prelude, at the
  runtime-wide guard when no entry is payable, and at each nonpayable selector case when one
  is;
- `ValueGate.acceptAny` — the receive effect owns any CALLVALUE and binds it for the source
  body (`let pf_recv := callvalue()`);
- `ValueGate.exact` — the deposit effects pin exact CALLVALUE equality against the
  already-materialized amount word (`if iszero(eq(callvalue(), amt)) { revert(0, 0) }`);
- `CalldataRoute.receiveEmpty` — empty calldata dispatches to the receive body
  (`if iszero(calldatasize()) { .. }`);
- `CalldataRoute.selectorDispatch` — calldata shorter than 4 bytes reverts and all remaining
  traffic dispatches on the 4-byte selector.

`EntryPlan` pairs one gate with one route and validates the combination fail closed: the
empty-calldata receive route exists only to accept value, so it requires `acceptAny`, and
`acceptAny` never serves selector dispatch. Validation is a bounded shape check with no
runtime allocation. Source-facing semantic names (`NativeFx.Source` deposit/receive, the
`Sdk` Ether APIs) and method-payable classification (`Evm.IR`'s deposit/receive effect scan)
stay owned by their existing modules; this layer names boundary contracts only. It is not a
source opcode escape hatch: no plan opens arbitrary CALL, delegatecall, create, or
callee/calldata/value selection. The native send CALL keeps its closed `Evm.NativeFx` /
`Evm.CallResult` policy and is deliberately not part of this abstraction. `Evm.Payable.Emit`
is the sole interpreter; `Evm.Emit` consumes it for the constructor, entry, and runtime
guards/routes and `Evm.NativeFx.Emit` consumes it for the deposit and receive effects.
-/

/-- Typed gate on `CALLVALUE` at one responsibility site. -/
inductive ValueGate where
  /-- Nonpayable boundary: any nonzero CALLVALUE reverts. -/
  | reject
  /-- Receive effect: any CALLVALUE is accepted and bound for the source body. -/
  | acceptAny
  /-- Deposit effects: CALLVALUE must equal the amount word supplied at emission. -/
  | exact
  deriving BEq, Repr, Inhabited

/-- Typed calldata route at the runtime entry boundary. -/
inductive CalldataRoute where
  /-- Empty calldata routes to the receive body. -/
  | receiveEmpty
  /-- Calldata shorter than 4 bytes reverts; the rest dispatches on the 4-byte selector. -/
  | selectorDispatch
  deriving BEq, Repr, Inhabited

/-- One entry boundary contract: a CALLVALUE gate paired with a calldata route. -/
structure EntryPlan where
  gate : ValueGate
  route : CalldataRoute
  deriving BEq, Repr, Inhabited

/-- Fail-closed combination gate: the empty-calldata receive route requires the accept-any
gate; selector dispatch carries either the reject gate (nonpayable) or the exact deposit
gate (payable). Every other pairing is impossible and rejected before Yul emission. -/
def EntryPlan.wellFormed (plan : EntryPlan) : Bool :=
  match plan.route, plan.gate with
  | .receiveEmpty, .acceptAny => true
  | .selectorDispatch, .reject => true
  | .selectorDispatch, .exact => true
  | _, _ => false

/-- Established nonpayable selector entry: reject any value, dispatch on the selector. -/
def EntryPlan.nonpayable : EntryPlan :=
  { gate := .reject, route := .selectorDispatch }

/-- Established payable selector entry: the deposit effect pins exact CALLVALUE equality. -/
def EntryPlan.deposit : EntryPlan :=
  { gate := .exact, route := .selectorDispatch }

/-- Established receive entry: empty calldata routes to a body that accepts any value. -/
def EntryPlan.receive : EntryPlan :=
  { gate := .acceptAny, route := .receiveEmpty }

/-- Boundary contract named by the IR-owned entry facts. `isReceive` marks the entry whose
`ixName` is `receive`; `payable` is the IR deposit/receive effect scan, which stays owned by
`Evm.IR`. The impossible combination (a receive entry that does not accept value) maps to a
deliberately malformed plan so interpretation fails closed. -/
def EntryPlan.ofEntry (isReceive payable : Bool) : EntryPlan :=
  match isReceive, payable with
  | true, true => receive
  | false, true => deposit
  | false, false => nonpayable
  | true, false => { gate := .acceptAny, route := .selectorDispatch }

end ProofForge.Evm.Payable
