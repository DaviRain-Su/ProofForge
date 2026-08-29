import ProofForge
import ProofForge.Evm.Payable
import ProofForge.Evm.Payable.Emit
import Examples.TipJar
import Examples.Vault

namespace Tests.EvmPayableSpec

open ProofForge.Evm

/-! Focused gates for the EVM-RT-2c typed entry-value policy: plan-layer combination gates,
byte-exact emission goldens for the reject/accept-any/exact CALLVALUE gates and the
receive/selector calldata routes, fail-closed emission errors for malformed plans, and
NativeFx / Evm.Emit consumer regression (including the existing TipJar and Vault structural
gates). Plan-level coverage names boundary contracts only; it does not open any new
source-level value or routing API. -/

-- Plan layer: the established entry contracts are well-formed.
#guard Payable.EntryPlan.nonpayable.wellFormed
#guard Payable.EntryPlan.deposit.wellFormed
#guard Payable.EntryPlan.receive.wellFormed

-- Plan layer: impossible gate/route combinations fail closed (a receive route that does not
-- accept value; accept-any serving selector dispatch).
#guard !({ gate := .reject, route := .receiveEmpty } : Payable.EntryPlan).wellFormed
#guard !({ gate := .exact, route := .receiveEmpty } : Payable.EntryPlan).wellFormed
#guard !({ gate := .acceptAny, route := .selectorDispatch } : Payable.EntryPlan).wellFormed

-- Plan layer: classification from the IR-owned entry facts; the impossible receive/nonpayable
-- pairing maps to a malformed plan.
#guard Payable.EntryPlan.ofEntry false false == .nonpayable
#guard Payable.EntryPlan.ofEntry false true == .deposit
#guard Payable.EntryPlan.ofEntry true true == .receive
#guard !(Payable.EntryPlan.ofEntry true false).wellFormed

private def mockCtx : Payable.Emit.Context := { indent := "  " }

-- Emission golden: nonpayable reject gate, byte-exact. Zero value passes; any nonzero value
-- reverts. The constructor prelude, the runtime-wide guard, and each nonpayable selector
-- case share this one spelling at their own indentation.
#guard
  match Payable.Emit.emitValueGate mockCtx .reject with
  | .error _ => false
  | .ok txt => txt == "  if callvalue() { revert(0, 0) }\n" && !txt.contains "eq(callvalue()"
#guard
  match Payable.Emit.emitValueGate { indent := "    " } .reject,
        Payable.Emit.emitValueGate { indent := "      " } .reject,
        Payable.Emit.emitValueGate { indent := "        " } .reject with
  | .ok ctor, .ok global, .ok entryGuard =>
      ctor == "    if callvalue() { revert(0, 0) }\n" &&
        global == "      if callvalue() { revert(0, 0) }\n" &&
        entryGuard == "        if callvalue() { revert(0, 0) }\n"
  | _, _, _ => false

-- Emission golden: receive accept-any gate binds CALLVALUE under the fixed `pf_recv` name.
#guard
  match Payable.Emit.emitValueGate mockCtx .acceptAny with
  | .error _ => false
  | .ok txt => txt == "  let pf_recv := callvalue()\n"

-- Emission golden: exact deposit gate, byte-exact.
#guard
  match Payable.Emit.emitValueGate mockCtx .exact (some "amt") with
  | .error _ => false
  | .ok txt => txt == "  if iszero(eq(callvalue(), amt)) { revert(0, 0) }\n"

-- Emission golden: empty calldata routes to the receive body; the route wraps the
-- already-emitted body byte-exact.
#guard
  match Payable.Emit.emitReceiveRoute mockCtx .receive "    body\n" with
  | .error _ => false
  | .ok txt => txt == "  if iszero(calldatasize()) {\n    body\n  }\n"

-- Emission golden: nonempty calldata falls through to selector dispatch; short calldata
-- reverts. Byte-exact.
#guard
  match Payable.Emit.emitSelectorHead mockCtx .selectorDispatch with
  | .error _ => false
  | .ok txt => txt ==
      "  if lt(calldatasize(), 4) { revert(0, 0) }\n  switch shr(224, calldataload(0))\n"
#guard
  match Payable.Emit.emitSelectorHead mockCtx .receiveEmpty with
  | .error reason => reason.contains "calldata route shape"
  | .ok _ => false

-- Fail closed at emission: malformed value-gate operands (missing, empty, or unexpected
-- amount word).
#guard
  match Payable.Emit.emitValueGate mockCtx .exact none with
  | .error reason => reason.contains "value gate shape"
  | .ok _ => false
#guard
  match Payable.Emit.emitValueGate mockCtx .exact (some "") with
  | .error reason => reason.contains "value gate shape"
  | .ok _ => false
#guard
  match Payable.Emit.emitValueGate mockCtx .reject (some "amt") with
  | .error reason => reason.contains "value gate shape"
  | .ok _ => false
#guard
  match Payable.Emit.emitValueGate mockCtx .acceptAny (some "amt") with
  | .error reason => reason.contains "value gate shape"
  | .ok _ => false

-- Fail closed at emission: malformed receive-route plans.
#guard
  match Payable.Emit.emitReceiveRoute mockCtx .nonpayable "" with
  | .error reason => reason.contains "entry policy shape"
  | .ok _ => false
#guard
  match Payable.Emit.emitReceiveRoute mockCtx .deposit "" with
  | .error reason => reason.contains "entry policy shape"
  | .ok _ => false
#guard
  match Payable.Emit.emitReceiveRoute mockCtx
      { gate := .acceptAny, route := .selectorDispatch } "" with
  | .error reason => reason.contains "entry policy shape"
  | .ok _ => false

private def lit : Ops.Val := .lit 0

private def mockNativeCtx : NativeFx.Emit.Context Nat :=
  { materialize := fun _ st => .ok ("", "0", st)
    fresh := fun st => (s!"v{st}", st + 1)
    indent := "  " }

-- Consumer regression: the NativeFx deposit effect consumes the shared exact gate,
-- byte-exact, and allocates no fresh names.
#guard
  match Payable.Emit.emitValueGate mockCtx .exact (some "0"),
        NativeFx.Emit.emitCall mockNativeCtx (.deposit lit) 0 with
  | .ok fragment, .ok (txt, ret, st) => txt == fragment && ret == "0" && st == 0
  | _, _ => false

-- Consumer regression: the NativeFx packed deposit consumes the shared exact gate after the
-- pack binding, byte-exact.
#guard
  match NativeFx.Emit.emitCall mockNativeCtx (.deposit256 lit lit lit lit) 0 with
  | .error _ => false
  | .ok (txt, ret, st) =>
      txt == "  let v0 := or(or(0, shl(64, 0)), or(shl(128, 0), shl(192, 0)))\n" ++
          "  if iszero(eq(callvalue(), v0)) { revert(0, 0) }\n" &&
        ret == "0" && st == 1

-- Consumer regression: the NativeFx receive effect consumes the shared accept-any gate and
-- hands the fixed binding name back, byte-exact.
#guard
  match Payable.Emit.emitValueGate mockCtx .acceptAny,
        NativeFx.Emit.emitCall mockNativeCtx .receive 0 with
  | .ok fragment, .ok (txt, ret, st) => txt == fragment && ret == "pf_recv" && st == 0
  | _, _ => false

-- Existing consumer regression: TipJar keeps every guard/route spelling byte-exact — the
-- constructor reject guard, the empty-calldata receive route with its accept-any binding,
-- the selector-dispatch head, the per-case reject guards, and the exact deposit gate — with
-- no runtime-wide guard while a payable entry exists.
#guard
  match Emit.emitYul ProofForge.Evm.Golden.extractedTipJar with
  | .error _ => false
  | .ok yul =>
      yul.contains "    if callvalue() { revert(0, 0) }\n    let programSize" &&
        yul.contains "      if iszero(calldatasize()) {\n" &&
        yul.contains "        let pf_recv := callvalue()\n" &&
        yul.contains
          "      if lt(calldatasize(), 4) { revert(0, 0) }\n      switch shr(224, calldataload(0))\n" &&
        yul.contains "        if callvalue() { revert(0, 0) }\n" &&
        yul.contains "if iszero(eq(callvalue(), " &&
        !yul.contains "\n      if callvalue() { revert(0, 0) }"

-- Existing consumer regression: Vault keeps the receive route, the exact packed-deposit gate,
-- and the closed WETH value CALL (which stays outside the entry-value abstraction).
#guard
  match Emit.emitYul ProofForge.Evm.Golden.extractedVault with
  | .error _ => false
  | .ok yul =>
      yul.contains "      if iszero(calldatasize()) {\n" &&
        yul.contains "        let pf_recv := callvalue()\n" &&
        yul.contains "if iszero(eq(callvalue(), " &&
        yul.contains " := call(gas(), " &&
        !yul.contains "\n      if callvalue() { revert(0, 0) }"

-- ABI regression: payable labels and the receive entry are unchanged.
#guard
  let abi := Emit.emitAbi ProofForge.Evm.Golden.extractedTipJar
  abi.contains "\"stateMutability\":\"payable\"" &&
    abi.contains "{\"type\":\"receive\",\"stateMutability\":\"payable\"}" &&
    !abi.contains "\"name\":\"receive\""

-- Consumer component/IR identity is preserved (registry digests).
#guard IR.digestHex ProofForge.Evm.Golden.extractedTipJar == "1582f2173f9b97b7"
#guard IR.digestHex ProofForge.Evm.Golden.extractedVault == "a3ea1b5b2a69c0e3"

end Tests.EvmPayableSpec
