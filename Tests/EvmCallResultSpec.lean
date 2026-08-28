import ProofForge
import ProofForge.Evm.CallResult
import ProofForge.Evm.CallResult.Emit
import Examples.Vault
import Examples.Token

namespace Tests.EvmCallResultSpec

open ProofForge.Evm

/-! Focused gates for the EVM-RT-2a typed call-result contract: plan-layer shape gates,
byte-exact emission goldens for each policy, fail-closed emission errors, and ClosedCall /
Component consumer regression (including the existing Vault and Token structural gates). -/

-- Plan layer: every policy keeps returndata bounded to one 32-byte word.
#guard CallResult.Policy.retBound .nonzeroWordOrEmpty == 32
#guard CallResult.Policy.retBound .exactWord == 32
#guard CallResult.Policy.retBound .ignored == 0
#guard [CallResult.Policy.nonzeroWordOrEmpty, .exactWord, .ignored].all
  (fun p => Nat.ble (CallResult.Policy.retBound p) 32)

-- Plan layer: established constructors are well-formed; msg.value on a STATICCALL is not.
#guard (CallResult.Request.erc20Mutation 68).wellFormed
#guard (CallResult.Request.erc20Mutation 100).wellFormed
#guard (CallResult.Request.erc20Mutation 228).wellFormed
#guard (CallResult.Request.staticWord 36).wellFormed
#guard (CallResult.Request.staticWord 68).wellFormed
#guard (CallResult.Request.successOnly 4 true).wellFormed
#guard (CallResult.Request.successOnly 260).wellFormed
#guard !({ kind := .staticcall, inSize := 36, policy := .exactWord, value := true } :
    CallResult.Request).wellFormed
#guard (CallResult.Request.erc20Mutation 68).retBound == 32
#guard (CallResult.Request.successOnly 292).retBound == 0

private def mockCtx : CallResult.Emit.Context Nat :=
  { fresh := fun st => (s!"v{st}", st + 1), indent := "  " }

-- Emission golden: ERC-20 compatibility rule (CALL success + returndata empty or one nonzero
-- return word), byte-exact.
#guard
  match CallResult.Emit.emit mockCtx (.erc20Mutation 68) "tok" none 0 with
  | .error _ => false
  | .ok (txt, word, st) =>
      txt ==
        "  let v0 := call(gas(), tok, 0, 0, 68, 0, 32)\n" ++
        "  if iszero(v0) { revert(0, 0) }\n" ++
        "  let v1 := returndatasize()\n" ++
        "  if and(iszero(eq(v1, 0)), iszero(eq(v1, 32))) { revert(0, 0) }\n" ++
        "  if eq(v1, 32) { if iszero(mload(0)) { revert(0, 0) } }\n" &&
        word == none && st == 2

-- Emission golden: exact-one-word STATICCALL read, byte-exact; the word is bound.
#guard
  match CallResult.Emit.emit mockCtx (.staticWord 36) "tok" none 0 with
  | .error _ => false
  | .ok (txt, word, st) =>
      txt ==
        "  let v0 := staticcall(gas(), tok, 0, 36, 0, 32)\n" ++
        "  if iszero(v0) { revert(0, 0) }\n" ++
        "  if iszero(eq(returndatasize(), 32)) { revert(0, 0) }\n" ++
        "  let v1 := mload(0)\n" &&
        word == some "v1" && st == 2

-- Emission golden: success-only CALL carrying msg.value; returndata is never touched.
#guard
  match CallResult.Emit.emit mockCtx (.successOnly 4 true) "tok" (some "amt") 0 with
  | .error _ => false
  | .ok (txt, word, st) =>
      txt ==
        "  let v0 := call(gas(), tok, amt, 0, 4, 0, 0)\n" ++
        "  if iszero(v0) { revert(0, 0) }\n" &&
        !txt.contains "returndatasize" && word == none && st == 1

-- Fail closed at emission: unexpected or missing msg.value expression.
#guard
  match CallResult.Emit.emit mockCtx (.erc20Mutation 68) "tok" (some "amt") 0 with
  | .error reason => reason.contains "value shape"
  | .ok _ => false
#guard
  match CallResult.Emit.emit mockCtx (.successOnly 4 true) "tok" none 0 with
  | .error reason => reason.contains "value shape"
  | .ok _ => false

-- Fail closed at emission: msg.value on a STATICCALL request is not well-formed.
#guard
  match CallResult.Emit.emit mockCtx
      { kind := .staticcall, inSize := 36, policy := .exactWord, value := true }
      "tok" (some "amt") 0 with
  | .error reason => reason.contains "request shape"
  | .ok _ => false

private def mockClosedCtx : ClosedCall.Emit.Context Nat :=
  { materialize := fun _ st => .ok ("", "0", st)
    fresh := fun st => (s!"v{st}", st + 1)
    rememberWide := fun st _ _ => st
    lookupWide := fun _ _ => none
    valKey := fun _ => ""
    indent := "  " }

private def lit : Ops.Val := .lit 0

-- ClosedCall mutation consumes the shared contract: the emitted transfer contains exactly the
-- fragment the shared interpreter produces at the same state.
#guard
  match CallResult.Emit.emit mockCtx (.erc20Mutation 68) "v0" none 1,
        ClosedCall.Emit.emitCall mockClosedCtx (.transfer lit lit lit lit lit lit lit) 0 with
  | .ok (fragment, _, _), .ok (txt, _, st) => txt.contains fragment && st == 3
  | _, _ => false

-- ClosedCall query consumes the shared contract: balance256 contains the exact-one-word
-- STATICCALL fragment and exposes the bound word through the limb selector.
#guard
  match CallResult.Emit.emit mockCtx (.staticWord 36) "v0" none 1,
        ClosedCall.Emit.emitQuery mockClosedCtx (.balance256 0) #[lit, lit, lit] 0 with
  | .ok (fragment, _, _), .ok (txt, _, _) =>
      txt.contains fragment && txt.contains "and(shr(0, v2), 0xffffffffffffffff)"
  | _, _ => false

-- Component bridge still routes closed calls into the shared contract.
#guard
  match Component.Emit.emitCall
      { materialize := fun _ st => .ok ("", "0", st)
        fresh := fun st => (s!"v{st}", st + 1)
        rememberWide := fun st _ _ => st
        lookupWide := fun _ _ => none
        valKey := fun _ => ""
        indent := "  " }
      (.closedCall (.transfer lit lit lit lit lit lit lit) : Component.Call Ops.Val) 0 with
  | .error _ => false
  | .ok (txt, _, _) =>
      txt.contains " := call(gas(), " && txt.contains " := returndatasize()" &&
        txt.contains " { if iszero(mload(0)) { revert(0, 0) } }"

-- Existing consumer regression: Vault and Token keep the shared gate spellings.
#guard
  match Emit.emitYul ProofForge.Evm.Golden.extractedVault with
  | .error _ => false
  | .ok yul =>
      yul.contains " := call(gas(), " &&
        yul.contains " := staticcall(gas(), " &&
        yul.contains " := returndatasize()" &&
        yul.contains "if and(iszero(eq(" &&
        yul.contains " { if iszero(mload(0)) { revert(0, 0) } }" &&
        yul.contains "if iszero(eq(returndatasize(), 32)) { revert(0, 0) }"

#guard
  match Emit.emitYul ProofForge.Evm.Golden.extractedToken with
  | .error _ => false
  | .ok yul =>
      yul.contains "staticcall(gas(), 1," &&
        !yul.contains " := returndatasize()"

-- Consumer component/IR identity is preserved (registry digests).
#guard IR.digestHex ProofForge.Evm.Golden.extractedVault == "a3ea1b5b2a69c0e3"
#guard IR.digestHex ProofForge.Evm.Golden.extractedToken == "4da7ac248a0fb556"

end Tests.EvmCallResultSpec
