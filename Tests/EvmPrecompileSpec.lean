import ProofForge
import ProofForge.Evm.Precompile
import ProofForge.Evm.Precompile.Emit
import Examples.Evm.Token

namespace Tests.EvmPrecompileSpec

open ProofForge.Evm

/-! Focused gates for the EVM-RT-2d typed ecrecover precompile contract: plan-layer shape
gates, a byte-exact emission golden, fail-closed emission errors for malformed plans, and
ClosedCall / Token consumer regression. Plan-level coverage names only the fixed ecrecover
contract; it does not claim any arbitrary precompile or STATICCALL source API. -/

-- Plan layer: fixed ecrecover geometry is explicit.
#guard Precompile.ecrecoverAddress == 1
#guard Precompile.ecrecoverInputBytes == 128
#guard Precompile.ecrecoverOutputBytes == 32

-- Plan layer: the established ecrecover plan is well-formed.
#guard Precompile.Plan.ecrecover.wellFormed

-- Plan layer: malformed address fails closed (only fixed precompile address 0x01).
#guard !({ Precompile.Plan.ecrecover with address := 0 }.wellFormed)
#guard !({ Precompile.Plan.ecrecover with address := 2 }.wellFormed)
#guard !({ Precompile.Plan.ecrecover with address := 9 }.wellFormed)

-- Plan layer: malformed input/output geometry fails closed (fixed 128-byte frame, fixed
-- 32-byte output).
#guard !({ Precompile.Plan.ecrecover with inputBytes := 0 }.wellFormed)
#guard !({ Precompile.Plan.ecrecover with inputBytes := 127 }.wellFormed)
#guard !({ Precompile.Plan.ecrecover with inputBytes := 129 }.wellFormed)
#guard !({ Precompile.Plan.ecrecover with outputBytes := 0 }.wellFormed)
#guard !({ Precompile.Plan.ecrecover with outputBytes := 31 }.wellFormed)
#guard !({ Precompile.Plan.ecrecover with outputBytes := 64 }.wellFormed)

-- Plan layer: missing success / exact-output / nonzero checks fail closed.
#guard !({ Precompile.Plan.ecrecover with requireSuccess := false }.wellFormed)
#guard !({ Precompile.Plan.ecrecover with requireExactOutput := false }.wellFormed)
#guard !({ Precompile.Plan.ecrecover with requireNonzeroResult := false }.wellFormed)

private def mockCtx : Precompile.Emit.Context Nat :=
  { fresh := fun st => (s!"v{st}", st + 1), indent := "  " }

-- Emission golden: the ecrecover plan, byte-exact; the recovered address word is bound and
-- the STATICCALL/success/exact-size gates share the CallResult spelling.
#guard
  match Precompile.Emit.emit mockCtx .ecrecover 0 with
  | .error _ => false
  | .ok (txt, word, st) =>
      txt ==
        "  let v0 := staticcall(gas(), 1, 0, 128, 0, 32)\n" ++
        "  if iszero(v0) { revert(0, 0) }\n" ++
        "  if iszero(eq(returndatasize(), 32)) { revert(0, 0) }\n" ++
        "  let v1 := mload(0)\n" ++
        "  if iszero(v1) { revert(0, 0) }\n" &&
        word == "v1" && st == 2

-- Fail closed at emission: malformed address, geometry, and missing checks.
#guard
  match Precompile.Emit.emit mockCtx { Precompile.Plan.ecrecover with address := 2 } 0 with
  | .error reason => reason.contains "precompile plan shape"
  | .ok _ => false
#guard
  match Precompile.Emit.emit mockCtx { Precompile.Plan.ecrecover with inputBytes := 64 } 0 with
  | .error reason => reason.contains "precompile plan shape"
  | .ok _ => false
#guard
  match Precompile.Emit.emit mockCtx { Precompile.Plan.ecrecover with outputBytes := 64 } 0 with
  | .error reason => reason.contains "precompile plan shape"
  | .ok _ => false
#guard
  match Precompile.Emit.emit mockCtx
      { Precompile.Plan.ecrecover with requireExactOutput := false } 0 with
  | .error reason => reason.contains "precompile plan shape"
  | .ok _ => false
#guard
  match Precompile.Emit.emit mockCtx
      { Precompile.Plan.ecrecover with requireNonzeroResult := false } 0 with
  | .error reason => reason.contains "precompile plan shape"
  | .ok _ => false

private def lit : Ops.Val := .lit 0

private def mockClosedCtx : ClosedCall.Emit.Context Nat :=
  { materialize := fun _ st => .ok ("", "0", st)
    fresh := fun st => (s!"v{st}", st + 1)
    rememberWide := fun st _ _ => st
    lookupWide := fun _ _ => none
    valKey := fun _ => ""
    indent := "  " }

-- ClosedCall permit consumes the typed interpreter: the emitted permit contains exactly the
-- fragment the interpreter produces at the same state, and the Unauthorized gate compares
-- the bound recovered word against the owner.
#guard
  match Precompile.Emit.emit mockCtx .ecrecover 14,
        ClosedCall.Emit.emitCall mockClosedCtx
        (.permit lit lit lit lit lit lit lit lit lit lit lit lit lit lit lit lit lit lit lit
          lit lit lit lit) 0 with
  | .ok (fragment, word, _), .ok (txt, _, _) =>
      word == "v15" && txt.contains fragment &&
        txt.contains ("  if iszero(eq(" ++ word ++ ", v0)) {\n") &&
        !txt.contains "if iszero(staticcall("
  | _, _ => false

-- Existing consumer regression: Token spells the closed precompile contract (fixed address,
-- fixed frame, success + exact-32 + nonzero gates) and no longer inlines the STATICCALL
-- assumption.
#guard
  match Emit.emitYul ProofForge.Evm.Golden.extractedToken with
  | .error _ => false
  | .ok yul =>
      yul.contains " := staticcall(gas(), 1, 0, 128, 0, 32)\n" &&
        yul.contains "if iszero(eq(returndatasize(), 32)) { revert(0, 0) }" &&
        !yul.contains "if iszero(staticcall(gas(), 1,"

-- Consumer component/IR identity is preserved (registry digests).
#guard IR.digestHex ProofForge.Evm.Golden.extractedVault == "a3ea1b5b2a69c0e3"
#guard IR.digestHex ProofForge.Evm.Golden.extractedToken == "59f8696f9b0e06db"

end Tests.EvmPrecompileSpec
