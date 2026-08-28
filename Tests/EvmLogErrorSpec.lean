import ProofForge
import ProofForge.Evm.LogError
import ProofForge.Evm.LogError.Emit
import Examples.Vault
import Examples.Token

namespace Tests.EvmLogErrorSpec

open ProofForge.Evm

/-! Focused gates for the EVM-RT-2b typed log/custom-error plan: plan-layer shape gates,
byte-exact emission goldens for LOG0 through LOG4 and for the custom-error shapes, fail-closed
emission errors for malformed plans, and NativeFx / ClosedCall / Component consumer regression
(including the existing Vault and Token structural gates). Plan-level LOG0/2/4 coverage does
not claim any new source-level event API. -/

-- Plan layer: geometry derivations are explicit.
#guard LogError.LogPlan.wordOffset 0 == 0
#guard LogError.LogPlan.wordOffset 1 == 32
#guard LogError.LogPlan.wordOffset 3 == 96
#guard LogError.ErrorPlan.argOffset 0 == 4
#guard LogError.ErrorPlan.argOffset 1 == 36
#guard LogError.ErrorPlan.argOffset 3 == 100
#guard ({} : LogError.LogPlan).topicCount == 0
#guard ({ topics := #["a", "b", "c", "d"] } : LogError.LogPlan).topicCount == 4
#guard ({ data := #["x", "y"] } : LogError.LogPlan).dataBytes == 64
#guard ({ selector := "0123abcd" } : LogError.ErrorPlan).revertBytes == 4
#guard ({ selector := "0123abcd", args := #["a", "b"] } : LogError.ErrorPlan).revertBytes == 68

-- Plan layer: LOG0..LOG4 shapes within bounds are well-formed.
#guard [0, 1, 2, 3, 4].all fun n =>
  ({ data := #["d"], topics := Array.replicate n "t" } : LogError.LogPlan).wellFormed
#guard [0, 1, 2, 3, 4].all fun n =>
  ({ data := Array.replicate n "d", topics := #["t"] } : LogError.LogPlan).wellFormed
#guard ({ selector := "0123abcd", args := Array.replicate 4 "a" } : LogError.ErrorPlan).wellFormed

-- Plan layer: unsupported shapes fail closed (more than 4 topics, oversized data, malformed
-- selector, oversized error argument list).
#guard !({ data := #["d"], topics := Array.replicate 5 "t" } : LogError.LogPlan).wellFormed
#guard !({ data := Array.replicate 5 "d" } : LogError.LogPlan).wellFormed
#guard !({ selector := "0123" } : LogError.ErrorPlan).wellFormed
#guard !({ selector := "0123abc" } : LogError.ErrorPlan).wellFormed
#guard !({ selector := "0123abcde" } : LogError.ErrorPlan).wellFormed
#guard !({ selector := "0123ABCD" } : LogError.ErrorPlan).wellFormed
#guard !({ selector := "0123abcg" } : LogError.ErrorPlan).wellFormed
#guard !({ selector := "", args := #["a"] } : LogError.ErrorPlan).wellFormed
#guard !({ selector := "0123abcd", args := Array.replicate 5 "a" } : LogError.ErrorPlan).wellFormed

private def mockCtx : LogError.Emit.Context := { indent := "  " }

-- Emission golden: LOG0 with one data word, byte-exact.
#guard
  match LogError.Emit.emitLog mockCtx { data := #["d0"] } with
  | .error _ => false
  | .ok txt => txt == "  mstore(0, d0)\n  log0(0, 32)\n"

-- Emission golden: LOG0 with empty data, byte-exact.
#guard
  match LogError.Emit.emitLog mockCtx {} with
  | .error _ => false
  | .ok txt => txt == "  log0(0, 0)\n"

-- Emission golden: LOG1 (the NativeFx uint64 event shape), byte-exact.
#guard
  match LogError.Emit.emitLog mockCtx { data := #["amt"], topics := #["0xsig"] } with
  | .error _ => false
  | .ok txt => txt == "  mstore(0, amt)\n  log1(0, 32, 0xsig)\n"

-- Emission golden: LOG2 with a two-word data payload, byte-exact.
#guard
  match LogError.Emit.emitLog mockCtx { data := #["d0", "d1"], topics := #["t0", "t1"] } with
  | .error _ => false
  | .ok txt =>
      txt == "  mstore(0, d0)\n  mstore(32, d1)\n  log2(0, 64, t0, t1)\n"

-- Emission golden: LOG3 (the Transfer/Approval shape), byte-exact.
#guard
  match LogError.Emit.emitLog mockCtx
      { data := #["amt"], topics := #["0xsig", "from", "to"] } with
  | .error _ => false
  | .ok txt => txt == "  mstore(0, amt)\n  log3(0, 32, 0xsig, from, to)\n"

-- Emission golden: LOG4, byte-exact.
#guard
  match LogError.Emit.emitLog mockCtx
      { data := #["d0"], topics := #["t0", "t1", "t2", "t3"] } with
  | .error _ => false
  | .ok txt => txt == "  mstore(0, d0)\n  log4(0, 32, t0, t1, t2, t3)\n"

-- Emission golden: selector-only custom error (ZeroAddress/Paused/CapExceeded shape),
-- byte-exact.
#guard
  match LogError.Emit.emitRevert mockCtx { selector := "0123abcd" } with
  | .error _ => false
  | .ok txt => txt == "  mstore(0, shl(224, 0x0123abcd))\n  revert(0, 4)\n"

-- Emission golden: one-argument custom error (Unauthorized(address) shape), byte-exact.
#guard
  match LogError.Emit.emitRevert mockCtx { selector := "0123abcd", args := #["who"] } with
  | .error _ => false
  | .ok txt =>
      txt == "  mstore(0, shl(224, 0x0123abcd))\n  mstore(4, who)\n  revert(0, 36)\n"

-- Emission golden: two-argument custom error (Insufficient(uint256,uint256) shape),
-- byte-exact.
#guard
  match LogError.Emit.emitRevert mockCtx { selector := "0123abcd", args := #["have", "want"] } with
  | .error _ => false
  | .ok txt =>
      txt == "  mstore(0, shl(224, 0x0123abcd))\n  mstore(4, have)\n" ++
        "  mstore(36, want)\n  revert(0, 68)\n"

-- Fail closed at emission: more than 4 topics and oversized data.
#guard
  match LogError.Emit.emitLog mockCtx { data := #["d"], topics := Array.replicate 5 "t" } with
  | .error reason => reason.contains "log plan shape"
  | .ok _ => false
#guard
  match LogError.Emit.emitLog mockCtx { data := Array.replicate 5 "d" } with
  | .error reason => reason.contains "log plan shape"
  | .ok _ => false

-- Fail closed at emission: malformed selector and oversized error argument list.
#guard
  match LogError.Emit.emitRevert mockCtx { selector := "0123ABCD" } with
  | .error reason => reason.contains "error plan shape"
  | .ok _ => false
#guard
  match LogError.Emit.emitRevert mockCtx { selector := "0123abcd", args := Array.replicate 5 "a" } with
  | .error reason => reason.contains "error plan shape"
  | .ok _ => false

private def lit : Ops.Val := .lit 0

private def mockNativeCtx : NativeFx.Emit.Context Nat :=
  { materialize := fun _ st => .ok ("", "0", st)
    fresh := fun st => (s!"v{st}", st + 1)
    indent := "  " }

-- Consumer regression: the NativeFx LOG1 uint64 event consumes the shared interpreter,
-- byte-exact.
#guard
  match NativeFx.Emit.emitCall mockNativeCtx (.log "Tipped" lit) 0 with
  | .error _ => false
  | .ok (txt, ret, st) =>
      txt == s!"  mstore(0, 0)\n  log1(0, 32, 0x{
        Keccak.keccak256HexOfString "Tipped(uint64)"})\n" &&
        ret == "0" && st == 0

-- Consumer regression: the NativeFx Transfer LOG3 consumes the shared interpreter; the emitted
-- text ends with exactly the fragment the interpreter produces for the same plan.
#guard
  match LogError.Emit.emitLog mockCtx
        { data := #["v2"]
          topics := #["0x" ++ Keccak.keccak256HexOfString "Transfer(address,address,uint256)",
            "v0", "v1"] },
        NativeFx.Emit.emitCall mockNativeCtx
        (.logTransfer256 lit lit lit lit lit lit lit lit lit lit) 0 with
  | .ok fragment, .ok (txt, ret, st) =>
      txt.endsWith fragment && ret == "0" && st == 3 &&
        txt.contains "  let v2 := or(or(0, shl(64, 0)), or(shl(128, 0), shl(192, 0)))\n"
  | _, _ => false

-- Consumer regression: the NativeFx Approval LOG3 consumes the shared interpreter.
#guard
  match LogError.Emit.emitLog mockCtx
        { data := #["v2"]
          topics := #["0x" ++ Keccak.keccak256HexOfString "Approval(address,address,uint256)",
            "v0", "v1"] },
        NativeFx.Emit.emitCall mockNativeCtx
        (.logApproval256 lit lit lit lit lit lit lit lit lit lit) 0 with
  | .ok fragment, .ok (txt, ret, st) => txt.endsWith fragment && ret == "0" && st == 3
  | _, _ => false

-- Consumer regression: Insufficient(uint256,uint256) consumes the shared interpreter,
-- byte-exact.
#guard
  match NativeFx.Emit.emitCall mockNativeCtx
      (.revertInsufficient lit lit lit lit lit lit lit lit) 0 with
  | .error _ => false
  | .ok (txt, ret, st) =>
      txt == s!"  mstore(0, shl(224, 0x{Keccak.selector "Insufficient" #["uint256", "uint256"]}))\n" ++
          "  mstore(4, or(or(0, shl(64, 0)), or(shl(128, 0), shl(192, 0))))\n" ++
          "  mstore(36, or(or(0, shl(64, 0)), or(shl(128, 0), shl(192, 0))))\n" ++
          "  revert(0, 68)\n" &&
        ret == "0" && st == 0

-- Consumer regression: Unauthorized(address) consumes the shared interpreter, byte-exact.
#guard
  match NativeFx.Emit.emitCall mockNativeCtx (.revertUnauthorized lit lit lit) 0 with
  | .error _ => false
  | .ok (txt, ret, st) =>
      txt == "  mstore(0, 0)\n  pf_store_addr20(0, 0, 0, 0)\n  let pf_who := mload(0)\n" ++
          s!"  mstore(0, shl(224, 0x{Keccak.selector "Unauthorized" #["address"]}))\n" ++
          "  mstore(4, pf_who)\n  revert(0, 36)\n" &&
        ret == "0" && st == 0

-- Consumer regression: the selector-only NativeFx errors consume the shared interpreter,
-- byte-exact.
#guard
  match NativeFx.Emit.emitCall mockNativeCtx .revertZeroAddress 0 with
  | .error _ => false
  | .ok (txt, _, _) =>
      txt == s!"  mstore(0, shl(224, 0x{Keccak.selector "ZeroAddress" #[]}))\n  revert(0, 4)\n"
#guard
  match NativeFx.Emit.emitCall mockNativeCtx .revertPaused 0 with
  | .error _ => false
  | .ok (txt, _, _) =>
      txt == s!"  mstore(0, shl(224, 0x{Keccak.selector "Paused" #[]}))\n  revert(0, 4)\n"
#guard
  match NativeFx.Emit.emitCall mockNativeCtx .revertCapExceeded 0 with
  | .error _ => false
  | .ok (txt, _, _) =>
      txt == s!"  mstore(0, shl(224, 0x{Keccak.selector "CapExceeded" #[]}))\n  revert(0, 4)\n"

private def mockClosedCtx : ClosedCall.Emit.Context Nat :=
  { materialize := fun _ st => .ok ("", "0", st)
    fresh := fun st => (s!"v{st}", st + 1)
    rememberWide := fun st _ _ => st
    lookupWide := fun _ _ => none
    valKey := fun _ => ""
    indent := "  " }

-- Consumer regression: ClosedCall permit spells its Approval LOG3 and its nested Expired and
-- Unauthorized custom errors through the same interpreter; the emitted text contains exactly
-- the fragments the interpreter produces for the same plans (nested gates deepen the indent).
#guard
  match LogError.Emit.emitLog mockCtx
        { data := #["v2"]
          topics := #["0x" ++ Keccak.keccak256HexOfString "Approval(address,address,uint256)",
            "v0", "v1"] },
        LogError.Emit.emitRevert { indent := "    " }
        { selector := Keccak.selector "Expired" #[] },
        LogError.Emit.emitRevert { indent := "    " }
        { selector := Keccak.selector "Unauthorized" #["address"], args := #["v15"] },
        ClosedCall.Emit.emitCall mockClosedCtx
        (.permit lit lit lit lit lit lit lit lit lit lit lit lit lit lit lit lit lit lit lit
          lit lit lit lit) 0 with
  | .ok approval, .ok expired, .ok unauthorized, .ok (txt, _, _) =>
      txt.endsWith approval && txt.contains expired &&
        txt.contains unauthorized &&
        txt.contains "  if lt(v3, timestamp()) {\n" &&
        txt.contains "  if iszero(eq(v15, v0)) {\n"
  | _, _, _, _ => false

-- Component bridge still routes native effects into the shared interpreter.
#guard
  match Component.Emit.emitCall
      { materialize := fun _ st => .ok ("", "0", st)
        fresh := fun st => (s!"v{st}", st + 1)
        rememberWide := fun st _ _ => st
        lookupWide := fun _ _ => none
        valKey := fun _ => ""
        indent := "  " }
      (.nativeFx (.revertZeroAddress) : Component.Call Ops.Val) 0 with
  | .error _ => false
  | .ok (txt, _, _) => txt.contains "shl(224, 0x" && txt.contains "revert(0, 4)"

-- Existing consumer regression: TipJar and Token keep the shared log/error spellings.
#guard
  match Emit.emitYul ProofForge.Evm.Golden.extractedTipJar with
  | .error _ => false
  | .ok yul =>
      yul.contains "log1(0, 32, 0x" &&
        yul.contains "mstore(0, "

#guard
  match Emit.emitYul ProofForge.Evm.Golden.extractedToken with
  | .error _ => false
  | .ok yul =>
      yul.contains "log1(0, 32, 0x" &&
        yul.contains "log3(0, 32, 0x" &&
        yul.contains "mstore(36, " &&
        yul.contains "revert(0, 4)" &&
        yul.contains "revert(0, 36)" &&
        yul.contains "revert(0, 68)"

-- Consumer component/IR identity is preserved (registry digests).
#guard IR.digestHex ProofForge.Evm.Golden.extractedVault == "a3ea1b5b2a69c0e3"
#guard IR.digestHex ProofForge.Evm.Golden.extractedToken == "4da7ac248a0fb556"

end Tests.EvmLogErrorSpec
