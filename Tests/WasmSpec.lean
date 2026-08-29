import ProofForge
import ProofForge.Wasm.IR
import ProofForge.Wasm.Emit
import ProofForge.Wasm.Commands
import Examples.Counter
import Examples.Clock
import Examples.EvmCtx

/-!
# WASM (XRPL Bedrock) target tests

v0 vertical slice: registration rejects foreign target leaves, the canonical digest is
pinned against the registry, and the emitted Rust source carries the Bedrock-dialect
anchors (`xrpl_wasm_std` storage helpers, `#[unsafe(no_mangle)]` exports, checked
arithmetic with pinned error codes).
-/

open ProofForge

#guard !ProofForge.Wasm.Ops.Op.wellFormed (.ext .reserved)
#guard !(ProofForge.Wasm.Ops.OpExt.wellFormed
  (.reserved : ProofForge.Wasm.Ops.OpExt ProofForge.Wasm.Ops.Val))
#guard ProofForge.Wasm.Ops.ValKind.arity .reserved == 0

#guard ProofForge.Wasm.Registry.digestOf "Counter" == some "335b688107a04afc"
#guard ProofForge.Wasm.Registry.names == #["Counter"]

open Lean Elab Command in
elab "#pf_wasm_reject " n:ident : command => do
  let env ← getEnv
  match Extract.extractModuleIR env n.getId none >>= ProofForge.Wasm.IR.fromExtracted with
  | .ok _ => throwError "expected wasm to reject {n.getId} (foreign target leaf)"
  | .error reason =>
      unless reason.contains "wasm rejects" do
        throwError "unexpected wasm rejection reason: {reason}"

/-! Runtime leaves are not cross-target: the wasm profile fails closed on svm and evm
values, same discipline as the EVM slice. -/

#pf_wasm_reject Examples.Clock

#pf_wasm_reject Examples.EvmCtx

/-! Digest pin: extraction → registration → lowering must reproduce the registry digest. -/

#pf_wasm_build Examples.Counter

open Lean Elab Command in
elab "#pf_wasm_emit_check " n:ident : command => do
  let env ← getEnv
  match Extract.extractModuleIR env n.getId none >>= ProofForge.Wasm.IR.fromExtracted with
  | .error reason => throwError reason
  | .ok program =>
    match ProofForge.Wasm.Emit.emit program with
    | .error reason => throwError reason
    | .ok source => do
        let anchors : Array String := #[
          "pub extern \"C\" fn initialize(pf_p0: u64) -> i32",
          "pub extern \"C\" fn increment(pf_p0: u64) -> i32",
          "pub extern \"C\" fn get() -> u64",
          "pub extern \"C\" fn nonzero() -> u64",
          "/// @xrpl-function increment",
          "#[unsafe(no_mangle)]",
          "use xrpl_wasm_std::core::data::codec::{get_data, set_data};",
          "const value_KEY: &str = \"value\";",
          "read_u64(value_KEY)",
          "write_u64(value_KEY, pf_r0)?;",
          "checked_add(pf_p0).ok_or(1i32)?",
          "checked_sub(pf_p0).ok_or(1i32)?",
          "checked_mul(pf_p0).ok_or(1i32)?",
          "checked_div(pf_p0).ok_or(2i32)?",
          "checked_rem(pf_p0).ok_or(2i32)?",
          "Ok(0)",
          "Err(code) => if code < 0 { code } else { -code },",
          "// digest=335b688107a04afc"
        ]
        for anchor in anchors do
          unless source.contains anchor do
            throwError s!"wasm emit is missing anchor: {anchor}"
        logInfo m!"proofforge-wasm-test: {source.length} bytes of Rust passed anchor check"

#pf_wasm_emit_check Examples.Counter