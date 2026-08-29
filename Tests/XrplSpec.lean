import ProofForge
import ProofForge.Wasm.Xrpl.IR
import ProofForge.Wasm.Xrpl.Emit
import ProofForge.Wasm.Xrpl.Commands
import Examples.Counter
import Examples.Clock
import Examples.EvmCtx

/-!
# XRPL Bedrock target tests (WASM family)

v0 vertical slice: registration rejects foreign target leaves, the canonical digest is
pinned against the registry, and the emitted Rust source carries the Bedrock-dialect
anchors (`xrpl_wasm_std` storage helpers, `#[unsafe(no_mangle)]` exports, checked
arithmetic with pinned error codes).
-/

open ProofForge

#guard !ProofForge.Wasm.Xrpl.Ops.Op.wellFormed (.ext .reserved)
#guard !(ProofForge.Wasm.Xrpl.Ops.OpExt.wellFormed
  (.reserved : ProofForge.Wasm.Xrpl.Ops.OpExt ProofForge.Wasm.Xrpl.Ops.Val))
#guard ProofForge.Wasm.Xrpl.Ops.ValKind.arity .reserved == 0

#guard ProofForge.Wasm.Xrpl.Registry.digestOf "Counter" == some "e029f72296e320be"
#guard ProofForge.Wasm.Xrpl.Registry.names == #["Counter"]

open Lean Elab Command in
elab "#pf_xrpl_reject " n:ident : command => do
  let env ← getEnv
  match Extract.extractModuleIR env n.getId none >>= ProofForge.Wasm.Xrpl.IR.fromExtracted with
  | .ok _ => throwError "expected xrpl to reject {n.getId} (foreign target leaf)"
  | .error reason =>
      unless reason.contains "xrpl rejects" do
        throwError "unexpected xrpl rejection reason: {reason}"

/-! Runtime leaves are not cross-target: the XRPL profile fails closed on svm and evm
values through the WASM family rejection, same discipline as the EVM slice. -/

#pf_xrpl_reject Examples.Clock

#pf_xrpl_reject Examples.EvmCtx

/-! Digest pin: extraction → registration → lowering must reproduce the registry digest. -/

#pf_xrpl_build Examples.Counter

open Lean Elab Command in
elab "#pf_xrpl_emit_check " n:ident : command => do
  let env ← getEnv
  match Extract.extractModuleIR env n.getId none >>= ProofForge.Wasm.Xrpl.IR.fromExtracted with
  | .error reason => throwError reason
  | .ok program =>
    match ProofForge.Wasm.Xrpl.Emit.emit program with
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
          "// digest=e029f72296e320be"
        ]
        for anchor in anchors do
          unless source.contains anchor do
            throwError s!"wasm emit is missing anchor: {anchor}"
        logInfo m!"proofforge-xrpl-test: {source.length} bytes of Rust passed anchor check"

#pf_xrpl_emit_check Examples.Counter