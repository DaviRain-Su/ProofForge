import ProofForge
import ProofForge.Wasm.Near.IR
import ProofForge.Wasm.Near.Emit
import ProofForge.Wasm.Near.Commands
import ProofForge.Wasm.Xrpl.IR
import Examples.NearCtx
import Examples.Clock
import Examples.EvmCtx

open ProofForge
open Lean Elab Command

elab "#pf_near_reject " n:ident : command => do
  let env ← getEnv
  match Extract.extractModuleIR env n.getId none >>= ProofForge.Wasm.Near.IR.fromExtracted with
  | .ok _ => throwError "expected near to reject {n.getId} (foreign target leaf)"
  | .error reason =>
      unless reason.contains "near rejects" do
        throwError "unexpected near rejection reason: {reason}"

#pf_near_reject Examples.Clock

#pf_near_reject Examples.EvmCtx

open Lean Elab Command in
elab "#pf_xrpl_reject_near " n:ident : command => do
  let env ← getEnv
  match Extract.extractModuleIR env n.getId none >>= ProofForge.Wasm.Xrpl.IR.fromExtracted with
  | .ok _ => throwError "expected xrpl to reject {n.getId} (near leaf)"
  | .error reason =>
      unless reason.contains "xrpl rejects near" || reason.contains "xrpl rejects" do
        throwError "unexpected xrpl rejection reason: {reason}"

#pf_xrpl_reject_near Examples.NearCtx

#pf_near_build Examples.NearCtx

open Lean Elab Command in
elab "#pf_near_ctx_emit_check " n:ident : command => do
  let env ← getEnv
  match Extract.extractModuleIR env n.getId none >>= ProofForge.Wasm.Near.IR.fromExtracted with
  | .error reason => throwError reason
  | .ok program =>
    match ProofForge.Wasm.Near.Emit.emit program with
    | .error reason => throwError reason
    | .ok source => do
        let anchors : Array String := #[
          "(import \"env\" \"block_index\"",
          "(import \"env\" \"block_timestamp\"",
          "(import \"env\" \"predecessor_account_id\"",
          "(import \"env\" \"attached_deposit\"",
          "(import \"env\" \"account_balance\"",
          "(func (export \"height\")",
          "(func (export \"seconds\")",
          "(func (export \"selfBal\")",
          "(call $pf_block_index)",
          "i64.div_u (call $pf_block_timestamp)"
        ]
        for anchor in anchors do
          unless source.contains anchor do
            throwError s!"near ctx emit is missing anchor: {anchor}\n{source}"
        unless !source.contains "host_lib" do
          throwError "near ctx emit mentions XRPL host_lib"
        logInfo m!"proofforge-near-ctx-test: digest = {ProofForge.Wasm.Near.IR.digestHex program}"
        logInfo m!"proofforge-near-ctx-test: {source.length} bytes of WAT passed anchor check"

#pf_near_ctx_emit_check Examples.NearCtx
