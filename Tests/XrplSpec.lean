import ProofForge
import ProofForge.Wasm.Xrpl.IR
import ProofForge.Wasm.Xrpl.Emit
import ProofForge.Wasm.Xrpl.Commands
import Examples.Counter
import Examples.Clock
import Examples.EvmCtx

/-!
# XRPL Bedrock target tests (WASM family)

v0: registration rejects foreign leaves; digest is pinned; emitted WAT carries
`host_lib` imports and exported entries.
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

#pf_xrpl_reject Examples.Clock

#pf_xrpl_reject Examples.EvmCtx

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
          "(import \"host_lib\" \"get_current_ledger_obj_field\"",
          "(import \"host_lib\" \"get_data_object_field\"",
          "(import \"host_lib\" \"set_data_object_field\"",
          "(import \"host_lib\" \"function_param\"",
          "(func (export \"initialize\") (result i32)",
          "(func (export \"increment\") (result i32)",
          "(func (export \"get\")",
          "(func (export \"nonzero\")",
          "(i32.const 524290)",
          "(data (i32.const 64) \"value\")",
          "(return (i32.const 1))",
          "(return (i32.const 2))",
          "i64.add",
          "i64.sub",
          "i64.mul",
          "i64.div_u",
          "i64.rem_u",
          ";; digest=e029f72296e320be"
        ]
        for anchor in anchors do
          unless source.contains anchor do
            throwError s!"wasm emit is missing anchor: {anchor}\n{source}"
        unless !source.contains "xrpl_wasm_std" do
          throwError "wasm emit still mentions xrpl_wasm_std"
        unless !source.contains "get_current_contract_call" do
          throwError "wasm emit still mentions get_current_contract_call"
        unless !source.contains "\"get_data\"" do
          throwError "wasm emit still mentions get_data"
        unless !source.contains "(param $pf_p0 i64)" do
          throwError "wasm emit still uses wasm i64 params; XRPL fetches UINT64 via function_param"
        unless !source.contains "update_data" do
          throwError "wasm emit still uses update_data; this Bedrock image does not persist it"
        logInfo m!"proofforge-xrpl-test: {source.length} bytes of WAT passed anchor check"

#pf_xrpl_emit_check Examples.Counter
