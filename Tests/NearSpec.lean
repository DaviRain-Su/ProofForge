import ProofForge
import ProofForge.Wasm.Near.IR
import ProofForge.Wasm.Near.Emit
import ProofForge.Wasm.Near.Commands
import Examples.Counter
import Examples.Clock
import Examples.EvmCtx

/-!
# NEAR target tests (WASM family)

v0: registration rejects foreign leaves; digest is pinned; emitted WAT carries
`env` imports and exported entries. Not JSON ABI; not XRPL `host_lib`.
-/

open ProofForge

#guard !ProofForge.Wasm.Near.Ops.Op.wellFormed (.ext .reserved)
#guard !(ProofForge.Wasm.Near.Ops.OpExt.wellFormed
  (.reserved : ProofForge.Wasm.Near.Ops.OpExt ProofForge.Wasm.Near.Ops.Val))
#guard ProofForge.Wasm.Near.Ops.ValKind.arity .reserved == 0

#guard ProofForge.Wasm.Near.Registry.digestOf "Counter" == some "121a0c8f7e697642"
#guard ProofForge.Wasm.Near.Registry.names ==
  #["Counter", "NearCtx", "NearBytes", "NearMemory", "NearOutput", "NearStorage", "NearVector",
    "NearLookup", "NearQueue", "NearIterable", "NearPromise", "NearPromiseResult"]
#guard ProofForge.Wasm.Near.Registry.digestOf "NearCtx" == some "8233f27ab39f6133"
#guard ProofForge.Wasm.Near.Registry.digestOf "NearMemory" == some "830255873ad66d7c"
#guard ProofForge.Wasm.Near.Registry.digestOf "NearOutput" == some "d455a43be10516e3"
#guard ProofForge.Wasm.Near.Registry.digestOf "NearStorage" == some "81dd911358e341be"
#guard ProofForge.Wasm.Near.Registry.digestOf "NearVector" == some "25b961c16db0bb93"
#guard ProofForge.Wasm.Near.Registry.digestOf "NearLookup" == some "153fe4dc7e95c3f0"
#guard ProofForge.Wasm.Near.Registry.digestOf "NearQueue" == some "f04d9a0d673b7fed"
#guard ProofForge.Wasm.Near.Registry.digestOf "NearIterable" == some "8c0ece42e2b091ff"
#guard ProofForge.Wasm.Near.Registry.digestOf "NearPromise" == some "7ba98f4624b9cd34"
#guard ProofForge.Wasm.Near.Registry.digestOf "NearPromiseResult" == some "ff7ea8988ba01999"

#guard ProofForge.Wasm.Near.Ops.OpExt.wellFormed
  (.logUtf8 "NEAR ✓" : ProofForge.Wasm.Near.Ops.OpExt ProofForge.Wasm.Near.Ops.Val)
#guard !ProofForge.Wasm.Near.Ops.OpExt.wellFormed
  (.logUtf8 (String.ofList (List.replicate 1025 'x')) :
    ProofForge.Wasm.Near.Ops.OpExt ProofForge.Wasm.Near.Ops.Val)

open Lean Elab Command in
elab "#pf_near_reject " n:ident : command => do
  let env ← getEnv
  match Extract.extractModuleIR env n.getId none >>= ProofForge.Wasm.Near.IR.fromExtracted with
  | .ok _ => throwError "expected near to reject {n.getId} (foreign target leaf)"
  | .error reason =>
      unless reason.contains "near rejects" do
        throwError "unexpected near rejection reason: {reason}"

#pf_near_reject Examples.Clock

#pf_near_reject Examples.EvmCtx

#pf_near_build Examples.Counter

open Lean Elab Command in
elab "#pf_near_emit_check " n:ident : command => do
  let env ← getEnv
  match Extract.extractModuleIR env n.getId none >>= ProofForge.Wasm.Near.IR.fromExtracted with
  | .error reason => throwError reason
  | .ok program =>
    match ProofForge.Wasm.Near.Emit.emit program with
    | .error reason => throwError reason
    | .ok source => do
        let digest := ProofForge.Wasm.Near.IR.digestHex program
        match ProofForge.Wasm.Near.Registry.digestOf program.name with
        | some want =>
            if digest != want then
              throwError s!"ir/mismatch: extracted near {program.name} digest {digest} != fixture {want}"
        | none => pure ()
        let anchors : Array String := #[
          "(import \"env\" \"input\"",
          "(import \"env\" \"register_len\"",
          "(import \"env\" \"read_register\"",
          "(import \"env\" \"storage_read\"",
          "(import \"env\" \"storage_write\"",
          "(import \"env\" \"value_return\"",
          "(import \"env\" \"panic_utf8\"",
          "(func (export \"initialize\")",
          "(func (export \"increment\")",
          "(func (export \"get\")",
          "(func (export \"nonzero\")",
          "i64.add",
          "i64.sub",
          "i64.mul",
          "i64.div_u",
          "i64.rem_u",
          "call $pf_storage_read",
          "call $pf_storage_write",
          "call $pf_value_return"
        ]
        for anchor in anchors do
          unless source.contains anchor do
            throwError s!"near emit is missing anchor: {anchor}\n{source}"
        unless !source.contains "host_lib" do
          throwError "near emit mentions XRPL host_lib"
        unless !source.contains "\"log_utf8\"" do
          throwError "Counter unexpectedly imports NEAR log_utf8"
        unless !source.contains "xrpl_wasm_std" do
          throwError "near emit still mentions xrpl_wasm_std"
        logInfo m!"proofforge-near-test: digest = {digest}"
        logInfo m!"proofforge-near-test: {source.length} bytes of WAT passed anchor check"

#pf_near_emit_check Examples.Counter
