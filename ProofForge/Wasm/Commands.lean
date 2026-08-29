import Lean
import ProofForge.Extract
import ProofForge.Wasm.IR
import ProofForge.Wasm.Emit
import ProofForge.Wasm.Registry

open Lean Elab Command
open ProofForge
open ProofForge.Wasm

namespace ProofForge.Wasm.Commands

elab "#pf_wasm_build " n:ident : command => do
  let ns := n.getId
  let env ← getEnv
  match Extract.extractModuleIR env ns none >>= IR.fromExtracted with
  | .error reason => throwError reason
  | .ok program => do
    match Emit.emit program with
    | .error reason => throwError reason
    | .ok source =>
        unless source.contains "pub extern \"C\" fn" do
          throwError "assemble/tool: missing exported wasm entry"
        let digest := IR.digestHex program
        match Registry.digestOf program.name with
        | some want =>
            if digest != want then
              throwError s!"ir/mismatch: extracted wasm {program.name} digest {digest} != fixture {want}"
        | none => pure ()
        logInfo m!"proofforge-wasm: program {program.name} slots = {IR.slotNames program}"
        logInfo m!"proofforge-wasm: entries = {program.entries.map (·.ixName)}"
        logInfo m!"proofforge-wasm: digest = {digest}"
        logInfo m!"proofforge-wasm: emitted {source.length} bytes of Rust"

elab "#pf_wasm_dump " n:ident : command => do
  let ns := n.getId
  let env ← getEnv
  match Extract.extractModuleIR env ns none >>= IR.fromExtracted with
  | .error reason => throwError reason
  | .ok program =>
    let methods := #[program.initializer] ++ program.entries
    logInfo m!"proofforge-wasm-dump: {program.name} methods = {methods.map (·.ixName)}"
    for m in methods do
      logInfo m!"proofforge-wasm-dump: {m.ixName} pc={m.paramCount} tuple={repr m.tupleArity}"
    logInfo m!"proofforge-wasm-dump: digest = {IR.digestHex program}"

end ProofForge.Wasm.Commands