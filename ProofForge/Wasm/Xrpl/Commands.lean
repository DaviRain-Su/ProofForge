import Lean
import ProofForge.Extract
import ProofForge.Wasm.Xrpl.IR
import ProofForge.Wasm.Xrpl.Emit
import ProofForge.Wasm.Xrpl.Registry

open Lean Elab Command
open ProofForge
open ProofForge.Wasm.Xrpl

namespace ProofForge.Wasm.Xrpl.Commands

elab "#pf_xrpl_build " n:ident : command => do
  let ns := n.getId
  let env ← getEnv
  match Extract.extractModuleIR env ns none >>= IR.fromExtracted with
  | .error reason => throwError reason
  | .ok program => do
    match Emit.emit program with
    | .error reason => throwError reason
    | .ok source =>
        unless source.contains "(func (export" do
          throwError "assemble/tool: missing exported wasm entry"
        let digest := IR.digestHex program
        match Registry.digestOf program.name with
        | some want =>
            if digest != want then
              throwError s!"ir/mismatch: extracted wasm {program.name} digest {digest} != fixture {want}"
        | none => pure ()
        logInfo m!"proofforge-xrpl: program {program.name} slots = {IR.slotNames program}"
        logInfo m!"proofforge-xrpl: entries = {program.entries.map (·.ixName)}"
        logInfo m!"proofforge-xrpl: digest = {digest}"
        logInfo m!"proofforge-xrpl: emitted {source.length} bytes of WAT"

elab "#pf_xrpl_dump " n:ident : command => do
  let ns := n.getId
  let env ← getEnv
  match Extract.extractModuleIR env ns none >>= IR.fromExtracted with
  | .error reason => throwError reason
  | .ok program =>
    let methods := #[program.initializer] ++ program.entries
    logInfo m!"proofforge-xrpl-dump: {program.name} methods = {methods.map (·.ixName)}"
    for m in methods do
      logInfo m!"proofforge-xrpl-dump: {m.ixName} pc={m.paramCount} tuple={repr m.tupleArity}"
    logInfo m!"proofforge-xrpl-dump: digest = {IR.digestHex program}"

end ProofForge.Wasm.Xrpl.Commands
