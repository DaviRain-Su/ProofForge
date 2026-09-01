import Lean
import ProofForge.Extract
import ProofForge.Wasm.Near.IR
import ProofForge.Wasm.Near.Emit
import ProofForge.Wasm.Near.Registry

open Lean Elab Command
open ProofForge
open ProofForge.Wasm.Near

namespace ProofForge.Wasm.Near.Commands

elab "#pf_near_build " n:ident : command => do
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
        logInfo m!"proofforge-near: program {program.name} slots = {IR.slotNames program}"
        logInfo m!"proofforge-near: entries = {program.entries.map (·.ixName)}"
        logInfo m!"proofforge-near: digest = {digest}"
        logInfo m!"proofforge-near: emitted {source.length} bytes of WAT"

elab "#pf_near_dump " n:ident : command => do
  let ns := n.getId
  let env ← getEnv
  match Extract.extractModuleIR env ns none >>= IR.fromExtracted with
  | .error reason => throwError reason
  | .ok program =>
    let methods := #[program.initializer] ++ program.entries
    logInfo m!"proofforge-near-dump: {program.name} methods = {methods.map (·.ixName)}"
    for m in methods do
      logInfo m!"proofforge-near-dump: {m.ixName} pc={m.paramCount} tuple={repr m.tupleArity}"
    logInfo m!"proofforge-near-dump: digest = {IR.digestHex program}"

end ProofForge.Wasm.Near.Commands
