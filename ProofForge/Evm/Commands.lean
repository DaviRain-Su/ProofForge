import Lean
import ProofForge.Extract
import ProofForge.Evm.IR
import ProofForge.Evm.Emit
import ProofForge.Evm.Golden

open Lean Elab Command
open ProofForge
open ProofForge.Evm

namespace ProofForge.Evm.Commands

elab "#pf_evm_build " n:ident : command => do
  let ns := n.getId
  let env ← getEnv
  match Extract.extractModule env ns none with
  | .error reason => throwError reason
  | .ok src => do
    match IR.fromProgram src with
    | .error reason => throwError reason
    | .ok program => do
      match Emit.emitYul program with
      | .error reason => throwError reason
      | .ok yul =>
          unless yul.contains "object \"" do
            throwError "assemble/tool: missing yul object"
          let digest := IR.digestHex program
          match Golden.digestOf program.name with
          | some want =>
              if digest != want then
                throwError s!"ir/mismatch: extracted evm {program.name} digest != fixture"
          | none => pure ()
          logInfo m!"proofforge-evm: program {program.name} slots = {program.slots.map (·.name)}"
          logInfo m!"proofforge-evm: entries = {program.entries.map (fun m => m.ixName)}"
          logInfo m!"proofforge-evm: digest = {digest}"
          logInfo m!"proofforge-evm: emitted {yul.length} bytes of Yul"

elab "#pf_evm_dump " n:ident : command => do
  let ns := n.getId
  let env ← getEnv
  match Extract.extractModule env ns none with
  | .error reason => throwError reason
  | .ok src =>
      logInfo m!"proofforge-evm-dump: {src.name} methods = {src.methods.map (·.ixName)}"
      for m in src.methods do
        logInfo m!"proofforge-evm-dump: {m.ixName} pc={m.paramCount} ops={repr m.ops}"
      match IR.fromProgram src with
      | .error reason => throwError reason
      | .ok program =>
          logInfo m!"proofforge-evm-dump: digest = {IR.digestHex program}"

end ProofForge.Evm.Commands
