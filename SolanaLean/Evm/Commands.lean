import Lean
import SolanaLean.Extract
import SolanaLean.Evm.IR
import SolanaLean.Evm.Emit
import SolanaLean.Evm.Golden

open Lean Elab Command
open SolanaLean
open SolanaLean.Evm

namespace SolanaLean.Evm.Commands

elab "#evm_build " n:ident : command => do
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
          logInfo m!"solana-lean-evm: program {program.name} slots = {program.slots.map (·.name)}"
          logInfo m!"solana-lean-evm: entries = {program.entries.map (fun m => m.ixName)}"
          logInfo m!"solana-lean-evm: digest = {digest}"
          logInfo m!"solana-lean-evm: emitted {yul.length} bytes of Yul"

end SolanaLean.Evm.Commands
