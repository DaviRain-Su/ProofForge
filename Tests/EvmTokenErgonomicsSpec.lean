import ProofForge
import ProofForge.Evm.IR
import ProofForge.Evm.Emit
import ProofForge.Evm.Commands
import Examples.EvmTokenErgonomics

open Lean Elab Command

elab "#pf_guard_evm_token_ergonomics" : command => do
  let env ← getEnv
  let source ←
    match ProofForge.Extract.extractModuleIR env `Examples.EvmTokenErgonomics with
    | .ok source => pure source
    | .error reason => throwError reason
  let program ←
    match ProofForge.Evm.IR.fromExtracted source with
    | .ok program => pure program
    | .error reason => throwError reason
  let yul ←
    match ProofForge.Evm.Emit.emitYul program with
    | .ok yul => pure yul
    | .error reason => throwError reason
  unless program.entries.any (·.ixName == "approve") do
    throwError "EVM Token ergonomics missing approve entry"
  unless program.entries.any (·.ixName == "transfer") do
    throwError "EVM Token ergonomics missing transfer entry"
  unless yul.contains "approve" || yul.contains "object \"" do
    throwError s!"EVM Token ergonomics Yul missing expected anchors\n{yul}"
  logInfo m!"proofforge-evm-token-ergonomics: digest = {ProofForge.Evm.IR.digestHex program}"

#pf_guard_evm_token_ergonomics
#pf_evm_build Examples.EvmTokenErgonomics

#guard ProofForge.Evm.Registry.digestOf "EvmTokenErgonomics" ==
  some "8e7ec772def9558a"
