import ProofForge
import ProofForge.Evm.IR
import ProofForge.Evm.Emit
import ProofForge.Evm.Commands
import Examples.EvmExceptErgonomics

open Lean Elab Command

elab "#pf_guard_evm_except_ergonomics" : command => do
  let env ← getEnv
  let source ←
    match ProofForge.Extract.extractModuleIR env `Examples.EvmExceptErgonomics with
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
  unless program.entries.any (·.ixName == "addViaAndThen") do
    throwError "EVM Except ergonomics missing addViaAndThen entry"
  unless yul.contains "addViaAndThen" || yul.contains "object \"" do
    throwError s!"EVM Except ergonomics Yul missing expected anchors\n{yul}"
  logInfo m!"proofforge-evm-except-ergonomics: digest = {ProofForge.Evm.IR.digestHex program}"

#pf_guard_evm_except_ergonomics
#pf_evm_build Examples.EvmExceptErgonomics

#guard ProofForge.Evm.Registry.digestOf "EvmExceptErgonomics" ==
  some "8def48aa72cd2c19"
