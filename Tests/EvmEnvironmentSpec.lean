import Examples.EvmCtx
import Examples.TipJar
import ProofForge

/-!
R4-008 focused ownership guards for full-width EVM environment observations. Existing source
facades and runtime stubs must lower through the generic Component bridge while preserving their
canonical digest and one-observation-per-wide-result emission contract.
-/

namespace Tests.EvmEnvironmentSpec

open Lean Elab Command
open ProofForge.Evm

#guard (Environment.Query.gasLeft256 0).arity == 0
#guard (Environment.Query.baseFee256 3).wellFormed
#guard !(Environment.Query.gasLimit256 4).wellFormed
#guard
  (Environment.Query.prevRandao256 2).canonical (fun _ : UInt64 => "v") #[] == "erandao.2"

private def hasEnvironmentReturn (method : IR.Method) (wanted : Environment.Query) : Bool :=
  method.ops.any fun
    | .returnU64 (.ext (.component (.environment found)) #[]) => found == wanted
    | _ => false

private def requireQuery (program : IR.Program) (methodName : String)
    (makeQuery : Nat → Environment.Query) : CommandElabM Unit := do
  let some method := program.entries.find? (·.ixName == methodName)
    | throwError s!"missing environment consumer {program.name}.{methodName}"
  for limb in [0, 1, 2, 3] do
    unless hasEnvironmentReturn method (makeQuery limb) do
      throwError s!"{program.name}.{methodName} limb {limb} escaped the Component bridge"

private def extractEvm (module : Name) : CommandElabM IR.Program := do
  let env ← getEnv
  let source ←
    match ProofForge.Extract.extractModuleIR env module with
    | .ok source => pure source
    | .error reason => throwError reason
  match IR.fromExtracted source with
  | .ok program => pure program
  | .error reason => throwError reason

elab "#pf_guard_evm_environment_component" : command => do
  let ctx ← extractEvm `Examples.EvmCtx
  let tipJar ← extractEvm `Examples.TipJar
  requireQuery ctx "gasLeft" .gasLeft256
  requireQuery tipJar "baseFee" .baseFee256
  requireQuery tipJar "prevRandao" .prevRandao256
  requireQuery tipJar "gasLimit" .gasLimit256
  unless IR.digestHex ctx == (ProofForge.Evm.Registry.digestOf "EvmCtx").getD "" do
    throwError s!"EvmCtx digest changed during environment ownership refactor: {IR.digestHex ctx}"
  unless IR.digestHex tipJar == (ProofForge.Evm.Registry.digestOf "TipJar").getD "" do
    throwError s!"TipJar digest changed during environment ownership refactor: {IR.digestHex tipJar}"
  let ctxYul ←
    match ProofForge.Evm.Emit.emitYul ctx with
    | .ok yul => pure yul
    | .error reason => throwError reason
  let tipJarYul ←
    match ProofForge.Evm.Emit.emitYul tipJar with
    | .ok yul => pure yul
    | .error reason => throwError reason
  unless ctxYul.contains " := gas()" && tipJarYul.contains " := basefee()" &&
      tipJarYul.contains " := prevrandao()" && tipJarYul.contains " := gaslimit()" do
    throwError "environment component omitted one or more pinned Cancun opcode bindings"

#pf_guard_evm_environment_component

end Tests.EvmEnvironmentSpec
