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
#guard (Environment.Query.blockHash256 3).arity == 1
#guard (Environment.Query.coinbase20 2).wellFormed
#guard !(Environment.Query.coinbase20 3).wellFormed
#guard Environment.Query.codeSize20.arity == 3
#guard (Environment.Query.codeHash32 3).wellFormed
#guard !(Environment.Query.codeHash32 4).wellFormed
#guard (Environment.Query.balance256 3).arity == 3
#guard !(Environment.Query.balance256 4).wellFormed
#guard
  (Environment.Query.prevRandao256 2).canonical (fun _ : UInt64 => "v") #[] == "erandao.2"
#guard
  (Environment.Query.blockHash256 1).canonical (fun _ : UInt64 => "v") #[37] ==
    "env.blockHash256.1(v)"

private def hasEnvironmentReturn (method : IR.Method) (wanted : Environment.Query) : Bool :=
  method.ops.any fun
    | .returnU64 (.ext (.component (.environment found)) operands) =>
        found == wanted && operands.size == wanted.arity
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
  requireQuery ctx "blockHash" .blockHash256
  requireQuery ctx "codeHash" .codeHash32
  requireQuery ctx "balance" .balance256
  let some codeSize := ctx.entries.find? (·.ixName == "codeSize")
    | throwError "missing EvmCtx.codeSize"
  unless hasEnvironmentReturn codeSize .codeSize20 do
    throwError "EvmCtx.codeSize escaped the Component bridge"
  for limb in [0, 1, 2] do
    unless hasEnvironmentReturn
        (tipJar.entries.find? (·.ixName == "coinbase")).get! (.coinbase20 limb) do
      throwError s!"TipJar.coinbase limb {limb} escaped the Component bridge"
  unless IR.digestHex ctx == (ProofForge.Evm.Registry.digestOf "EvmCtx").getD "" do
    throwError s!"EvmCtx registry digest is stale: {IR.digestHex ctx}"
  unless IR.digestHex tipJar == (ProofForge.Evm.Registry.digestOf "TipJar").getD "" do
    throwError s!"TipJar registry digest is stale: {IR.digestHex tipJar}"
  let ctxYul ←
    match ProofForge.Evm.Emit.emitYul ctx with
    | .ok yul => pure yul
    | .error reason => throwError reason
  let tipJarYul ←
    match ProofForge.Evm.Emit.emitYul tipJar with
    | .ok yul => pure yul
    | .error reason => throwError reason
  unless ctxYul.contains " := gas()" && tipJarYul.contains " := basefee()" &&
      tipJarYul.contains " := prevrandao()" && tipJarYul.contains " := gaslimit()" &&
      ctxYul.contains " := blockhash(" && tipJarYul.contains " := coinbase()" &&
      (ctxYul.splitOn "blockhash(").length == 2 &&
      (tipJarYul.splitOn "coinbase()").length == 2 &&
      (ctxYul.splitOn "extcodesize(").length == 2 &&
      (ctxYul.splitOn "extcodehash(").length == 2 &&
      (ctxYul.splitOn " := balance(").length == 2 do
    throwError "environment component omitted one or more pinned Cancun opcode bindings"

#pf_guard_evm_environment_component

end Tests.EvmEnvironmentSpec
