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
#guard (Environment.Query.origin20 2).wellFormed
#guard !(Environment.Query.origin20 3).wellFormed
#guard (Environment.Query.gasPrice256 3).wellFormed
#guard !(Environment.Query.gasPrice256 4).wellFormed
#guard (Environment.Query.blobBaseFee256 3).wellFormed
#guard !(Environment.Query.blobBaseFee256 4).wellFormed
#guard (Environment.Query.blobHash32 3).arity == 1
#guard !(Environment.Query.blobHash32 4).wellFormed
#guard Environment.Query.selector4.arity == 0
#guard Environment.Query.selector4.wellFormed
#guard Environment.Query.calldataSize.arity == 0
#guard Environment.Query.calldataSize.wellFormed
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

private partial def valueMentionsEnvironment (wanted : Environment.Query) : Ops.Val → Bool
  | .field base _ | .bitNot base => valueMentionsEnvironment wanted base
  | .bitAnd left right | .bitOr left right | .bitXor left right
  | .shiftL left right | .shiftR left right
  | .addU64 left right | .subU64 left right | .mulU64 left right
  | .divU64 left right | .modU64 left right =>
      valueMentionsEnvironment wanted left || valueMentionsEnvironment wanted right
  | .indexGet base _ index _ _ =>
      valueMentionsEnvironment wanted base || valueMentionsEnvironment wanted index
  | .select _ left right thenValue elseValue =>
      valueMentionsEnvironment wanted left || valueMentionsEnvironment wanted right ||
        valueMentionsEnvironment wanted thenValue || valueMentionsEnvironment wanted elseValue
  | .ext (.component (.environment found)) operands =>
      (found == wanted && operands.size == wanted.arity) ||
        operands.any (valueMentionsEnvironment wanted)
  | .ext _ operands => operands.any (valueMentionsEnvironment wanted)
  | _ => false

private def returnMentionsEnvironment (method : IR.Method) (wanted : Environment.Query) : Bool :=
  method.ops.any fun
    | .returnU64 value => valueMentionsEnvironment wanted value
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
  requireQuery ctx "gasPrice" .gasPrice256
  requireQuery ctx "blobBaseFee" .blobBaseFee256
  requireQuery ctx "blobHash" .blobHash32
  let some selector := ctx.entries.find? (·.ixName == "selector")
    | throwError "missing EvmCtx.selector"
  unless hasEnvironmentReturn selector .selector4 do
    throwError "EvmCtx.selector escaped the Component bridge"
  let some calldataSize := ctx.entries.find? (·.ixName == "calldataSize")
    | throwError "missing EvmCtx.calldataSize"
  unless hasEnvironmentReturn calldataSize .calldataSize do
    throwError "EvmCtx.calldataSize escaped the Component bridge"
  requireQuery ctx "blockHash" .blockHash256
  requireQuery ctx "codeHash" .codeHash32
  requireQuery ctx "balance" .balance256
  let some codeSize := ctx.entries.find? (·.ixName == "codeSize")
    | throwError "missing EvmCtx.codeSize"
  unless hasEnvironmentReturn codeSize .codeSize20 do
    throwError "EvmCtx.codeSize escaped the Component bridge"
  let some hasCode := ctx.entries.find? (·.ixName == "hasCode")
    | throwError "missing EvmCtx.hasCode"
  unless returnMentionsEnvironment hasCode .codeSize20 do
    throwError "EvmCtx.hasCode escaped the Component bridge"
  for limb in [0, 1, 2] do
    unless hasEnvironmentReturn
        (tipJar.entries.find? (·.ixName == "coinbase")).get! (.coinbase20 limb) do
      throwError s!"TipJar.coinbase limb {limb} escaped the Component bridge"
    unless hasEnvironmentReturn
        (ctx.entries.find? (·.ixName == "origin")).get! (.origin20 limb) do
      throwError s!"EvmCtx.origin limb {limb} escaped the Component bridge"
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
      ctxYul.contains " := gasprice()" && ctxYul.contains " := blobbasefee()" &&
      ctxYul.contains " := blobhash(" && ctxYul.contains " := origin()" &&
      ctxYul.contains " := calldataload(0)" &&
      ctxYul.contains " := calldatasize()" &&
      ctxYul.contains " := blockhash(" && tipJarYul.contains " := coinbase()" &&
      (ctxYul.splitOn "gasprice()").length == 2 &&
      (ctxYul.splitOn "blobbasefee()").length == 2 &&
      (ctxYul.splitOn "blobhash(").length == 2 &&
      (ctxYul.splitOn "origin()").length == 2 &&
      (ctxYul.splitOn " := calldataload(0)").length == 2 &&
      (ctxYul.splitOn " := calldatasize()").length ≥ 2 &&
      (ctxYul.splitOn "blockhash(").length == 2 &&
      (tipJarYul.splitOn "coinbase()").length == 2 &&
      (ctxYul.splitOn "extcodesize(").length == 3 &&
      (ctxYul.splitOn "extcodehash(").length == 2 &&
      (ctxYul.splitOn " := balance(").length == 2 do
    throwError "environment component omitted one or more pinned Cancun opcode bindings"

#pf_guard_evm_environment_component

end Tests.EvmEnvironmentSpec
