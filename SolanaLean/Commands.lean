import Lean
import SolanaLean.Profile
import SolanaLean.Extract
import SolanaLean.IR
import SolanaLean.Emit

open Lean Elab Command

namespace SolanaLean.Commands

/-- `#solana_check ident`：对声明做传递闭包剖面检查。 -/
elab "#solana_check " n:ident : command => do
  let name ← liftCoreM <| realizeGlobalConstNoOverload n
  let env ← getEnv
  match Profile.check env name with
  | .accept =>
    logInfo m!"solana-lean: accept {name}"
  | .reject reason =>
    throwError reason

/-- `#solana_extract init increment get`：抽出 Counter IR 并打印 sketch。 -/
elab "#solana_extract " initN:ident incrementN:ident getN:ident : command => do
  let initName ← liftCoreM <| realizeGlobalConstNoOverload initN
  let incrementName ← liftCoreM <| realizeGlobalConstNoOverload incrementN
  let getName ← liftCoreM <| realizeGlobalConstNoOverload getN
  let env ← getEnv
  match Extract.extractCounter env initName incrementName getName with
  | .error reason => throwError reason
  | .ok program => do
    let incSketch :=
      (program.methods.find? (·.kind == IR.MethodKind.increment)).map (·.sketch)
    match incSketch with
    | some sketch =>
      unless sketch.any (· == "SolanaLean.Counter.u64Max") do
        throwError "ir/mismatch: increment sketch missing u64Max"
    | none => throwError "extract/unsupported: missing increment"
    let extractedOps := program.methods.map (·.ops)
    let fixtureOps := IR.extractedCounter.methods.map (·.ops)
    unless extractedOps == fixtureOps do
      throwError "ir/mismatch: extract != IR.extractedCounter"
    match Emit.emitCounterAsm program with
    | .error reason => throwError reason
    | .ok asm =>
      unless asm.contains "entrypoint:" do
        throwError "assemble/tool: missing entrypoint"
      unless asm.contains "call sol_set_return_data" do
        throwError "assemble/tool: missing return data"
      unless asm.contains Emit.overflowCode do
        throwError "assemble/tool: missing overflow code"
      unless asm.contains Emit.discIncrement do
        throwError "assemble/tool: missing increment discriminator"
      logInfo m!"solana-lean: extracted {program.name} ops = {program.methods.map (fun m => repr m.ops)}"
      logInfo m!"solana-lean: extracted {program.name} sketches = {program.methods.map (·.sketch)}"
      logInfo m!"solana-lean: emitted {asm.length} bytes of sBPF assembly"

/-- `#solana_dump ident`：打印定义体，供抽出器对照。 -/
elab "#solana_dump " n:ident : command => do
  let name ← liftCoreM <| realizeGlobalConstNoOverload n
  let env ← getEnv
  match env.find? name with
  | none => throwError "unknown {name}"
  | some info =>
    match info.value? with
    | none => throwError "no value {name}"
    | some e => logInfo m!"{name} := {e}"

end SolanaLean.Commands
