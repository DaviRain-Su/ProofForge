import Lean
import SolanaLean.Profile
import SolanaLean.Extract
import SolanaLean.IR

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
    logInfo m!"solana-lean: extracted {program.name} sketches = {program.methods.map (·.sketch)}"

end SolanaLean.Commands
