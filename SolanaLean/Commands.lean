import Lean
import SolanaLean.Profile
import SolanaLean.Extract
import SolanaLean.IR
import SolanaLean.Ops
import SolanaLean.Emit
import SolanaLean.Golden

open Lean Elab Command

namespace SolanaLean.Commands

elab "#solana_check " n:ident : command => do
  let name ← liftCoreM <| realizeGlobalConstNoOverload n
  let env ← getEnv
  match Profile.check env name with
  | .accept => logInfo m!"solana-lean: accept {name}"
  | .reject reason => throwError reason

syntax "#solana_extract " ident ident ident : command
syntax "#solana_extract " ident ident ident " with " str,+ : command

private def runExtract (initN mutN getN : TSyntax `ident) (fields? : Option (Array String)) :
    CommandElabM Unit := do
  let initName ← liftCoreM <| realizeGlobalConstNoOverload initN
  let mutName ← liftCoreM <| realizeGlobalConstNoOverload mutN
  let getName ← liftCoreM <| realizeGlobalConstNoOverload getN
  let env ← getEnv
  match Extract.extractProgram env initName mutName getName none fields? with
  | .error reason => throwError reason
  | .ok program => do
    let mutOps := (program.methods.find? (·.kind == IR.MethodKind.increment)).map (·.ops)
    match mutOps with
    | some ops =>
      unless Ops.hasCheckedArith ops || ops.any (fun | .ite .. => true | _ => false) do
        throwError "extract/unsupported: mutating method missing checked arith"
    | none => throwError "extract/unsupported: missing mutating method"
    match Emit.emitCounterAsm program with
    | .error reason => throwError reason
    | .ok asm =>
      unless asm.contains "entrypoint:" do
        throwError "assemble/tool: missing entrypoint"
      logInfo m!"solana-lean: fields = {program.fields}"
      logInfo m!"solana-lean: extracted ops = {program.methods.map (fun m => repr m.ops)}"
      logInfo m!"solana-lean: emitted {asm.length} bytes of sBPF assembly"

elab_rules : command
  | `(#solana_extract $initN:ident $mutN:ident $getN:ident) =>
      runExtract initN mutN getN none
  | `(#solana_extract $initN:ident $mutN:ident $getN:ident with $fs:str,*) => do
      let fields := (fs.getElems.map (·.getString)).toList.toArray
      runExtract initN mutN getN (some fields)

elab "#solana_build " n:ident : command => do
  let ns := n.getId
  let env ← getEnv
  match Extract.extractModule env ns none with
  | .error reason => throwError reason
  | .ok program => do
    match Emit.emitCounterAsm program with
    | .error reason => throwError reason
    | .ok asm =>
      unless asm.contains "entrypoint:" do
        throwError "assemble/tool: missing entrypoint"
      let digest := IR.digestHex program
      match SolanaLean.Golden.digestOf program.name with
      | some want =>
        if digest != want then
          throwError s!"ir/mismatch: extracted {program.name} digest != fixture"
      | none => pure ()
      logInfo m!"solana-lean: program {program.name} fields = {program.fields}"
      logInfo m!"solana-lean: methods = {program.methods.map (fun m => m.ixName)}"
      logInfo m!"solana-lean: digest = {digest}"
      logInfo m!"solana-lean: emitted {asm.length} bytes of sBPF assembly"

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
