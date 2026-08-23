import Lean
import ProofForge.Profile
import ProofForge.Extract
import ProofForge.Core.IR
import ProofForge.Svm.Emit
import ProofForge.Extract.LegacyGolden

open Lean Elab Command
open ProofForge
open ProofForge.Svm

namespace ProofForge.Svm.Commands

elab "#pf_check " n:ident : command => do
  let name ← liftCoreM <| realizeGlobalConstNoOverload n
  let env ← getEnv
  match Profile.check env name with
  | .accept => logInfo m!"proofforge: accept {name}"
  | .reject reason => throwError reason

syntax "#pf_extract " ident ident ident : command
syntax "#pf_extract " ident ident ident " with " str,+ : command

private def runExtract (initN mutN getN : TSyntax `ident) (fields? : Option (Array String)) :
    CommandElabM Unit := do
  let initName ← liftCoreM <| realizeGlobalConstNoOverload initN
  let mutName ← liftCoreM <| realizeGlobalConstNoOverload mutN
  let getName ← liftCoreM <| realizeGlobalConstNoOverload getN
  let env ← getEnv
  match Extract.extractProgramIR env initName mutName getName none fields? with
  | .error reason => throwError reason
  | .ok source => do
    let program ←
      match IR.fromExtracted source with
      | .ok program => pure program
      | .error reason => throwError reason
    let mutOps :=
      (program.methods.find? (·.kind == Core.IR.MethodKind.increment)).map (·.ops)
    match mutOps with
    | some ops =>
      unless IR.hasCheckedArith ops || IR.hasSelect ops ||
          ops.any (fun | .ite .. => true | .indexSet .. => true | .forAccum .. => true | .forBody .. => true | .storeField .. => true | _ => false) ||
          IR.hasInvoke ops do
        throwError "extract/unsupported: mutating method missing checked arith"
    | none => throwError "extract/unsupported: missing mutating method"
    match Emit.emitAsm program with
    | .error reason => throwError reason
    | .ok asm =>
      unless asm.contains "entrypoint:" do
        throwError "assemble/tool: missing entrypoint"
      logInfo m!"proofforge: fields = {program.fields}"
      logInfo m!"proofforge: extracted ops = {program.methods.map (fun m => repr m.ops)}"
      logInfo m!"proofforge: emitted {asm.length} bytes of sBPF assembly"

elab_rules : command
  | `(#pf_extract $initN:ident $mutN:ident $getN:ident) =>
      runExtract initN mutN getN none
  | `(#pf_extract $initN:ident $mutN:ident $getN:ident with $fs:str,*) => do
      let fields := (fs.getElems.map (·.getString)).toList.toArray
      runExtract initN mutN getN (some fields)

elab "#pf_build " n:ident : command => do
  let ns := n.getId
  let env ← getEnv
  match Extract.extractModuleIR env ns none with
  | .error reason => throwError reason
  | .ok source => do
    let program ←
      match IR.fromExtracted source with
      | .ok program => pure program
      | .error reason => throwError reason
    match Emit.emitAsm program with
    | .error reason => throwError reason
    | .ok asm =>
      unless asm.contains "entrypoint:" do
        throwError "assemble/tool: missing entrypoint"
      let digest := IR.digestHex program
      match ProofForge.Golden.digestOf program.name with
      | some want =>
        if digest != want then
          throwError s!"ir/mismatch: extracted {program.name} digest != fixture"
      | none => pure ()
      logInfo m!"proofforge: program {program.name} fields = {program.fields}"
      logInfo m!"proofforge: methods = {program.methods.map (fun m => m.ixName)}"
      logInfo m!"proofforge: digest = {digest}"
      logInfo m!"proofforge: emitted {asm.length} bytes of sBPF assembly"

elab "#pf_dump " n:ident : command => do
  let name ← liftCoreM <| realizeGlobalConstNoOverload n
  let env ← getEnv
  match env.find? name with
  | none => throwError "unknown {name}"
  | some info =>
    match info.value? with
    | none => throwError "no value {name}"
    | some e => logInfo m!"{name} := {e}"

end ProofForge.Svm.Commands
