import Examples.RawEntry

namespace Tests.EntryAdapterSpec

open Lean Elab Command
open ProofForge.Svm

#guard Examples.RawEntry.packed (Examples.RawEntry.init 0) 3 40 == 43

elab "#pf_guard_entry_adapter" : command => do
  let env ← getEnv
  let source ←
    match ProofForge.Extract.extractModuleIR env `Examples.RawEntry with
    | .ok program => pure program
    | .error reason => throwError reason
  let some sourcePacked := source.methods.find? (·.ixName == "packed")
    | throwError "missing packed source method"
  unless sourcePacked.annotations == #["svm.raw.v1:7:2:0"] &&
      sourcePacked.paramWidths == #[1, 8] do
    throwError "wrong source adapter metadata"
  let program ←
    match IR.fromExtracted source with
    | .ok program => pure program
    | .error reason => throwError reason
  let stateCoupled := { source with methods := source.methods.map fun method =>
    if method.ixName == "packed" then
      { method with ops := #[.returnU64 (.field (.arg 2) "dummy")] }
    else method }
  match IR.fromExtracted stateCoupled with
  | .error reason =>
      unless reason.contains "external account storage, not managed State" do
        throwError s!"wrong managed-state rejection: {reason}"
  | .ok _ => throwError "raw entry was allowed to reinterpret its program account as State"
  let some packed := program.methods.find? (·.ixName == "packed")
    | throwError "missing packed SVM method"
  match packed.entry with
  | .raw entry =>
      unless entry.tag == 7 && entry.accountCount == 2 && entry.programAccount == 0 &&
          entry.paramWidths == #[1, 8] && entry.dataLen == 10 do
        throwError s!"wrong projected adapter: {repr entry}"
  | .generated => throwError "packed method lost its raw adapter"
  unless IR.generatedAccountCount program == 1 do
    throwError "raw account geometry leaked into generated methods"
  let asm ←
    match Emit.emitAsm program with
    | .ok asm => pure asm
    | .error reason => throwError reason
  unless asm.contains "raw_walk_loop_route" &&
      asm.contains "raw_route_match_0:\n  call packed" &&
      asm.contains "authenticate the declared executable program account" &&
      asm.contains "ldxb r1, [r8 + 9]" &&
      asm.contains "ldxdw r1, [r8 + 10]" &&
      asm.contains "ja raw_generated_entry" &&
      asm.contains "call initialize" do
    throwError "packed and generated entry assembly paths are not both present"
  let idl := Idl.emitProgramIdl program
  unless idl.contains "\"name\": \"initialize\"" && !idl.contains "\"name\": \"packed\"" do
    throwError "target IDL exposed protocol-owned raw wire as a generated instruction"
  match ProofForge.Extract.IR.toLegacyProgram source with
  | .error reason =>
      unless reason.contains "cannot preserve annotations" do
        throwError s!"wrong legacy adapter failure: {reason}"
  | .ok _ => throwError "legacy adapter silently discarded raw entry metadata"
  match ProofForge.Evm.IR.fromExtracted source with
  | .error reason =>
      unless reason.contains "cannot consume target annotations" do
        throwError s!"wrong foreign-target failure: {reason}"
  | .ok _ => throwError "EVM target silently discarded SVM entry metadata"

#pf_guard_entry_adapter

private def accepts (result : Except String α) : Bool :=
  result.isOk

#guard accepts (EntryAdapter.decode #["svm.raw.v1:7:2:0"] 2 #[1, 8])
#guard !accepts (EntryAdapter.decode #["svm.raw.v1:256:2:0"] 2 #[1, 8])
#guard !accepts (EntryAdapter.decode #["svm.raw.v1:7:2:2"] 2 #[1, 8])
#guard !accepts (EntryAdapter.decode #["svm.raw.v1:7:2:0"] 2 #[1, 3])
#guard !accepts (EntryAdapter.validateUniqueTags #[
  .raw { tag := 7, accountCount := 2, programAccount := 0, paramWidths := #[1] },
  .raw { tag := 7, accountCount := 2, programAccount := 0, paramWidths := #[8] }
])

end Tests.EntryAdapterSpec
