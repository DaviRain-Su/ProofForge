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
  let some sourceBorsh := source.methods.find? (·.ixName == "borshOptions")
    | throwError "missing Borsh-option source method"
  unless sourceBorsh.annotations == #["svm.raw.v2:8:2:0:1:8,4,4"] &&
      sourceBorsh.paramWidths == #[1, 1, 8, 1, 4, 1, 4] do
    throwError "wrong source Borsh-option adapter metadata"
  let some sourcePair := source.methods.find? (·.ixName == "boundedPair")
    | throwError "missing bounded-pair source method"
  let pairPlan :=
    match sourcePair.ops with
    | #[.ite .le (.arg 0) (.arg 1)
        #[.returnU64 (.arg 0), .returnU64 (.arg 1)] #[.errorNamed "rejected"]] => true
    | _ => false
  unless sourcePair.annotations == #["svm.raw.v1:9:2:0"] &&
      sourcePair.paramWidths == #[8, 8] && sourcePair.retCount == 2 && pairPlan do
    throwError "wrong source bounded-pair plan"
  let some sourcePackedReturn := source.methods.find? (·.ixName == "borshSingletonPair")
    | throwError "missing packed-return source method"
  let packedReturnPlan :=
    match sourcePackedReturn.ops with
    | #[.ite .le (.arg 0) (.arg 1)
        #[.returnU64 (.lit 1), .returnU64 (.arg 0), .returnU64 (.arg 1)]
        #[.errorNamed "rejected"]] => true
    | _ => false
  unless sourcePackedReturn.annotations == #["svm.raw.v3:10:2:0:4,8,8"] &&
      sourcePackedReturn.paramWidths == #[8, 8] && sourcePackedReturn.retCount == 3 &&
      packedReturnPlan do
    throwError "wrong source packed-return plan"
  let some sourceEnumSmall := source.methods.find? (·.ixName == "enumSmall")
    | throwError "missing small enum-variant source method"
  let some sourceEnumWide := source.methods.find? (·.ixName == "enumWide")
    | throwError "missing wide enum-variant source method"
  unless sourceEnumSmall.annotations == #["svm.raw.v4:11:2:0:0:8"] &&
      sourceEnumSmall.paramWidths == #[1] &&
      sourceEnumWide.annotations == #["svm.raw.v4:11:2:0:1:8"] &&
      sourceEnumWide.paramWidths == #[8] do
    throwError "wrong source Borsh enum-variant metadata"
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
  let effectful := { source with methods := source.methods.map fun method =>
    if method.ixName == "packed" then
      { method with kind := .increment, ops := #[
          .ite .eq (.arg 0) (.lit 0)
            #[.okState (.arg 1)] #[.errorNamed "rejected"]
        ] }
    else method }
  let effectfulProgram ←
    match IR.fromExtracted effectful with
    | .ok program => pure program
    | .error reason => throwError reason
  let some effectfulPacked := effectfulProgram.methods.find? (·.ixName == "packed")
    | throwError "missing effectful packed method"
  unless effectfulPacked.kind == .get && effectfulPacked.ops == #[
      .ite .eq (.arg 0) (.lit 0)
        #[.returnU64 (.arg 1)] #[.errorNamed "rejected"]
    ] do
    throwError "effectful raw scalar result was not normalized away from managed State"
  let some packed := program.methods.find? (·.ixName == "packed")
    | throwError "missing packed SVM method"
  match packed.entry with
  | .raw entry =>
      unless entry.tag == 7 && entry.accountCount == 2 && entry.programAccount == 0 &&
          entry.paramWidths == #[1, 8] && entry.dataLen == 10 do
        throwError s!"wrong projected adapter: {repr entry}"
  | .generated => throwError "packed method lost its raw adapter"
  let some borsh := program.methods.find? (·.ixName == "borshOptions")
    | throwError "missing projected Borsh-option method"
  match borsh.entry with
  | .raw entry =>
      unless entry.tag == 8 && entry.accountCount == 2 && entry.programAccount == 0 &&
          entry.paramWidths == #[1, 1, 8, 1, 4, 1, 4] &&
          entry.optionWidths == #[8, 4, 4] && entry.fixedParamCount == 1 &&
          entry.minDataLen == 5 && entry.maxDataLen == 21 do
        throwError s!"wrong projected Borsh-option adapter: {repr entry}"
  | .generated => throwError "Borsh-option method lost its raw adapter"
  let some pair := program.methods.find? (·.ixName == "boundedPair")
    | throwError "missing projected bounded-pair method"
  match pair.entry with
  | .raw entry =>
      unless pair.kind == .get && pair.retCount == 2 && entry.tag == 9 &&
          entry.accountCount == 2 && entry.programAccount == 0 &&
          entry.paramWidths == #[8, 8] && entry.dataLen == 17 do
        throwError s!"wrong projected bounded-pair adapter: {repr entry}"
  | .generated => throwError "bounded-pair method lost its raw adapter"
  let pairCfg ←
    match pair.toCFG with
    | .ok graph => pure graph
    | .error reason => throwError reason
  unless pairCfg.blocks.any fun block =>
      match block.terminator with
      | .exit (.returnU64s values) => values.size == 2
      | _ => false do
    throwError "bounded effectful pair did not reach generic CFG returnU64s"
  let some packedReturn := program.methods.find? (·.ixName == "borshSingletonPair")
    | throwError "missing projected packed-return method"
  match packedReturn.entry with
  | .raw entry =>
      unless packedReturn.kind == .get && packedReturn.retCount == 3 && entry.tag == 10 &&
          entry.accountCount == 2 && entry.programAccount == 0 &&
          entry.paramWidths == #[8, 8] && entry.returnWidths == #[4, 8, 8] &&
          entry.returnDataLen == 20 && entry.returnScratchBytes == 20 do
        throwError s!"wrong projected packed-return adapter: {repr entry}"
  | .generated => throwError "packed-return method lost its raw adapter"
  let some enumSmall := program.methods.find? (·.ixName == "enumSmall")
    | throwError "missing projected small enum variant"
  let some enumWide := program.methods.find? (·.ixName == "enumWide")
    | throwError "missing projected wide enum variant"
  match enumSmall.entry, enumWide.entry with
  | .raw small, .raw wide =>
      unless small.tag == 11 && small.variant == some 0 && small.paramWidths == #[1] &&
          small.dataLen == 3 && small.returnWidths == #[8] &&
          wide.tag == 11 && wide.variant == some 1 && wide.paramWidths == #[8] &&
          wide.dataLen == 10 && wide.returnWidths == #[8] do
        throwError s!"wrong projected enum variants: {repr small}, {repr wide}"
  | _, _ => throwError "Borsh enum variant lost its raw adapter"
  unless IR.generatedAccountCount program == 1 do
    throwError "raw account geometry leaked into generated methods"
  let asm ←
    match Emit.emitAsm program with
    | .ok asm => pure asm
    | .error reason => throwError reason
  unless asm.contains "raw_walk_loop_route" &&
      asm.contains "call packed" && asm.contains "call borshOptions" &&
      asm.contains "call boundedPair" && asm.contains "lddw r2, 16" &&
      asm.contains "call borshSingletonPair" && asm.contains "lddw r2, 20" &&
      asm.contains "call enumSmall" && asm.contains "call enumWide" &&
      asm.contains "jeq r1, 0, raw_route_match_" &&
      asm.contains "jeq r1, 1, raw_route_match_" &&
      asm.contains "call sol_set_return_data" &&
      asm.contains "authenticate the declared executable program account" &&
      asm.contains "ldxb r1, [r8 + 9]" &&
      asm.contains "ldxdw r1, [r8 + 10]" &&
      asm.contains "jlt r2, 5, raw_route_next_" &&
      asm.contains "jgt r2, 21, raw_route_next_" &&
      asm.contains "decode a bounded Borsh Option suffix with exact cursor consumption" &&
      asm.contains "jne r1, 1, err_raw_borshOptions" &&
      asm.contains "jne r7, r9, err_raw_borshOptions" &&
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
#guard accepts (EntryAdapter.decode #["svm.raw.v2:8:4:0:1:8,4,4"] 7 #[1, 1, 8, 1, 4, 1, 4])
#guard accepts (EntryAdapter.decode #["svm.raw.v3:10:2:0:4,8,8"] 2 #[8, 8] 3)
#guard accepts (EntryAdapter.decode #["svm.raw.v4:11:2:0:0:8"] 1 #[1])
#guard accepts (EntryAdapter.decode #["svm.raw.v4:11:2:0:1:8"] 1 #[8])
#guard !accepts (EntryAdapter.decode #["svm.raw.v1:256:2:0"] 2 #[1, 8])
#guard !accepts (EntryAdapter.decode #["svm.raw.v1:7:2:2"] 2 #[1, 8])
#guard !accepts (EntryAdapter.decode #["svm.raw.v1:7:2:0"] 2 #[1, 3])
#guard !accepts (EntryAdapter.decode #["svm.raw.v2:8:4:0:1:8,4,4"] 7 #[1, 1, 8, 1, 8, 1, 4])
#guard !accepts (EntryAdapter.decode #["svm.raw.v2:8:4:0:1:8,3,4"] 7 #[1, 1, 8, 1, 4, 1, 4])
#guard !accepts (EntryAdapter.decode #["svm.raw.v3:10:2:0:4,8"] 2 #[8, 8] 3)
#guard !accepts (EntryAdapter.decode #["svm.raw.v3:10:2:0:4,3,8"] 2 #[8, 8] 3)
#guard !accepts (EntryAdapter.decode #["svm.raw.v4:11:2:0:256:8"] 1 #[1])
#guard accepts (EntryAdapter.validateUniqueTags #[
  .raw { tag := 11, accountCount := 2, programAccount := 0, variant := some 0, paramWidths := #[1] },
  .raw { tag := 11, accountCount := 2, programAccount := 0, variant := some 1, paramWidths := #[8] }
])
#guard !accepts (EntryAdapter.validateUniqueTags #[
  .raw { tag := 7, accountCount := 2, programAccount := 0, paramWidths := #[1] },
  .raw { tag := 7, accountCount := 2, programAccount := 0, paramWidths := #[8] }
])

end Tests.EntryAdapterSpec
