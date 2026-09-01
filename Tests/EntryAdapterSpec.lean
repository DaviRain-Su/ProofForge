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
  let some sourceEnumOptional := source.methods.find? (·.ixName == "enumOptional")
    | throwError "missing optional-return enum-variant source method"
  unless sourceEnumSmall.annotations == #["svm.raw.v4:11:2:0:0:8"] &&
      sourceEnumSmall.paramWidths == #[1] &&
      sourceEnumWide.annotations == #["svm.raw.v4:11:2:0:1:8"] &&
      sourceEnumWide.paramWidths == #[8] &&
      sourceEnumOptional.annotations == #["svm.raw.v5:11:2:0:2:8"] &&
      sourceEnumOptional.paramWidths == #[1, 8] && sourceEnumOptional.retCount == 2 do
    throwError "wrong source Borsh enum-variant metadata"
  let some sourceEcho128 := source.methods.find? (·.ixName == "echo128")
    | throwError "missing shared UInt128 raw method"
  let some sourceEchoBytes12 := source.methods.find? (·.ixName == "echoBytes12")
    | throwError "missing shared FixedBytes raw method"
  unless sourceEcho128.paramTypes == #[.uint128] && sourceEcho128.retTypes == #[.uint128] &&
      sourceEcho128.paramWidths == #[16] && sourceEcho128.retCount == 2 &&
      sourceEchoBytes12.paramTypes == #[.fixedBytes 12] &&
      sourceEchoBytes12.retTypes == #[.fixedBytes 12] &&
      sourceEchoBytes12.paramWidths == #[12] && sourceEchoBytes12.retCount == 2 do
    throwError "wrong shared SVM codec metadata"
  let some sourceAggregate := source.methods.find? (·.ixName == "aggregate")
    | throwError "missing aggregate raw method"
  unless sourceAggregate.paramCount == 3 && sourceAggregate.paramWidths.isEmpty &&
      sourceAggregate.paramTypes.isEmpty && sourceAggregate.paramSchemas.size == 3 do
    throwError "wrong aggregate source metadata"
  let some sourceOption := source.methods.find? (·.ixName == "optionValue")
    | throwError "missing logical Option raw method"
  let some sourceTagged := source.methods.find? (·.ixName == "taggedValue")
    | throwError "missing logical enum raw method"
  let some sourceBounded := source.methods.find? (·.ixName == "boundedValues")
    | throwError "missing logical bounded-vector raw method"
  let some sourceBytes := source.methods.find? (·.ixName == "boundedBytes")
    | throwError "missing logical bounded-bytes raw method"
  let some sourceString := source.methods.find? (·.ixName == "boundedString")
    | throwError "missing logical bounded-string raw method"
  unless sourceOption.annotations == #["svm.raw.v1:15:2:0"] &&
      sourceOption.paramCount == 1 && sourceOption.paramWidths.isEmpty &&
      sourceOption.paramSchemas == #[.option (.scalar .uint64)] &&
      sourceTagged.annotations == #["svm.raw.v1:16:2:0"] &&
      sourceTagged.paramCount == 1 && sourceTagged.paramWidths.isEmpty &&
      (match sourceTagged.paramSchemas[0]? with
        | some (ProofForge.Core.Codec.Schema.enumeration
            "Examples.RawEntry.TaggedRequest" 8 variants) =>
            variants.size == 3
        | _ => false) &&
      sourceBounded.annotations == #["svm.raw.v1:17:2:0"] &&
      sourceBounded.paramCount == 1 && sourceBounded.paramWidths.isEmpty &&
      sourceBounded.paramSchemas == #[.boundedArray 4 (.scalar .uint64)] &&
      sourceBytes.annotations == #["svm.raw.v1:18:2:0"] &&
      sourceBytes.paramSchemas == #[.boundedBytes 8] &&
      sourceString.annotations == #["svm.raw.v1:19:2:0"] &&
      sourceString.paramSchemas == #[.boundedString 8] do
    throwError "ordinary tagged/bounded source schemas were not preserved"
  let some sourceEchoBoundedValues := source.methods.find? (·.ixName == "echoBoundedValues")
    | throwError "missing bounded-vector return source method"
  let some sourceEchoBoundedBytes := source.methods.find? (·.ixName == "echoBoundedBytes")
    | throwError "missing bounded-bytes return source method"
  let some sourceEchoBoundedString := source.methods.find? (·.ixName == "echoBoundedString")
    | throwError "missing bounded-string return source method"
  let some sourceMakeBoundedString := source.methods.find? (·.ixName == "makeBoundedString")
    | throwError "missing constructed bounded-string source method"
  let some sourceEchoOptionValue := source.methods.find? (·.ixName == "echoOptionValue")
    | throwError "missing tagged Option return source method"
  let some sourceEchoTaggedValue := source.methods.find? (·.ixName == "echoTaggedValue")
    | throwError "missing tagged enum return source method"
  let some sourceEchoPubkey := source.methods.find? (·.ixName == "echoPubkey")
    | throwError "missing Pubkey return source method"
  let some sourceBytesEqual := source.methods.find? (·.ixName == "bytesEqual")
    | throwError "missing bounded-bytes equality source method"
  let some sourceStringsEqual := source.methods.find? (·.ixName == "stringsEqual")
    | throwError "missing bounded-string equality source method"
  let some sourceBytesLess := source.methods.find? (·.ixName == "bytesLess")
    | throwError "missing bounded-bytes ordering source method"
  let some sourceStringsLess := source.methods.find? (·.ixName == "stringsLess")
    | throwError "missing bounded-string ordering source method"
  let some sourceBytesContains := source.methods.find? (·.ixName == "bytesContains")
    | throwError "missing bounded-bytes substring source method"
  let some sourceStringsContains := source.methods.find? (·.ixName == "stringsContains")
    | throwError "missing bounded-string substring source method"
  let some sourceBytesStarts := source.methods.find? (·.ixName == "bytesStartsWith")
    | throwError "missing bounded-bytes prefix source method"
  let some sourceStringsStarts := source.methods.find? (·.ixName == "stringsStartsWith")
    | throwError "missing bounded-string prefix source method"
  let some sourceBytesEnds := source.methods.find? (·.ixName == "bytesEndsWith")
    | throwError "missing bounded-bytes suffix source method"
  let some sourceStringsEnds := source.methods.find? (·.ixName == "stringsEndsWith")
    | throwError "missing bounded-string suffix source method"
  let some sourceBytesFind := source.methods.find? (·.ixName == "bytesFindIndex")
    | throwError "missing bounded-bytes first-position source method"
  let some sourceStringsFind := source.methods.find? (·.ixName == "stringsFindIndex")
    | throwError "missing bounded-string first-position source method"
  let some sourceEchoBoundedU128 := source.methods.find? (·.ixName == "echoBoundedU128")
    | throwError "missing wide bounded-vector return source method"
  let some sourceEchoOptionU128 := source.methods.find? (·.ixName == "echoOptionU128")
    | throwError "missing wide Option return source method"
  let pubkeySchema := .record "ProofForge.Svm.Sdk.Pubkey" #[
    ("word0", .scalar .uint64), ("word1", .scalar .uint64),
    ("word2", .scalar .uint64), ("word3", .scalar .uint64)]
  unless sourceEchoBoundedValues.annotations == #["svm.raw.v1:20:2:0"] &&
      sourceEchoBoundedValues.retSchema == .boundedArray 4 (.scalar .uint16) &&
      sourceEchoBoundedValues.retCount == 5 &&
      sourceEchoBoundedBytes.annotations == #["svm.raw.v1:21:2:0"] &&
      sourceEchoBoundedBytes.retSchema == .boundedBytes 8 && sourceEchoBoundedBytes.retCount == 9 &&
      sourceEchoBoundedString.annotations == #["svm.raw.v1:22:2:0"] &&
      sourceEchoBoundedString.retSchema == .boundedString 8 && sourceEchoBoundedString.retCount == 9 &&
      sourceMakeBoundedString.annotations == #["svm.raw.v1:23:2:0"] &&
      sourceMakeBoundedString.paramWidths == #[4, 1, 1, 1, 1, 1, 1, 1, 1] &&
      sourceMakeBoundedString.retSchema == .boundedString 8 &&
      sourceMakeBoundedString.retCount == 9 &&
      sourceEchoOptionValue.annotations == #["svm.raw.v1:24:2:0"] &&
      sourceEchoOptionValue.retSchema == .option (.scalar .uint64) &&
      sourceEchoOptionValue.retCount == 2 &&
      sourceEchoTaggedValue.annotations == #["svm.raw.v1:25:2:0"] &&
      sourceEchoTaggedValue.retCount == 3 &&
      sourceEchoPubkey.annotations == #["svm.raw.v1:26:2:0"] &&
      sourceEchoPubkey.paramCount == 1 && sourceEchoPubkey.paramWidths.isEmpty &&
      sourceEchoPubkey.paramSchemas == #[pubkeySchema] &&
      sourceEchoPubkey.retSchema == pubkeySchema && sourceEchoPubkey.retCount == 4 &&
      sourceBytesEqual.annotations == #["svm.raw.v1:27:2:0"] &&
      sourceBytesEqual.paramSchemas == #[.boundedBytes 8, .boundedBytes 8] &&
      sourceBytesEqual.retSchema == .scalar .boolean && sourceBytesEqual.retCount == 1 &&
      sourceStringsEqual.annotations == #["svm.raw.v1:28:2:0"] &&
      sourceStringsEqual.paramSchemas == #[.boundedString 8, .boundedString 8] &&
      sourceStringsEqual.retSchema == .scalar .boolean && sourceStringsEqual.retCount == 1 &&
      sourceBytesLess.annotations == #["svm.raw.v1:29:2:0"] &&
      sourceBytesLess.paramSchemas == #[.boundedBytes 8, .boundedBytes 8] &&
      sourceBytesLess.retSchema == .scalar .boolean && sourceBytesLess.retCount == 1 &&
      sourceStringsLess.annotations == #["svm.raw.v1:30:2:0"] &&
      sourceStringsLess.paramSchemas == #[.boundedString 8, .boundedString 8] &&
      sourceStringsLess.retSchema == .scalar .boolean && sourceStringsLess.retCount == 1 &&
      sourceBytesContains.annotations == #["svm.raw.v1:31:2:0"] &&
      sourceBytesContains.paramSchemas == #[.boundedBytes 8, .boundedBytes 8] &&
      sourceBytesContains.retSchema == .scalar .boolean && sourceBytesContains.retCount == 1 &&
      sourceStringsContains.annotations == #["svm.raw.v1:32:2:0"] &&
      sourceStringsContains.paramSchemas == #[.boundedString 8, .boundedString 8] &&
      sourceStringsContains.retSchema == .scalar .boolean &&
      sourceStringsContains.retCount == 1 &&
      sourceBytesStarts.annotations == #["svm.raw.v1:33:2:0"] &&
      sourceBytesStarts.paramSchemas == #[.boundedBytes 8, .boundedBytes 8] &&
      sourceBytesStarts.retSchema == .scalar .boolean && sourceBytesStarts.retCount == 1 &&
      sourceStringsStarts.annotations == #["svm.raw.v1:34:2:0"] &&
      sourceStringsStarts.paramSchemas == #[.boundedString 8, .boundedString 8] &&
      sourceStringsStarts.retSchema == .scalar .boolean && sourceStringsStarts.retCount == 1 &&
      sourceBytesEnds.annotations == #["svm.raw.v1:35:2:0"] &&
      sourceBytesEnds.paramSchemas == #[.boundedBytes 8, .boundedBytes 8] &&
      sourceBytesEnds.retSchema == .scalar .boolean && sourceBytesEnds.retCount == 1 &&
      sourceStringsEnds.annotations == #["svm.raw.v1:36:2:0"] &&
      sourceStringsEnds.paramSchemas == #[.boundedString 8, .boundedString 8] &&
      sourceStringsEnds.retSchema == .scalar .boolean && sourceStringsEnds.retCount == 1 &&
      sourceBytesFind.annotations == #["svm.raw.v1:37:2:0"] &&
      sourceBytesFind.paramSchemas == #[.boundedBytes 8, .boundedBytes 8] &&
      sourceBytesFind.retSchema == .option (.scalar .uint64) && sourceBytesFind.retCount == 2 &&
      sourceStringsFind.annotations == #["svm.raw.v1:38:2:0"] &&
      sourceStringsFind.paramSchemas == #[.boundedString 8, .boundedString 8] &&
      sourceStringsFind.retSchema == .option (.scalar .uint64) &&
      sourceStringsFind.retCount == 2 &&
      sourceEchoBoundedU128.annotations == #["svm.raw.v1:39:2:0"] &&
      sourceEchoBoundedU128.retSchema == .boundedArray 2 (.scalar .uint128) &&
      sourceEchoBoundedU128.retCount == 5 &&
      sourceEchoOptionU128.annotations == #["svm.raw.v1:40:2:0"] &&
      sourceEchoOptionU128.retSchema == .option (.scalar .uint128) &&
      sourceEchoOptionU128.retCount == 3 do
    throwError "bounded/tagged return values were not expanded to fixed source frames"
  let rec loopBounds (fuel : Nat) (ops : Array ProofForge.Extract.Ops.Op) : Array Nat :=
    match fuel with
    | 0 => #[]
    | fuel' + 1 => ops.foldl (init := #[]) fun bounds op =>
        match op with
        | .forBody bound body => bounds.push bound ++ loopBounds fuel' body
        | .ite _ _ _ yes no => bounds ++ loopBounds fuel' yes ++ loopBounds fuel' no
        | _ => bounds
  for method in #[sourceBytesContains, sourceStringsContains, sourceBytesStarts,
      sourceStringsStarts, sourceBytesEnds, sourceStringsEnds, sourceBytesFind,
      sourceStringsFind] do
    unless loopBounds 8 method.ops == #[64] do
      throwError s!"{method.ixName} lost its static SVM product loop: {loopBounds 8 method.ops}"
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
  let some enumOptional := program.methods.find? (·.ixName == "enumOptional")
    | throwError "missing projected optional-return enum variant"
  match enumSmall.entry, enumWide.entry, enumOptional.entry with
  | .raw small, .raw wide, .raw optional =>
      unless small.tag == 11 && small.variant == some 0 && small.paramWidths == #[1] &&
          small.dataLen == 3 && small.returnWidths == #[8] &&
          wide.tag == 11 && wide.variant == some 1 && wide.paramWidths == #[8] &&
          wide.dataLen == 10 && wide.returnWidths == #[8] &&
          enumOptional.retCount == 2 && optional.tag == 11 && optional.variant == some 2 &&
          optional.paramWidths == #[1, 8] && optional.dataLen == 11 &&
          optional.returnWidths == #[8] && optional.returnDataLen == 8 &&
          optional.optionalReturnData do
        throwError s!"wrong projected enum variants: {repr small}, {repr wide}, {repr optional}"
  | _, _, _ => throwError "Borsh enum variant lost its raw adapter"
  let some echo128 := program.methods.find? (·.ixName == "echo128")
    | throwError "missing projected shared UInt128 method"
  let some echoBytes12 := program.methods.find? (·.ixName == "echoBytes12")
    | throwError "missing projected shared FixedBytes method"
  match echo128.entry, echoBytes12.entry with
  | .raw wide, .raw bytes =>
      unless wide.paramLeafWidths == #[8, 8] && wide.paramLeafCounts == #[2] &&
          wide.inferredReturnWidths == #[8, 8] && wide.dataLen == 17 &&
          wide.returnDataLen == 16 &&
          bytes.paramLeafWidths == #[8, 4] && bytes.paramLeafCounts == #[2] &&
          bytes.inferredReturnWidths == #[8, 4] && bytes.dataLen == 13 &&
          bytes.returnDataLen == 12 && bytes.returnScratchBytes == 16 &&
          bytes.canonical.contains "borsh-leaves.[8,4].borsh-returns.[8,4]" do
        throwError s!"wrong shared SVM codec plans: {repr wide}, {repr bytes}"
  | _, _ => throwError "shared codec method lost its raw adapter"
  let some aggregate := program.methods.find? (·.ixName == "aggregate")
    | throwError "missing projected aggregate method"
  match aggregate.entry with
  | .raw entry =>
      unless entry.tag == 14 && entry.paramCount == 3 && entry.paramWidths.isEmpty &&
          entry.paramLeafWidths == #[8, 1, 1, 4, 8, 2, 2, 2] &&
          entry.paramLeafCounts == #[3, 2, 3] &&
          entry.paramLeafBooleans == #[false, false, true, false, false, false, false, false] &&
          entry.dataLen == 29 &&
          entry.canonical.contains "borsh-bool.[2]" do
        throwError s!"wrong aggregate Borsh plan: {repr entry}"
  | .generated => throwError "aggregate method lost its raw adapter"
  let _ ←
    match aggregate.toCFG with
    | .ok graph => pure graph
    | .error reason => throwError s!"aggregate Borsh locals did not reach CFG: {reason}"
  let some optionValue := program.methods.find? (·.ixName == "optionValue")
    | throwError "missing projected logical Option method"
  let some taggedValue := program.methods.find? (·.ixName == "taggedValue")
    | throwError "missing projected logical enum method"
  let some boundedValues := program.methods.find? (·.ixName == "boundedValues")
    | throwError "missing projected logical bounded-vector method"
  let some boundedBytes := program.methods.find? (·.ixName == "boundedBytes")
    | throwError "missing projected logical bounded-bytes method"
  let some boundedString := program.methods.find? (·.ixName == "boundedString")
    | throwError "missing projected logical bounded-string method"
  match optionValue.entry, taggedValue.entry with
  | .raw optionEntry, .raw taggedEntry =>
      unless optionEntry.tag == 15 && optionEntry.paramBorshPlans.size == 1 &&
          optionEntry.paramLeafWidths == #[1, 8] && optionEntry.paramLeafCounts == #[2] &&
          optionEntry.minDataLen == 2 && optionEntry.maxDataLen == 10 &&
          optionEntry.canonical.contains "borsh-schema.[1-9:o" &&
          taggedEntry.tag == 16 && taggedEntry.paramBorshPlans.size == 1 &&
          taggedEntry.paramLeafWidths == #[1, 8, 8] && taggedEntry.paramLeafCounts == #[3] &&
          taggedEntry.minDataLen == 2 && taggedEntry.maxDataLen == 18 &&
          taggedEntry.canonical.contains "borsh-schema.[1-17:e" do
        throwError s!"wrong tagged Borsh plans: {repr optionEntry}, {repr taggedEntry}"
  | _, _ => throwError "logical tagged method lost its raw adapter"
  let _ ←
    match optionValue.toCFG with
    | .ok graph => pure graph
    | .error reason => throwError s!"logical Option did not bind to fixed locals: {reason}"
  let _ ←
    match taggedValue.toCFG with
    | .ok graph => pure graph
    | .error reason => throwError s!"logical enum did not bind to fixed locals: {reason}"
  match boundedValues.entry with
  | .raw boundedEntry =>
      unless boundedEntry.tag == 17 && boundedEntry.paramBorshPlans.size == 1 &&
          boundedEntry.paramLeafWidths == #[4, 8, 8, 8, 8] &&
          boundedEntry.paramLeafCounts == #[5] && boundedEntry.minDataLen == 5 &&
          boundedEntry.maxDataLen == 37 &&
          boundedEntry.canonical.contains "borsh-schema.[4-36:a" do
        throwError s!"wrong bounded-array Borsh plan: {repr boundedEntry}"
  | .generated => throwError "logical bounded vector lost its raw adapter"
  let _ ←
    match boundedValues.toCFG with
    | .ok graph => pure graph
    | .error reason => throwError s!"logical bounded vector did not bind to fixed locals: {reason}"
  for (method, tag, marker) in [
      (boundedBytes, 18, "borsh-schema.[4-12:b"),
      (boundedString, 19, "borsh-schema.[4-12:t")
    ] do
    match method.entry with
    | .raw entry =>
        unless entry.tag == tag && entry.paramBorshPlans.size == 1 &&
            entry.paramLeafWidths == #[4, 1, 1, 1, 1, 1, 1, 1, 1] &&
            entry.paramLeafCounts == #[9] && entry.minDataLen == 5 &&
            entry.maxDataLen == 13 && entry.canonical.contains marker do
          throwError s!"wrong bounded byte/string Borsh plan: {repr entry}"
    | .generated => throwError "logical bounded byte/string lost its raw adapter"
    let _ ←
      match method.toCFG with
      | .ok graph => pure graph
      | .error reason => throwError s!"bounded byte/string did not bind to fixed locals: {reason}"
  let some echoBoundedValues := program.methods.find? (·.ixName == "echoBoundedValues")
    | throwError "missing projected bounded-vector return method"
  let some echoBoundedBytes := program.methods.find? (·.ixName == "echoBoundedBytes")
    | throwError "missing projected bounded-bytes return method"
  let some echoBoundedString := program.methods.find? (·.ixName == "echoBoundedString")
    | throwError "missing projected bounded-string return method"
  let some makeBoundedString := program.methods.find? (·.ixName == "makeBoundedString")
    | throwError "missing projected constructed bounded-string method"
  let some echoOptionValue := program.methods.find? (·.ixName == "echoOptionValue")
    | throwError "missing projected tagged Option return method"
  let some echoTaggedValue := program.methods.find? (·.ixName == "echoTaggedValue")
    | throwError "missing projected tagged enum return method"
  match echoBoundedValues.entry, echoBoundedBytes.entry, echoBoundedString.entry,
      makeBoundedString.entry with
  | .raw values, .raw bytes, .raw string, .raw constructed =>
      unless values.tag == 20 && values.returnBorshPlan == some (.boundedArray 4 #[2]) &&
          values.returnDataLen == 12 && values.returnScratchBytes == 20 &&
          values.canonical.contains "borsh-return-schema.array.4.[2]" &&
          bytes.tag == 21 && bytes.returnBorshPlan == some (.packedBytes 8 false) &&
          bytes.returnDataLen == 12 && bytes.returnScratchBytes == 20 &&
          string.tag == 22 && string.returnBorshPlan == some (.packedBytes 8 true) &&
          string.returnDataLen == 12 && string.returnScratchBytes == 20 &&
          constructed.tag == 23 && constructed.paramCount == 9 && constructed.dataLen == 13 &&
          constructed.returnBorshPlan == some (.packedBytes 8 true) &&
          constructed.returnDataLen == 12 && constructed.returnScratchBytes == 20 do
        throwError s!"wrong bounded Borsh return plans: {repr values}, {repr bytes}, " ++
          s!"{repr string}, {repr constructed}"
  | _, _, _, _ => throwError "bounded return method lost its raw adapter"
  match echoOptionValue.entry, echoTaggedValue.entry with
  | .raw option, .raw tagged =>
      unless option.tag == 24 && option.returnBorshPlan == some (.option #[8]) &&
          option.returnDataLen == 9 && option.returnScratchBytes == 17 &&
          option.canonical.contains "borsh-return-schema.option.[8]" &&
          tagged.tag == 25 && tagged.returnBorshPlan == some (.enumeration #[0, 1, 2]) &&
          tagged.returnDataLen == 17 && tagged.returnScratchBytes == 25 &&
          tagged.canonical.contains "borsh-return-schema.enum.[0,1,2]" do
        throwError s!"wrong tagged Borsh return plans: {repr option}, {repr tagged}"
  | _, _ => throwError "tagged return method lost its raw adapter"
  let some echoPubkey := program.methods.find? (·.ixName == "echoPubkey")
    | throwError "missing projected Pubkey method"
  match echoPubkey.entry with
  | .raw entry =>
      unless entry.tag == 26 && entry.paramCount == 1 && entry.paramWidths.isEmpty &&
          entry.paramLeafWidths == #[8, 8, 8, 8] && entry.paramLeafCounts == #[4] &&
          entry.inferredReturnWidths == #[8, 8, 8, 8] && entry.dataLen == 33 &&
          entry.returnDataLen == 32 && entry.returnScratchBytes == 32 &&
          entry.canonical.contains "borsh-leaves.[8,8,8,8]" do
        throwError s!"wrong Pubkey Borsh boundary plan: {repr entry}"
  | .generated => throwError "Pubkey method lost its raw adapter"
  let some bytesEqual := program.methods.find? (·.ixName == "bytesEqual")
    | throwError "missing projected bounded-bytes equality method"
  let some stringsEqual := program.methods.find? (·.ixName == "stringsEqual")
    | throwError "missing projected bounded-string equality method"
  let some bytesLess := program.methods.find? (·.ixName == "bytesLess")
    | throwError "missing projected bounded-bytes ordering method"
  let some stringsLess := program.methods.find? (·.ixName == "stringsLess")
    | throwError "missing projected bounded-string ordering method"
  let some bytesContains := program.methods.find? (·.ixName == "bytesContains")
    | throwError "missing projected bounded-bytes substring method"
  let some stringsContains := program.methods.find? (·.ixName == "stringsContains")
    | throwError "missing projected bounded-string substring method"
  let some bytesStarts := program.methods.find? (·.ixName == "bytesStartsWith")
    | throwError "missing projected bounded-bytes prefix method"
  let some stringsStarts := program.methods.find? (·.ixName == "stringsStartsWith")
    | throwError "missing projected bounded-string prefix method"
  let some bytesEnds := program.methods.find? (·.ixName == "bytesEndsWith")
    | throwError "missing projected bounded-bytes suffix method"
  let some stringsEnds := program.methods.find? (·.ixName == "stringsEndsWith")
    | throwError "missing projected bounded-string suffix method"
  let some bytesFind := program.methods.find? (·.ixName == "bytesFindIndex")
    | throwError "missing projected bounded-bytes first-position method"
  let some stringsFind := program.methods.find? (·.ixName == "stringsFindIndex")
    | throwError "missing projected bounded-string first-position method"
  for (method, tag, marker) in [
      (bytesEqual, 27, "borsh-schema.[4-12:b"),
      (stringsEqual, 28, "borsh-schema.[4-12:t"),
      (bytesLess, 29, "borsh-schema.[4-12:b"),
      (stringsLess, 30, "borsh-schema.[4-12:t"),
      (bytesContains, 31, "borsh-schema.[4-12:b"),
      (stringsContains, 32, "borsh-schema.[4-12:t"),
      (bytesStarts, 33, "borsh-schema.[4-12:b"),
      (stringsStarts, 34, "borsh-schema.[4-12:t"),
      (bytesEnds, 35, "borsh-schema.[4-12:b"),
      (stringsEnds, 36, "borsh-schema.[4-12:t")
    ] do
    match method.entry with
    | .raw entry =>
        unless entry.tag == tag && entry.paramCount == 2 &&
            entry.paramBorshPlans.size == 2 &&
            entry.paramLeafWidths == #[4, 1, 1, 1, 1, 1, 1, 1, 1,
              4, 1, 1, 1, 1, 1, 1, 1, 1] &&
            entry.paramLeafCounts == #[9, 9] && entry.minDataLen == 9 &&
            entry.maxDataLen == 25 && entry.inferredReturnWidths == #[1] &&
            entry.returnDataLen == 1 && entry.canonical.contains marker do
          throwError s!"wrong bounded comparison Borsh plan: {repr entry}"
    | .generated => throwError "bounded comparison method lost its raw adapter"
    let graph ←
      match method.toCFG with
      | .ok graph => pure graph
      | .error reason => throwError s!"bounded comparison did not reach CFG: {reason}"
    unless graph.blocks.any fun block =>
        match block.terminator with
        | .exit (.returnU64 _) => true
        | _ => false do
      throwError s!"{method.ixName} lost its scalar Bool return"
  for (method, tag, marker) in [
      (bytesFind, 37, "borsh-schema.[4-12:b"),
      (stringsFind, 38, "borsh-schema.[4-12:t")
    ] do
    match method.entry with
    | .raw entry =>
        unless entry.tag == tag && entry.paramCount == 2 &&
            entry.paramBorshPlans.size == 2 &&
            entry.paramLeafWidths == #[4, 1, 1, 1, 1, 1, 1, 1, 1,
              4, 1, 1, 1, 1, 1, 1, 1, 1] &&
            entry.paramLeafCounts == #[9, 9] && entry.minDataLen == 9 &&
            entry.maxDataLen == 25 && entry.inferredReturnWidths.isEmpty &&
            entry.returnBorshPlan == some (.option #[8]) && entry.returnDataLen == 9 &&
            entry.returnScratchBytes == 17 &&
            entry.canonical.contains marker &&
            entry.canonical.contains "borsh-return-schema.option.[8]" do
          throwError s!"wrong bounded first-position Borsh plan: {repr entry}"
    | .generated => throwError "bounded first-position method lost its raw adapter"
    let graph ←
      match method.toCFG with
      | .ok graph => pure graph
      | .error reason => throwError s!"bounded first-position did not reach CFG: {reason}"
    unless graph.blocks.all fun block =>
        match block.terminator with
        | .exit (.returnU64s values) => values.size == 2
        | .exit (.returnU64 _) | .exit (.returnState _) | .exit (.okState _) => false
        | _ => true do
      throwError s!"{method.ixName} lost its complete Option return frame"
  let some echoBoundedU128 := program.methods.find? (·.ixName == "echoBoundedU128")
    | throwError "missing projected wide bounded-vector return method"
  let some echoOptionU128 := program.methods.find? (·.ixName == "echoOptionU128")
    | throwError "missing projected wide Option return method"
  match echoBoundedU128.entry, echoOptionU128.entry with
  | .raw wideArray, .raw wideOption =>
      unless wideArray.tag == 39 &&
          wideArray.returnBorshPlan == some (.boundedArray 2 #[8, 8]) &&
          wideArray.returnDataLen == 36 && wideArray.returnScratchBytes == 44 &&
          wideArray.canonical.contains "borsh-return-schema.array.2.[8,8]" &&
          wideOption.tag == 40 && wideOption.returnBorshPlan == some (.option #[8, 8]) &&
          wideOption.returnDataLen == 17 && wideOption.returnScratchBytes == 25 &&
          wideOption.canonical.contains "borsh-return-schema.option.[8,8]" do
        throwError s!"wrong wide Borsh return plans: {repr wideArray}, {repr wideOption}"
  | _, _ => throwError "wide return method lost its raw adapter"
  for (method, count) in [
      (echoBoundedValues, 5), (echoBoundedBytes, 9),
      (echoBoundedString, 9), (makeBoundedString, 9),
      (echoOptionValue, 2), (echoTaggedValue, 3), (echoPubkey, 4),
      (echoBoundedU128, 5), (echoOptionU128, 3)
    ] do
    let graph ←
      match method.toCFG with
      | .ok graph => pure graph
      | .error reason => throwError s!"bounded return did not reach CFG: {reason}"
    unless graph.blocks.any fun block =>
        match block.terminator with
        | .exit (.returnU64s values) => values.size == count
        | _ => false do
      throwError s!"{method.ixName} lost its fixed return frame"
  let bareWide := { echo128 with ops := #[.returnU64 (.arg 0)] }
  match bareWide.toCFG with
  | .error reason =>
      unless reason.contains "requires a limb projection" do
        throwError s!"wrong bare multi-limb rejection: {reason}"
  | .ok _ => throwError "bare multi-limb raw parameter was accepted"
  unless IR.generatedAccountCount program == 1 do
    throwError "raw account geometry leaked into generated methods"
  let asm ←
    match Emit.emitAsm program with
    | .ok asm => pure asm
    | .error reason => throwError reason
  for marker in #[
      "raw_walk_loop_route", "call packed", "call borshOptions", "call boundedPair",
      "lddw r2, 16", "call borshSingletonPair", "lddw r2, 20", "call enumSmall",
      "call enumWide", "call enumOptional", "call echo128", "call echoBytes12",
      "call aggregate", "jne r1, 29, err_raw_aggregate", "call optionValue",
      "call taggedValue", "call boundedValues", "call boundedBytes", "call boundedString",
      "call echoBoundedValues", "call echoBoundedBytes", "call echoBoundedString",
      "call makeBoundedString", "call echoOptionValue", "call echoTaggedValue",
      "call echoPubkey", "jne r1, 33, err_raw_echoPubkey", "call bytesEqual",
      "call stringsEqual", "call bytesLess", "call stringsLess", "call bytesContains",
      "call stringsContains", "call bytesStartsWith", "call stringsStartsWith",
      "call bytesEndsWith", "call stringsEndsWith", "call bytesFindIndex",
      "call stringsFindIndex", "call echoBoundedU128", "call echoOptionU128",
      "borsh_schema_utf8_loop_stringsEqual_0",
      "borsh_schema_utf8_loop_stringsEqual_9", "borsh_schema_utf8_loop_stringsLess_0",
      "borsh_schema_utf8_loop_stringsLess_9", "borsh_schema_utf8_loop_stringsContains_0",
      "borsh_schema_utf8_loop_stringsContains_9",
      "borsh_schema_utf8_loop_stringsStartsWith_0",
      "borsh_schema_utf8_loop_stringsStartsWith_9",
      "borsh_schema_utf8_loop_stringsEndsWith_0",
      "borsh_schema_utf8_loop_stringsEndsWith_9",
      "borsh_schema_utf8_loop_stringsFindIndex_0",
      "borsh_schema_utf8_loop_stringsFindIndex_9",
      "borsh_return_option_present_bytesFindIndex_",
      "borsh_return_option_present_stringsFindIndex_",
      "borsh_return_invalid_echoBoundedValues_",
      "borsh_return_invalid_echoBoundedBytes_", "borsh_return_invalid_echoBoundedString_",
      "borsh_return_invalid_echoBoundedU128_",
      "borsh_return_option_present_echoOptionU128_",
      "borsh_schema_utf8_loop_echoBoundedString_b0_return_",
      "borsh_return_invalid_makeBoundedString_",
      "borsh_schema_utf8_loop_makeBoundedString_b0_return_",
      "borsh_return_option_present_echoOptionValue_",
      "borsh_return_enum_variant_echoTaggedValue_", "mul64 r2, 2", "mul64 r2, 1",
      "decode recursive target-owned Borsh schema with exact cursor consumption",
      "borsh_schema_none_optionValue_", "borsh_schema_enum_done_taggedValue_",
      "borsh_schema_array_skip_boundedValues_", "borsh_schema_bytes_skip_boundedBytes_",
      "borsh_schema_utf8_loop_boundedString_", "borsh_schema_utf8_cont_boundedString_",
      "jne r7, r9, err_raw_optionValue", "jne r7, r9, err_raw_taggedValue",
      "jne r7, r9, err_raw_boundedValues", "jgt r1, 4, err_raw_boundedValues",
      "jgt r1, 1, err_raw_aggregate", "ldxdw r1, [r8 + 9]", "ldxw r1, [r8 + 19]",
      "ldxh r1, [r8 + 35]", "optional_return_present_enumOptional_",
      "optional_return_invalid_enumOptional_", "jeq r1, 0, raw_route_match_",
      "jeq r1, 1, raw_route_match_", "call sol_set_return_data",
      "authenticate the declared executable program account", "ldxb r1, [r8 + 9]",
      "ldxdw r1, [r8 + 10]", "jlt r2, 5, raw_route_next_", "jgt r2, 21, raw_route_next_",
      "decode a bounded Borsh Option suffix with exact cursor consumption",
      "jne r1, 1, err_raw_borshOptions", "jne r7, r9, err_raw_borshOptions",
      "ja raw_generated_entry", "call initialize"
    ] do
    unless asm.contains marker do
      throwError s!"raw/generated entry assembly is missing {marker}"
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

private def hasTaggedBounds (result : Except String EntryAdapter.MethodEntry)
    (minDataLen maxDataLen localCount : Nat) : Bool :=
  match result with
  | .ok (.raw entry) =>
      entry.minDataLen == minDataLen && entry.maxDataLen == maxDataLen &&
        entry.paramLeafWidths.size == localCount && entry.paramBorshPlans.size == 1
  | _ => false

#guard accepts (EntryAdapter.decode #["svm.raw.v1:7:2:0"] 2 #[1, 8])
#guard accepts (EntryAdapter.decode #["svm.raw.v2:8:4:0:1:8,4,4"] 7 #[1, 1, 8, 1, 4, 1, 4])
#guard accepts (EntryAdapter.decode #["svm.raw.v3:10:2:0:4,8,8"] 2 #[8, 8] 3)
#guard accepts (EntryAdapter.decode #["svm.raw.v4:11:2:0:0:8"] 1 #[1])
#guard accepts (EntryAdapter.decode #["svm.raw.v4:11:2:0:1:8"] 1 #[8])
#guard accepts (EntryAdapter.decode #["svm.raw.v5:11:2:0:2:8"] 2 #[1, 8] 2)
#guard accepts (EntryAdapter.decode #["svm.raw.v1:12:2:0"] 1 #[16] 2
  #[.uint128] #[.uint128])
#guard accepts (EntryAdapter.decode #["svm.raw.v1:13:2:0"] 1 #[12] 2
  #[.fixedBytes 12] #[.fixedBytes 12])
#guard accepts (EntryAdapter.decode #["svm.raw.v1:15:2:0"] 1 #[] 1
  (paramSchemas := #[.unit]))
#guard hasTaggedBounds (EntryAdapter.decode #["svm.raw.v1:15:2:0"] 1 #[] 1
  (paramSchemas := #[.option (.scalar .uint64)])) 2 10 2
#guard hasTaggedBounds (EntryAdapter.decode #["svm.raw.v1:16:2:0"] 1 #[] 1
  (paramSchemas := #[.enumeration "Request" 8 #[
    ("idle", .unit),
    ("one", .scalar .uint64),
    ("pair", .tuple #[.scalar .uint64, .scalar .uint64])
  ]])) 2 18 3
#guard accepts (EntryAdapter.decode #["svm.raw.v1:17:2:0"] 1 #[] 1
  (paramSchemas := #[.record "Nested" #[
    ("enabled", .scalar .boolean),
    ("limit", .option (.scalar .uint32))
  ]]))
#guard hasTaggedBounds (EntryAdapter.decode #["svm.raw.v1:17:2:0"] 1 #[] 1
  (paramSchemas := #[.boundedArray 4 (.scalar .uint64)])) 5 37 5
#guard hasTaggedBounds (EntryAdapter.decode #["svm.raw.v1:18:2:0"] 1 #[] 1
  (paramSchemas := #[.boundedBytes 8])) 5 13 9
#guard hasTaggedBounds (EntryAdapter.decode #["svm.raw.v1:19:2:0"] 1 #[] 1
  (paramSchemas := #[.boundedString 8])) 5 13 9
#guard accepts (EntryAdapter.decode #["svm.raw.v1:20:2:0"] 1 #[] 5
  (paramSchemas := #[.boundedArray 4 (.scalar .uint16)])
  (retSchema := .boundedArray 4 (.scalar .uint16)))
#guard accepts (EntryAdapter.decode #["svm.raw.v1:21:2:0"] 1 #[] 9
  (paramSchemas := #[.boundedBytes 8]) (retSchema := .boundedBytes 8))
#guard accepts (EntryAdapter.decode #["svm.raw.v1:22:2:0"] 1 #[] 9
  (paramSchemas := #[.boundedString 8]) (retSchema := .boundedString 8))
#guard accepts (EntryAdapter.decode #["svm.raw.v1:24:2:0"] 1 #[] 2
  (paramSchemas := #[.option (.scalar .uint64)])
  (retSchema := .option (.scalar .uint64)))
#guard accepts (EntryAdapter.decode #["svm.raw.v1:25:2:0"] 1 #[] 3
  (paramSchemas := #[.enumeration "Request" 8 #[
    ("idle", .unit),
    ("one", .scalar .uint64),
    ("pair", .tuple #[.scalar .uint64, .scalar .uint64])
  ]])
  (retSchema := .enumeration "Request" 8 #[
    ("idle", .unit),
    ("one", .scalar .uint64),
    ("pair", .tuple #[.scalar .uint64, .scalar .uint64])
  ]))
#guard !accepts (EntryAdapter.decode #["svm.raw.v1:20:2:0"] 1 #[] 4
  (paramSchemas := #[.boundedArray 4 (.scalar .uint16)])
  (retSchema := .boundedArray 4 (.scalar .uint16)))
#guard accepts (EntryAdapter.decode #["svm.raw.v1:27:2:0"] 1 #[] 5
  (paramSchemas := #[.boundedArray 2 (.scalar .uint128)])
  (retSchema := .boundedArray 2 (.scalar .uint128)))
#guard accepts (EntryAdapter.decode #["svm.raw.v1:28:2:0"] 1 #[] 5
  (paramSchemas := #[.boundedArray 2 (.tuple #[.scalar .uint32, .scalar .uint32])])
  (retSchema := .boundedArray 2 (.tuple #[.scalar .uint32, .scalar .uint32])))
#guard accepts (EntryAdapter.decode #["svm.raw.v1:29:2:0"] 1 #[] 3
  (paramSchemas := #[.option (.scalar .uint128)])
  (retSchema := .option (.scalar .uint128)))
#guard !accepts (EntryAdapter.decode #["svm.raw.v1:20:2:0"] 1 #[] 5
  (paramSchemas := #[.boundedArray 4 (.scalar .uint16)])
  (retSchema := .boundedArray 4 (.tuple #[.scalar .uint16, .scalar .uint16])))
#guard !accepts (EntryAdapter.decode #["svm.raw.v1:28:2:0"] 1 #[] 5
  (paramSchemas := #[.boundedArray 2 (.tuple #[.scalar .uint32, .scalar .uint32])])
  (retSchema := .record "Wrap" #[
    ("items", .boundedArray 2 (.tuple #[.scalar .uint32, .scalar .uint32]))
  ]))
#guard !accepts (EntryAdapter.decode #["svm.raw.v1:27:2:0"] 1 #[] 5
  (paramSchemas := #[.boundedArray 2 (.scalar .uint128)])
  (retSchema := .boundedArray 2 (.option (.scalar .uint64))))
#guard !accepts (EntryAdapter.decode #["svm.raw.v1:17:2:0"] 1 #[] 1
  (paramSchemas := #[.boundedArray 128 (.scalar .uint64)]))
#guard !accepts (EntryAdapter.decode #["svm.raw.v1:24:2:0"] 0 #[] 1
  (retSchema := .option (.scalar .uint64)))
#guard !accepts (EntryAdapter.decode #["svm.raw.v1:15:2:0"] 1 #[] 1
  (paramSchemas := #[.unit])
  (retSchema := .record "Pair" #[
    ("left", .scalar .uint64),
    ("right", .scalar .uint64)
  ]))
#guard !accepts (EntryAdapter.decode #["svm.raw.v1:13:2:0"] 1 #[20] 3
  #[.address20] #[.address20])
#guard !accepts (EntryAdapter.decode #["svm.raw.v1:256:2:0"] 2 #[1, 8])
#guard !accepts (EntryAdapter.decode #["svm.raw.v1:7:2:2"] 2 #[1, 8])
#guard !accepts (EntryAdapter.decode #["svm.raw.v1:7:2:0"] 2 #[1, 3])
#guard !accepts (EntryAdapter.decode #["svm.raw.v2:8:4:0:1:8,4,4"] 7 #[1, 1, 8, 1, 8, 1, 4])
#guard !accepts (EntryAdapter.decode #["svm.raw.v2:8:4:0:1:8,3,4"] 7 #[1, 1, 8, 1, 4, 1, 4])
#guard !accepts (EntryAdapter.decode #["svm.raw.v3:10:2:0:4,8"] 2 #[8, 8] 3)
#guard !accepts (EntryAdapter.decode #["svm.raw.v3:10:2:0:4,3,8"] 2 #[8, 8] 3)
#guard !accepts (EntryAdapter.decode #["svm.raw.v4:11:2:0:256:8"] 1 #[1])
#guard !accepts (EntryAdapter.decode #["svm.raw.v5:11:2:0:2:8"] 2 #[1, 8] 1)
#guard !accepts (EntryAdapter.decode #["svm.raw.v5:11:2:0:2:3"] 2 #[1, 8] 2)
#guard accepts (EntryAdapter.validateUniqueTags #[
  .raw { tag := 11, accountCount := 2, programAccount := 0, variant := some 0, paramWidths := #[1] },
  .raw { tag := 11, accountCount := 2, programAccount := 0, variant := some 1, paramWidths := #[8] },
  .raw { tag := 11, accountCount := 2, programAccount := 0, variant := some 2,
         paramWidths := #[1, 8], returnWidths := #[8], optionalReturnData := true }
])
#guard !accepts (EntryAdapter.validateUniqueTags #[
  .raw { tag := 7, accountCount := 2, programAccount := 0, paramWidths := #[1] },
  .raw { tag := 7, accountCount := 2, programAccount := 0, paramWidths := #[8] }
])

end Tests.EntryAdapterSpec
