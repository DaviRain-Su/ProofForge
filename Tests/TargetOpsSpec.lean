import ProofForge.Svm.Ops
import ProofForge.Svm.IR
import ProofForge.Evm.Ops
import ProofForge.Evm.IR
import ProofForge.Core.Target
import ProofForge.Extract.LegacyAdapter
import ProofForge.Extract.LegacyGolden

namespace Tests.TargetOpsSpec

private def validSvmValue : ProofForge.Svm.Ops.Val :=
  ProofForge.Svm.Ops.checkPda "vault" (ProofForge.Svm.Ops.findPda "vault")

private def invalidSvmValue : ProofForge.Svm.Ops.Val :=
  .ext (.checkPda "vault") #[]

#guard validSvmValue.wellFormed ProofForge.Svm.Ops.ValKind.arity
#guard !invalidSvmValue.wellFormed ProofForge.Svm.Ops.ValKind.arity

private def validSvmOp : ProofForge.Svm.Ops.Op :=
  .ext (.invoke 2
    #[{ acc := 0, signer := true, writable := true }]
    #[.u64le validSvmValue]
    #[.ascii "vault"]
    (some validSvmValue))

#guard validSvmOp.wellFormed
#guard ProofForge.Svm.Ops.cpiAccInRange 62
#guard !ProofForge.Svm.Ops.cpiAccInRange 63
#guard ProofForge.Svm.Ops.dataWordInRange 4
#guard !ProofForge.Svm.Ops.dataWordInRange 2305843009213693951
#guard ProofForge.Svm.Ops.indexedDataWordsInRange 114 8 4096
#guard !ProofForge.Svm.Ops.indexedDataWordsInRange 114 0 4096
#guard !ProofForge.Svm.Ops.indexedDataWordsInRange 114 8 0
#guard !ProofForge.Svm.Ops.indexedDataWordsInRange 0 2305843009213693951 1
#guard ProofForge.Svm.Ops.parentPathWordsInRange 114 115 8 4096 32
#guard !ProofForge.Svm.Ops.parentPathWordsInRange 114 115 8 4096 0
#guard !ProofForge.Svm.Ops.parentPathWordsInRange 114 115 8 4096 65

private def invalidDataWordOp : ProofForge.Svm.Ops.Op :=
  .returnU64 (ProofForge.Svm.Ops.accDataWord 1 2305843009213693951)

#guard !invalidDataWordOp.wellFormed

private def validIndexedDataWordOp : ProofForge.Svm.Ops.Op :=
  .returnU64 (ProofForge.Svm.Ops.accDataWordAt 1 114 8 512 (.arg 0))

private def invalidIndexedDataWordOp : ProofForge.Svm.Ops.Op :=
  .returnU64 (ProofForge.Svm.Ops.accDataWordAt 1 114 0 512 (.arg 0))

#guard validIndexedDataWordOp.wellFormed
#guard !invalidIndexedDataWordOp.wellFormed

private def validParentPathOp : ProofForge.Svm.Ops.Op :=
  .returnU64 (ProofForge.Svm.Ops.accDataParentPathValid
    1 114 115 8 4096 32 (.arg 0) (.arg 1) (.arg 2))

private def malformedParentPathOp : ProofForge.Svm.Ops.Op :=
  .returnU64 (.ext (.accDataParentPathValid 1 114 115 8 4096 32) #[.arg 0, .arg 1])

private def unboundedParentPathOp : ProofForge.Svm.Ops.Op :=
  .returnU64 (ProofForge.Svm.Ops.accDataParentPathValid
    1 114 115 8 4096 65 (.arg 0) (.arg 1) (.arg 2))

#guard validParentPathOp.wellFormed
#guard !malformedParentPathOp.wellFormed
#guard !unboundedParentPathOp.wellFormed

private def invalidCpiAccountOp : ProofForge.Svm.Ops.Op :=
  .ext (.invoke 63 #[] #[] #[] none)

#guard !invalidCpiAccountOp.wellFormed

private def invalidLongSeedOp : ProofForge.Svm.Ops.Op :=
  .ext (.invoke 1 #[] #[] #[.ascii "123456789012345678901234567890123"] (some (.lit 1)))

#guard !invalidLongSeedOp.wellFormed

private def invalidSeedCountOp : ProofForge.Svm.Ops.Op :=
  .ext (.invoke 1 #[] #[]
    (Array.replicate 16 (.stateKey : ProofForge.Svm.Ops.PdaSeed)) (some (.lit 1)))

#guard !invalidSeedCountOp.wellFormed

private def accKeySizedProgram : ProofForge.Svm.IR.Program :=
  { name := "AccKeySized"
    schema := {}
    slots := #[]
    methods := #[
      { kind := .increment, name := "AccKeySized.call", ixName := "call", paramCount := 0
        ops := #[.invoke 1 #[] #[.accKey 5] #[] none] }
    ] }

#guard ProofForge.Svm.IR.cpiAccountCount accKeySizedProgram == 7

private def seedAccKeySizedProgram : ProofForge.Svm.IR.Program :=
  { name := "SeedAccKeySized"
    schema := {}
    slots := #[]
    methods := #[
      { kind := .increment, name := "SeedAccKeySized.call", ixName := "call", paramCount := 0
        ops := #[.invoke 1 #[] #[] #[.accKey 5] (some (.lit 1))] }
    ] }

#guard ProofForge.Svm.IR.cpiAccountCount seedAccKeySizedProgram == 7

private def validEvmValue : ProofForge.Evm.Ops.Val :=
  ProofForge.Evm.Ops.mapGetU64 ProofForge.Evm.Ops.self (.lit 7)

private def invalidEvmValue : ProofForge.Evm.Ops.Val :=
  .ext .mapGetU64 #[ProofForge.Evm.Ops.self]

#guard validEvmValue.wellFormed ProofForge.Evm.Ops.ValKind.arity
#guard !invalidEvmValue.wellFormed ProofForge.Evm.Ops.ValKind.arity

private def validEvmOp : ProofForge.Evm.Ops.Op :=
  .ext (.sendEth (.lit 1) (.lit 2) (.lit 3) validEvmValue)

#guard validEvmOp.wellFormed

#guard
  let source := ProofForge.Extract.IR.ofLegacyOps
    #[.returnU64 ProofForge.Ops.Val.clockSlot]
  match ProofForge.Svm.IR.projectExtractedOps source,
      ProofForge.Evm.IR.projectExtractedOps source with
  | .ok svm, .error _ => svm.all ProofForge.Svm.Ops.Op.wellFormed
  | _, _ => false

#guard
  let source := ProofForge.Extract.IR.ofLegacyOps
    #[.evmDeposit ProofForge.Ops.Val.evmCallValue]
  match ProofForge.Svm.IR.projectExtractedOps source,
      ProofForge.Evm.IR.projectExtractedOps source with
  | .error _, .ok evm => evm.all ProofForge.Evm.Ops.Op.wellFormed
  | _, _ => false

/-- A synthetic future backend with no accepted source extensions. -/
private inductive CoreOnlyValKind where
  | reserved
  deriving BEq

private inductive CoreOnlyOpExt (V : Type) where
  | reserved

private def coreOnlyCfgDialect :
    ProofForge.Core.CFG.Dialect CoreOnlyValKind CoreOnlyOpExt where
  mapValues := fun _ payload => match payload with | .reserved => .reserved
  values := fun payload => match payload with | .reserved => #[]
  payloadEq := fun left right =>
    match left, right with
    | .reserved, .reserved => true

private def coreOnlyOpWellFormed :
    ProofForge.Core.Ops.Op CoreOnlyValKind CoreOnlyOpExt → Bool :=
  ProofForge.Core.Ops.Op.wellFormed (fun _ => 0) (fun _ => false)

private def coreOnlyRegistration :
    ProofForge.Core.Target.Registration
      ProofForge.Extract.IR.ValKind ProofForge.Extract.IR.OpExt
      CoreOnlyValKind CoreOnlyOpExt where
  name := "CoreOnly"
  projectValExt := fun _ => throw "core-only target rejects source value extensions"
  projectOpExt := fun _ _ => throw "core-only target rejects source effect extensions"
  valArity := fun _ => 0
  opWellFormed := coreOnlyOpWellFormed
  cfgDialect := coreOnlyCfgDialect

private def coreOnlySource : ProofForge.Extract.IR.Program :=
  { name := "CoreOnly"
    slots := #[]
    schema := {}
    methods := #[{
      kind := .get
      name := "CoreOnly.choose"
      ixName := "choose"
      paramCount := 1
      ops := #[
        .letLocal 0 (.addU64 (.arg 0) (.lit 1)),
        .ite .ne (.local 0) (.lit 0)
          #[.returnU64 (.local 0)] #[.returnU64 (.lit 0)]
      ]
    }] }

#guard
  match ProofForge.Core.Target.projectProgram coreOnlyRegistration coreOnlySource with
  | .ok program =>
      program.methods.size == 1 &&
        match program.methods[0]!.ops with
        | #[.letLocal 0 (.addU64 (.arg 0) (.lit 1)),
            .ite .ne (.local 0) (.lit 0)
              #[.returnU64 (.local 0)] #[.returnU64 (.lit 0)]] => true
        | _ => false
  | .error _ => false

#guard
  let source : ProofForge.Extract.IR.Program :=
    { coreOnlySource with methods := #[{
        kind := .get
        name := "CoreOnly.foreign"
        ixName := "foreign"
        ops := #[.returnU64 (.ext (.svm .clockSlot) #[])]
      }] }
  match ProofForge.Core.Target.projectProgram coreOnlyRegistration source with
  | .error _ => true
  | .ok _ => false

private def legacyOpsRoundTrip (ops : Array ProofForge.Ops.Op) : Bool :=
  let extensible := ProofForge.Extract.IR.ofLegacyOps ops
  extensible.all ProofForge.Extract.IR.Op.wellFormed &&
    match ProofForge.Extract.IR.toLegacyOps extensible with
    | .ok restored => restored == ops
    | .error _ => false

#guard ProofForge.Golden.programs.all fun program =>
  program.methods.all fun method => legacyOpsRoundTrip method.ops

#guard ProofForge.Golden.programs.all fun program =>
  match ProofForge.Extract.IR.ofLegacyProgram program >>= ProofForge.Extract.IR.toLegacyProgram with
  | .ok restored => restored == program
  | .error _ => false

private def coreSchema : ProofForge.Core.Schema :=
  { rootType := "CoreCounter.State"
    leaves := #[{
      place := { steps := #[.field "CoreCounter.State" 0 "value"] }
      name := "value"
      ty := .uint 64
    }] }

private def coreProgram : ProofForge.Extract.IR.Program :=
  let schema := coreSchema
  { name := "CoreCounter"
    slots := ProofForge.Core.IR.slotsOfSchema schema
    schema
    methods := #[
      { kind := .init, name := "init", ixName := "initialize" },
      { kind := .increment, name := "tick", ixName := "tick" },
      { kind := .get, name := "get", ixName := "get" }
    ] }

#guard ProofForge.Core.IR.schemaMatchesSlots coreProgram
#guard ProofForge.Core.IR.isProgramShape coreProgram

private def genericEvaluation : Except String ProofForge.Extract.IR.Evaluation :=
  let slot : ProofForge.Extract.IR.Val := .ext (.svm .clockSlot) #[]
  let ops : Array ProofForge.Extract.IR.Op :=
    #[.storeField "value" slot, .okState slot]
  ProofForge.Core.evaluate coreSchema ops

#guard
  match genericEvaluation with
  | .ok evaluation =>
      evaluation.explicit && evaluation.events.size == 2 &&
        evaluation.commits.size == 1 && evaluation.commits[0]!.writes.isEmpty
  | .error _ => false

end Tests.TargetOpsSpec
