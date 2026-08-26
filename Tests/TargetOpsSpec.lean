import ProofForge.Svm.Ops
import ProofForge.Svm.AccountStorage
import ProofForge.Svm.AccountStorage.Emit
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

private def validByteSwap64Value : ProofForge.Svm.Ops.Val :=
  ProofForge.Svm.Ops.byteSwap64 (.arg 0)

private def malformedByteSwap64Value : ProofForge.Svm.Ops.Val :=
  .ext .byteSwap64 #[]

#guard validByteSwap64Value.wellFormed ProofForge.Svm.Ops.ValKind.arity
#guard !malformedByteSwap64Value.wellFormed ProofForge.Svm.Ops.ValKind.arity

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

private def validOneBasedDataWordOp : ProofForge.Svm.Ops.Op :=
  .returnU64 (ProofForge.Svm.Ops.accDataWordAtOneBased 1 114 8 512 (.arg 0))

#guard validIndexedDataWordOp.wellFormed
#guard !invalidIndexedDataWordOp.wellFormed
#guard validOneBasedDataWordOp.wellFormed

private def validIndexedDataWordQuery : ProofForge.Svm.AccountStorage.Query :=
  .readWordZeroBased 1 114 8 512

private def validOneBasedDataWordQuery : ProofForge.Svm.AccountStorage.Query :=
  .readWordOneBased 1 114 8 512

private def invalidIndexedDataWordQuery : ProofForge.Svm.AccountStorage.Query :=
  .readWordZeroBased 1 114 2305843009213693951 1

#guard validIndexedDataWordQuery.wellFormed
#guard validOneBasedDataWordQuery.wellFormed
#guard !invalidIndexedDataWordQuery.wellFormed
#guard validIndexedDataWordQuery.arity == 1
#guard validIndexedDataWordQuery.effects.reads == #[1]
#guard validIndexedDataWordQuery.effects.writes.isEmpty
#guard validIndexedDataWordQuery.canonical
    (fun value : ProofForge.Svm.Ops.Val => match value with | .arg i => s!"a{i}" | _ => "v")
    (#[.arg 0] : Array ProofForge.Svm.Ops.Val) == "dwi.1.114.8.512(a0)"
#guard validOneBasedDataWordQuery.canonical
    (fun value : ProofForge.Svm.Ops.Val => match value with | .arg i => s!"a{i}" | _ => "v")
    (#[.arg 0] : Array ProofForge.Svm.Ops.Val) == "dwi1.1.114.8.512(a0)"

private def validParentPathOp : ProofForge.Svm.Ops.Op :=
  .returnU64 (ProofForge.Svm.Ops.accDataParentPathValid
    1 114 115 8 4096 32 (.arg 0) (.arg 1) (.arg 2))

private def malformedParentPathOp : ProofForge.Svm.Ops.Op :=
  .returnU64 (.ext (.accountStorage (.parentPathValidOneBased 1 114 115 8 4096 32))
    #[.arg 0, .arg 1])

private def unboundedParentPathOp : ProofForge.Svm.Ops.Op :=
  .returnU64 (ProofForge.Svm.Ops.accDataParentPathValid
    1 114 115 8 4096 65 (.arg 0) (.arg 1) (.arg 2))

#guard validParentPathOp.wellFormed
#guard !malformedParentPathOp.wellFormed
#guard !unboundedParentPathOp.wellFormed

private def validParentPathQuery : ProofForge.Svm.AccountStorage.Query :=
  .parentPathValidOneBased 1 114 115 8 4096 32

#guard validParentPathQuery.wellFormed
#guard validParentPathQuery.arity == 3
#guard validParentPathQuery.effects.reads == #[1]
#guard validParentPathQuery.effects.writes.isEmpty
#guard validParentPathQuery.canonical
    (fun value : ProofForge.Svm.Ops.Val => match value with | .arg i => s!"a{i}" | _ => "v")
    (#[.arg 0, .arg 1, .arg 2] : Array ProofForge.Svm.Ops.Val) ==
  "dpp.1.114.115.8.4096.32(a0,a1,a2)"

private def validRbTreeOp : ProofForge.Svm.Ops.Op :=
  .returnU64 (ProofForge.Svm.Ops.accDataRbTreeValid
    1 114 115 116 117 8 4096 true (.arg 0) (.arg 1) (.arg 2) (.arg 3))

private def malformedRbTreeOp : ProofForge.Svm.Ops.Op :=
  .returnU64 (.ext (.accountStorage (.fifoRbTreeValidOneBased
    1 114 115 116 117 8 4096 true)) #[.arg 0, .arg 1, .arg 2])

private def oversizedRbTreeOp : ProofForge.Svm.Ops.Op :=
  .returnU64 (ProofForge.Svm.Ops.accDataRbTreeValid
    1 114 115 116 117 8 4097 true (.arg 0) (.arg 1) (.arg 2) (.arg 3))

#guard validRbTreeOp.wellFormed
#guard !malformedRbTreeOp.wellFormed
#guard !oversizedRbTreeOp.wellFormed

private def validRbTreeQuery : ProofForge.Svm.AccountStorage.Query :=
  .fifoRbTreeValidOneBased 1 114 115 116 117 8 4096 true

#guard validRbTreeQuery.wellFormed
#guard validRbTreeQuery.arity == 4
#guard validRbTreeQuery.effects.reads == #[1]
#guard validRbTreeQuery.effects.writes.isEmpty
#guard validRbTreeQuery.canonical
    (fun value : ProofForge.Svm.Ops.Val => match value with | .arg i => s!"a{i}" | _ => "v")
    (#[.arg 0, .arg 1, .arg 2, .arg 3] : Array ProofForge.Svm.Ops.Val) ==
  "drb.1.114.115.116.117.8.4096.true(a0,a1,a2,a3)"

private def validRbTreeKey4Op : ProofForge.Svm.Ops.Op :=
  .returnU64 (ProofForge.Svm.Ops.accDataRbTreeKey4Valid
    1 65658 65659 65660 18 8321 (.arg 0) (.arg 1) (.arg 2) (.arg 3))

private def malformedRbTreeKey4Op : ProofForge.Svm.Ops.Op :=
  .returnU64 (.ext (.accountStorage (.key4RbTreeValidOneBased
    1 65658 65659 65660 18 8321)) #[.arg 0, .arg 1, .arg 2])

private def oversizedRbTreeKey4Op : ProofForge.Svm.Ops.Op :=
  .returnU64 (ProofForge.Svm.Ops.accDataRbTreeKey4Valid
    1 65658 65659 65660 18 8322 (.arg 0) (.arg 1) (.arg 2) (.arg 3))

#guard ProofForge.Svm.Ops.rbTreeKey4WordsInRange 65658 65659 65660 18 8321
#guard !ProofForge.Svm.Ops.rbTreeKey4WordsInRange 65658 65659 65660 18 8322
#guard validRbTreeKey4Op.wellFormed
#guard !malformedRbTreeKey4Op.wellFormed
#guard !oversizedRbTreeKey4Op.wellFormed

private def validRbTreeKey4Query : ProofForge.Svm.AccountStorage.Query :=
  .key4RbTreeValidOneBased 1 65658 65659 65660 18 8321

#guard validRbTreeKey4Query.wellFormed
#guard validRbTreeKey4Query.arity == 4
#guard validRbTreeKey4Query.effects.reads == #[1]
#guard validRbTreeKey4Query.effects.writes.isEmpty
#guard validRbTreeKey4Query.canonical
    (fun value : ProofForge.Svm.Ops.Val => match value with | .arg i => s!"a{i}" | _ => "v")
    (#[.arg 0, .arg 1, .arg 2, .arg 3] : Array ProofForge.Svm.Ops.Val) ==
  "drb4.1.65658.65659.65660.18.8321(a0,a1,a2,a3)"

private def validFifoFindQuery : ProofForge.Svm.AccountStorage.Query :=
  .fifoFindOneBased 1 110 114 115 116 117 8 4096 true

private def validKey4FindQuery : ProofForge.Svm.AccountStorage.Query :=
  .key4FindOneBased 1 8310 8314 8315 8316 18 128

private def stateKey4FindQuery : ProofForge.Svm.AccountStorage.Query :=
  .key4FindOneBased 0 1 4 5 6 10 4

private def invalidFindRootQuery : ProofForge.Svm.AccountStorage.Query :=
  .key4FindOneBased 1 8314 8314 8315 8316 18 128

private def unboundedFifoFindQuery : ProofForge.Svm.AccountStorage.Query :=
  .fifoFindOneBased 1 110 114 115 116 117 8 4097 true

private def writableKey4FindQuery : ProofForge.Svm.AccountStorage.Query :=
  .key4Find 8310 (.oneBased 1 8314 8315 8316 18 128
    { writable := true, currentProgramOwned := true })

#guard validFifoFindQuery.wellFormed
#guard validKey4FindQuery.wellFormed
#guard stateKey4FindQuery.wellFormed
#guard !invalidFindRootQuery.wellFormed
#guard !unboundedFifoFindQuery.wellFormed
#guard !writableKey4FindQuery.wellFormed
#guard validFifoFindQuery.arity == 2
#guard validKey4FindQuery.arity == 4
#guard validFifoFindQuery.effects.reads == #[1]
#guard validFifoFindQuery.effects.writes.isEmpty
#guard validKey4FindQuery.effects.reads == #[1]
#guard validKey4FindQuery.effects.writes.isEmpty
#guard validFifoFindQuery.canonical
    (fun value : ProofForge.Svm.Ops.Val => match value with | .arg i => s!"a{i}" | _ => "v")
    (#[.arg 0, .arg 1] : Array ProofForge.Svm.Ops.Val) ==
  "rbof.1.110.114.116.117.8.4096.true(a0,a1)"
#guard validKey4FindQuery.canonical
    (fun value : ProofForge.Svm.Ops.Val => match value with | .arg i => s!"a{i}" | _ => "v")
    (#[.arg 0, .arg 1, .arg 2, .arg 3] : Array ProofForge.Svm.Ops.Val) ==
  "rb4f.1.8310.8314.8316.18.128(a0,a1,a2,a3)"

private def findEmitContext : ProofForge.Svm.AccountStorage.Emit.Context :=
  { loadValue := fun value stackOff _ _ =>
      match value with
      | .arg i => .ok s!"  lddw r1, {i}\n  stxdw [r10 - {stackOff}], r1\n"
      | _ => .error "unexpected test value"
    loadOwnerIsSelf := fun _ _ _ => ""
    headerStack := fun account => 512 + 8 * account }

private def key4FindAssembly :=
  ProofForge.Svm.AccountStorage.Emit.emitQuery findEmitContext validKey4FindQuery
    #[.arg 0, .arg 1, .arg 2, .arg 3] 160 0 "key4_find_test"

private def fifoFindAssembly :=
  ProofForge.Svm.AccountStorage.Emit.emitQuery findEmitContext validFifoFindQuery
    #[.arg 0, .arg 1] 160 0 "fifo_find_test"

private def stateFindAssembly :=
  ProofForge.Svm.AccountStorage.Emit.emitQuery findEmitContext stateKey4FindQuery
    #[.arg 0, .arg 1, .arg 2, .arg 3] 160 0 "state_find_test"

#guard
  match key4FindAssembly with
  | .ok assembly =>
      assembly.contains "bounded one-based acc1 RB find root=8310 links=8314 stride=18 capacity=128" &&
        assembly.contains "be64 r1" && assembly.contains "rb_find_found_" &&
        assembly.contains "rb_find_missing_" && assembly.contains "lddw r3, 64"
  | .error _ => false

#guard
  match fifoFindAssembly with
  | .ok assembly =>
      assembly.contains "bounded one-based acc1 RB find root=110 links=114 stride=8 capacity=4096" &&
        assembly.contains "jgt r1, r3, rb_find_before_" &&
        assembly.contains "jlt r1, r3, rb_find_after_" && !assembly.contains "be64 r1"
  | .error _ => false

#guard
  match stateFindAssembly with
  | .ok assembly =>
      assembly.contains "ldxdw r1, [r6 + ACC0_DATA_LEN]" &&
        assembly.contains "add64 r5, ACC0_DATA" &&
        assembly.contains "bounded one-based acc0 RB find root=1 links=4 stride=10 capacity=4"
  | .error _ => false

private def validAccDataWordSetAtOp : ProofForge.Svm.Ops.Op :=
  .ext (.accountStorage (.writeWordZeroBased 1 8314 18 128 (.arg 0) (.arg 1)))

private def stateAccDataWordSetAtOp : ProofForge.Svm.Ops.Op :=
  .ext (.accountStorage (.writeWordZeroBased 0 1 1 1 (.arg 0) (.arg 1)))

private def unboundedAccDataWordSetAtOp : ProofForge.Svm.Ops.Op :=
  .ext (.accountStorage (.writeWordZeroBased 1 8314 0 128 (.arg 0) (.arg 1)))

#guard validAccDataWordSetAtOp.wellFormed
#guard !stateAccDataWordSetAtOp.wellFormed
#guard !unboundedAccDataWordSetAtOp.wellFormed

private def oneBasedTraderLinks : ProofForge.Svm.AccountStorage.Field :=
  { region :=
      { account := 1
        baseWord := 8314
        strideWords := 18
        capacity := 128
        indexBase := .one
        access := { writable := true, currentProgramOwned := true } } }

private def oneBasedTraderWrite :
    ProofForge.Svm.AccountStorage.Call ProofForge.Svm.Ops.Val :=
  .writeWordOneBased 1 8314 18 128 (.arg 0) (.arg 1)

#guard oneBasedTraderLinks.wellFormed
#guard oneBasedTraderWrite.wellFormed
  (·.wellFormed ProofForge.Svm.Ops.ValKind.arity)
#guard oneBasedTraderWrite.effects.reads == #[1]
#guard oneBasedTraderWrite.effects.writes == #[1]
#guard oneBasedTraderWrite.canonical (fun | .arg i => s!"a{i}" | _ => "v") ==
  "dws1.1.8314.18.128(a0,a1)"
#guard
  match ProofForge.Svm.IR.ofSourceOps #[validAccDataWordSetAtOp] with
  | .ok #[.accountStorage (.writeWord field (.arg 0) (.arg 1))] =>
      field.region.account == 1 && field.firstWord == 8314 &&
        field.region.strideWords == 18 && field.region.capacity == 128 &&
        field.region.indexBase == .zero
  | _ => false
#guard
  match ProofForge.Svm.IR.ofSourceOps
      #[.ext (.accountStorage (.writeWordOneBased 1 8314 18 128 (.arg 0) (.arg 1)))] with
  | .ok #[.accountStorage (.writeWord field (.arg 0) (.arg 1))] =>
      field.region.account == 1 && field.firstWord == 8314 &&
        field.region.strideWords == 18 && field.region.capacity == 128 &&
        field.region.indexBase == .one
  | _ => false

private def validKey4MapInsert :
    ProofForge.Svm.AccountStorage.Call ProofForge.Svm.Ops.Val :=
  .rbMapInsertKey4OneBased 1 8310 8314 8315 8316 18 128
    (.arg 0) (.arg 1) (.arg 2) (.arg 3)

private def malformedKey4MapInsert :
    ProofForge.Svm.AccountStorage.Call ProofForge.Svm.Ops.Val :=
  .rbMapInsert (.key4OneBased 1 8310 8314 8315 8316 18 128) #[.arg 0] #[] .reject

private def validFifoMapInsert :
    ProofForge.Svm.AccountStorage.Call ProofForge.Svm.Ops.Val :=
  .rbMapInsertFifoOneBased 1 110 114 115 116 117 8 512 true
    (.arg 0) (.arg 1) (.arg 2) (.arg 3) (.lit 0) (.lit 0)

private def malformedFifoMapInsert :
    ProofForge.Svm.AccountStorage.Call ProofForge.Svm.Ops.Val :=
  .rbMapInsert (.fifoOneBased 1 110 114 115 116 118 8 512 true)
    #[.arg 0, .arg 1] #[.arg 2, .arg 3, .lit 0, .lit 0] .replace

#guard validKey4MapInsert.wellFormed (·.wellFormed ProofForge.Svm.Ops.ValKind.arity)
#guard !malformedKey4MapInsert.wellFormed (·.wellFormed ProofForge.Svm.Ops.ValKind.arity)
#guard validFifoMapInsert.wellFormed (·.wellFormed ProofForge.Svm.Ops.ValKind.arity)
#guard !malformedFifoMapInsert.wellFormed (·.wellFormed ProofForge.Svm.Ops.ValKind.arity)
#guard validKey4MapInsert.effects.reads == #[1]
#guard validKey4MapInsert.effects.writes == #[1]
#guard validKey4MapInsert.canonical (fun | .arg i => s!"a{i}" | _ => "v") ==
  "rb4i.1.8310.8314.8315.8316.18.128(a0,a1,a2,a3)"
#guard validFifoMapInsert.canonical (fun | .arg i => s!"a{i}" | .lit n => s!"{n}" | _ => "v") ==
  "rboi.1.110.114.115.116.117.8.512.true(a0,a1,a2,a3,0,0)"

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

#guard (ProofForge.Svm.Ops.PdaSeed.accData 1 48 32).wellFormed
#guard !(ProofForge.Svm.Ops.PdaSeed.accData 1 48 0).wellFormed
#guard !(ProofForge.Svm.Ops.PdaSeed.accData 1 48 33).wellFormed
#guard !(ProofForge.Svm.Ops.PdaSeed.accData 63 48 32).wellFormed

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

private def seedAccDataSizedProgram : ProofForge.Svm.IR.Program :=
  { name := "SeedAccDataSized"
    schema := {}
    slots := #[]
    methods := #[
      { kind := .increment, name := "SeedAccDataSized.call", ixName := "call", paramCount := 0
        ops := #[.invoke 1 #[] #[] #[.accData 5 48 32] (some (.lit 1))] }
    ] }

#guard ProofForge.Svm.IR.cpiAccountCount seedAccDataSizedProgram == 7

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
