import ProofForge.Svm.Ops
import ProofForge.Svm.AccountStorage
import ProofForge.Svm.AccountStorage.Emit
import ProofForge.Svm.BatchRecorder.Emit
import ProofForge.Svm.Component.Emit
import ProofForge.Svm.Heap
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

private def validReadComponentQuery : ProofForge.Svm.Component.Query :=
  .accountStorage validOneBasedDataWordQuery

private def invalidIndexedDataWordQuery : ProofForge.Svm.AccountStorage.Query :=
  .readWordZeroBased 1 114 2305843009213693951 1

#guard validIndexedDataWordQuery.wellFormed
#guard validOneBasedDataWordQuery.wellFormed
#guard !invalidIndexedDataWordQuery.wellFormed
#guard validIndexedDataWordQuery.arity == 1
#guard validIndexedDataWordQuery.effects.reads == #[1]
#guard validIndexedDataWordQuery.effects.writes.isEmpty
#guard validReadComponentQuery.arity == validOneBasedDataWordQuery.arity
#guard validReadComponentQuery.effects == validOneBasedDataWordQuery.effects
#guard validReadComponentQuery.wellFormed
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
  .returnU64 (.ext (.component (.accountStorage
    (.parentPathValidOneBased 1 114 115 8 4096 32)))
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
  .returnU64 (.ext (.component (.accountStorage (.fifoRbTreeValidOneBased
    1 114 115 116 117 8 4096 true))) #[.arg 0, .arg 1, .arg 2])

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
  .returnU64 (.ext (.component (.accountStorage (.key4RbTreeValidOneBased
    1 65658 65659 65660 18 8321))) #[.arg 0, .arg 1, .arg 2])

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

private def validFifoCursorQuery : ProofForge.Svm.AccountStorage.Query :=
  .fifoCursorOneBased 1 110 114 115 116 117 8 4096 true

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
#guard validFifoCursorQuery.wellFormed
#guard validFifoCursorQuery.arity == 3
#guard validKey4FindQuery.arity == 4
#guard validFifoFindQuery.effects.reads == #[1]
#guard validFifoFindQuery.effects.writes.isEmpty
#guard validFifoCursorQuery.effects.reads == #[1]
#guard validFifoCursorQuery.effects.writes.isEmpty
#guard validKey4FindQuery.effects.reads == #[1]
#guard validKey4FindQuery.effects.writes.isEmpty
#guard validFifoFindQuery.canonical
    (fun value : ProofForge.Svm.Ops.Val => match value with | .arg i => s!"a{i}" | _ => "v")
    (#[.arg 0, .arg 1] : Array ProofForge.Svm.Ops.Val) ==
  "rbof.1.110.114.116.117.8.4096.true(a0,a1)"
#guard validFifoCursorQuery.canonical
    (fun value : ProofForge.Svm.Ops.Val => match value with | .arg i => s!"a{i}" | _ => "v")
    (#[.arg 0, .arg 1, .arg 2] : Array ProofForge.Svm.Ops.Val) ==
  "rboc.1.110.114.116.117.8.4096.true(a0,a1,a2)"
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

private def fifoCursorAssembly :=
  ProofForge.Svm.AccountStorage.Emit.emitQuery findEmitContext validFifoCursorQuery
    #[.arg 0, .arg 1, .arg 2] 160 0 "fifo_cursor_test"

private def stateFindAssembly :=
  ProofForge.Svm.AccountStorage.Emit.emitQuery findEmitContext stateKey4FindQuery
    #[.arg 0, .arg 1, .arg 2, .arg 3] 160 0 "state_find_test"

private def componentFifoCursorAssembly :=
  ProofForge.Svm.Component.Emit.emitQuery
    { loadValue := findEmitContext.loadValue
      loadOwnerIsSelf := findEmitContext.loadOwnerIsSelf
      headerStack := findEmitContext.headerStack
      accountCount := 2 }
    (.accountStorage validFifoCursorQuery) #[.arg 0, .arg 1, .arg 2]
    160 0 "fifo_cursor_test"

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
  match fifoCursorAssembly with
  | .ok assembly =>
      assembly.contains
          "bounded key-based acc1 FIFO cursor root=110 links=114 stride=8 capacity=4096" &&
        assembly.contains "jgt r1, r3, rb_cursor_before_" &&
        assembly.contains "jlt r1, r3, rb_cursor_after_" &&
        assembly.contains "stxdw [r10 - 208], r2" &&
        assembly.contains "lddw r3, 64" && !assembly.contains "be64 r1"
  | .error _ => false

#guard
  match componentFifoCursorAssembly, fifoCursorAssembly with
  | .ok componentAssembly, .ok storageAssembly => componentAssembly == storageAssembly
  | .error componentError, .error storageError => componentError == storageError
  | _, _ => false

#guard
  match stateFindAssembly with
  | .ok assembly =>
      assembly.contains "ldxdw r1, [r6 + ACC0_DATA_LEN]" &&
        assembly.contains "add64 r5, ACC0_DATA" &&
        assembly.contains "bounded one-based acc0 RB find root=1 links=4 stride=10 capacity=4"
  | .error _ => false

private def validAccDataWordSetAtOp : ProofForge.Svm.Ops.Op :=
  .ext (.component (.accountStorage
    (.writeWordZeroBased 1 8314 18 128 (.arg 0) (.arg 1))))

private def stateAccDataWordSetAtOp : ProofForge.Svm.Ops.Op :=
  .ext (.component (.accountStorage
    (.writeWordZeroBased 0 1 1 1 (.arg 0) (.arg 1))))

private def unboundedAccDataWordSetAtOp : ProofForge.Svm.Ops.Op :=
  .ext (.component (.accountStorage
    (.writeWordZeroBased 1 8314 0 128 (.arg 0) (.arg 1))))

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

private def oneBasedTraderComponent :
    ProofForge.Svm.Component.Call ProofForge.Svm.Ops.Val :=
  .accountStorage oneBasedTraderWrite

#guard oneBasedTraderLinks.wellFormed
#guard oneBasedTraderWrite.wellFormed
  (·.wellFormed ProofForge.Svm.Ops.ValKind.arity)
#guard oneBasedTraderWrite.effects.reads == #[1]
#guard oneBasedTraderWrite.effects.writes == #[1]
#guard oneBasedTraderWrite.canonical (fun | .arg i => s!"a{i}" | _ => "v") ==
  "dws1.1.8314.18.128(a0,a1)"
#guard oneBasedTraderComponent.values == #[.arg 0, .arg 1]
#guard oneBasedTraderComponent.effects == oneBasedTraderWrite.effects
#guard oneBasedTraderComponent.canonical (fun | .arg i => s!"a{i}" | _ => "v") ==
  "dws1.1.8314.18.128(a0,a1)"

private def phoenixRecorderConfig : ProofForge.Svm.BatchRecorder.Config :=
  { logAccount := 0
    selfEntryTag := 15
    authoritySeed := "log"
    maxBytes := 1246
    headerBytes := 93
    countOffset := 91
    maxRecords := 32 }

private def mutableOneBasedField (account baseWord strideWords capacity : Nat) :
    ProofForge.Svm.AccountStorage.Field :=
  { region :=
      { account, baseWord, strideWords, capacity
        indexBase := .one
        access := { writable := true, currentProgramOwned := true } } }

private def phoenixAskCancelConfig : ProofForge.Svm.FifoCancel.Config :=
  { map := .fifoOneBased 1 4210 4214 4215 4216 4217 8 512 false
    owner := mutableOneBasedField 1 4218 8 512
    size := mutableOneBasedField 1 4219 8 512
    locked := mutableOneBasedField 1 8322 18 128
    free := mutableOneBasedField 1 8323 18 128
    collateral := .base
    recorder := phoenixRecorderConfig }

private def phoenixAskCancel : ProofForge.Svm.Component.Call ProofForge.Svm.Ops.Val :=
  .fifoCancel (.cancelSide phoenixAskCancelConfig (.arg 0))

private def phoenixAskCancelUpTo : ProofForge.Svm.Component.Call ProofForge.Svm.Ops.Val :=
  .fifoCancel (.cancelUpTo phoenixAskCancelConfig (.arg 0) (.arg 1) (.arg 2) (.arg 3) true)

private def fifoEventCountQuery : ProofForge.Svm.Component.Query :=
  .fifoCancel .eventCount

#guard phoenixAskCancelConfig.wellFormed
#guard !({ phoenixAskCancelConfig with collateral := .quote 104 105 }).wellFormed
#guard phoenixAskCancel.values == #[.arg 0]
#guard phoenixAskCancel.effects.reads == #[1]
#guard phoenixAskCancel.effects.writes == #[1]
#guard phoenixAskCancel.minAccounts (fun _ => 0) == 2
#guard phoenixAskCancel.usesCpi
#guard phoenixAskCancel.stackScratchEnd == ProofForge.Svm.BatchRecorder.stackScratchEnd
#guard phoenixAskCancel.canonical (fun | .arg i => s!"a{i}" | _ => "v") ==
  "fcs.1.4210.4214.4215.4216.4217.4218.4219.8322.8323.8.512.b.a0"
#guard phoenixAskCancelUpTo.values == #[.arg 0, .arg 1, .arg 2, .arg 3]
#guard phoenixAskCancelUpTo.effects == phoenixAskCancel.effects
#guard phoenixAskCancelUpTo.usesCpi
#guard phoenixAskCancelUpTo.canonical (fun | .arg i => s!"a{i}" | _ => "v") ==
  "fcu.1.4210.4214.4215.4216.4217.4218.4219.8322.8323.8.512.b.c.a0.a1.a2.a3"
#guard fifoEventCountQuery.arity == 0
#guard fifoEventCountQuery.effects.reads.isEmpty && fifoEventCountQuery.effects.writes.isEmpty
#guard fifoEventCountQuery.wellFormed
#guard fifoEventCountQuery.canonical (fun _ : ProofForge.Svm.Ops.Val => "v") #[] == "fcqe"
#guard fifoEventCountQuery.canonical (fun _ : ProofForge.Svm.Ops.Val => "v") #[.lit 1] ==
  "invalid-fcqe-1"
#guard ProofForge.Svm.FifoCancel.eventIndexStack > 2048
#guard ProofForge.Svm.FifoCancel.queryScratchEnd ≤ 4096

private def phoenixRecorderHeader :
    Array (ProofForge.Svm.BatchRecorder.Word ProofForge.Svm.Ops.Val) :=
  #[.u8le (.lit 1), .u8le (.lit 5),
    .u64le (.arg 0), .u64le (.lit 2), .u64le (.lit 3),
    .u64le (.lit 4), .u64le (.lit 5), .u64le (.lit 6), .u64le (.lit 7),
    .accountKey 2, .u16le (.lit 0)]

private def phoenixReduceRecord :
    Array (ProofForge.Svm.BatchRecorder.Word ProofForge.Svm.Ops.Val) :=
  #[.u8le (.lit 4), .u16le (.arg 1), .u64le (.arg 2), .u64le (.arg 3),
    .u64le (.arg 4), .u64le (.arg 5)]

private def recorderBegin : ProofForge.Svm.Component.Call ProofForge.Svm.Ops.Val :=
  .batchRecorder (.begin phoenixRecorderConfig phoenixRecorderHeader (.arg 6))

private def recorderAppend : ProofForge.Svm.Component.Call ProofForge.Svm.Ops.Val :=
  .batchRecorder (.append phoenixRecorderConfig (.arg 7) phoenixReduceRecord)

private def recorderFinish : ProofForge.Svm.Component.Call ProofForge.Svm.Ops.Val :=
  .batchRecorder (.finish phoenixRecorderConfig)

private def malformedRecorderBegin : ProofForge.Svm.Component.Call ProofForge.Svm.Ops.Val :=
  .batchRecorder (.begin phoenixRecorderConfig (phoenixRecorderHeader.pop) (.arg 6))

#guard phoenixRecorderConfig.wellFormed
#guard !({ phoenixRecorderConfig with maxBytes := 1247 }).wellFormed
#guard ProofForge.Svm.BatchRecorder.wordsByteSize phoenixRecorderHeader == 92
#guard ProofForge.Svm.BatchRecorder.wordsByteSize phoenixReduceRecord == 35
#guard 93 + 32 * 35 == 1213
#guard 93 + 33 * 35 > ProofForge.Svm.BatchRecorder.maxInnerDataBytes
#guard recorderBegin.wellFormed (·.wellFormed ProofForge.Svm.Ops.ValKind.arity)
#guard recorderAppend.wellFormed (·.wellFormed ProofForge.Svm.Ops.ValKind.arity)
#guard recorderFinish.wellFormed (·.wellFormed ProofForge.Svm.Ops.ValKind.arity)
#guard !malformedRecorderBegin.wellFormed (·.wellFormed ProofForge.Svm.Ops.ValKind.arity)
#guard recorderBegin.effects.reads == #[1, 3]
#guard recorderBegin.effects.writes.isEmpty
#guard recorderBegin.minAccounts (fun _ => 0) == 4
#guard recorderBegin.usesCpi && recorderAppend.usesCpi && recorderFinish.usesCpi
#guard recorderBegin.stackScratchEnd == ProofForge.Svm.BatchRecorder.activeStack
#guard recorderBegin.rawSelfEntries == #[(15, "log")]
#guard recorderAppend.rawSelfEntries.isEmpty && recorderFinish.rawSelfEntries.isEmpty
#guard recorderAppend.canonical (fun | .arg i => s!"a{i}" | .lit n => s!"{n}" | _ => "v") ==
  "bra.0.15.log.1246.93.91.32(a7,[b1:4,b2:a1,b8:a2,b8:a3,b8:a4,b8:a5])"

private def recorderProgram : ProofForge.Svm.IR.Program :=
  { name := "Recorder"
    slots := #[]
    methods := #[{
      kind := .increment
      name := "Recorder.record"
      ixName := "record"
      paramCount := 8
      ops := #[.component recorderBegin, .component recorderAppend, .component recorderFinish]
    }] }

#guard ProofForge.Svm.IR.usesCpi recorderProgram
#guard ProofForge.Svm.IR.componentStackScratchEnd recorderProgram ==
  ProofForge.Svm.BatchRecorder.activeStack
#guard ProofForge.Svm.IR.cpiAccountCount recorderProgram == 4
#guard
  match ProofForge.Svm.IR.rawSelfEntry? recorderProgram with
  | .ok (some entry) => entry.tag == 15 && entry.authoritySeed == "log"
  | _ => false

private def recorderEmitContext : ProofForge.Svm.BatchRecorder.Emit.Context :=
  { loadValue := fun value stackOff _ _ =>
      match value with
      | .lit literal =>
          .ok s!"  lddw r1, {literal}\n  stxdw [r10 - {stackOff}], r1\n"
      | .arg index =>
          .ok s!"  lddw r1, {index}\n  stxdw [r10 - {stackOff}], r1\n"
      | _ => .error "unexpected recorder test value"
    headerStack := fun account => 512 + 8 * account
    accountCount := 4 }

private def recorderComponentEmitContext : ProofForge.Svm.Component.Emit.Context :=
  { loadValue := recorderEmitContext.loadValue
    loadOwnerIsSelf := fun _ _ _ => ""
    headerStack := recorderEmitContext.headerStack
    accountCount := recorderEmitContext.accountCount }

private def unusedStorageBackend : ProofForge.Svm.Component.Emit.Backend :=
  { accountStorage :=
      { emitInsert := fun _ _ _ _ _ => .error "unused storage insert"
        emitRemove := fun _ _ _ => .error "unused storage remove"
        emitRemoveValidated := fun _ _ _ _ => .error "unused validated storage remove"
        emitCheckedAdd := fun _ _ _ _ => .error "unused storage checked add" } }

private def recorderBeginAssembly :=
  ProofForge.Svm.Component.Emit.emitCall recorderComponentEmitContext unusedStorageBackend
    "recorder_begin_test" recorderBegin

private def recorderAppendAssembly :=
  ProofForge.Svm.Component.Emit.emitCall recorderComponentEmitContext unusedStorageBackend
    "recorder_append_test" recorderAppend

private def recorderFinishAssembly :=
  ProofForge.Svm.Component.Emit.emitCall recorderComponentEmitContext unusedStorageBackend
    "recorder_finish_test" recorderFinish

private def fifoCancelBackend : ProofForge.Svm.Component.Emit.Backend :=
  { accountStorage :=
      { emitInsert := fun _ _ _ _ _ => .error "unused FIFO insert"
        emitRemove := fun _ _ _ => .ok "  ; ordinary-remove-hook\n"
        emitRemoveValidated := fun _ _ _ _ => .ok "  ; validated-remove-hook\n"
        emitCheckedAdd := fun _ _ _ _ => .error "unused FIFO checked add" } }

private def fifoCancelBeginAssembly :=
  ProofForge.Svm.Component.Emit.emitCall recorderComponentEmitContext fifoCancelBackend
    "fifo_cancel_begin_test" (.fifoCancel .begin)

private def fifoCancelSideAssembly :=
  ProofForge.Svm.Component.Emit.emitCall recorderComponentEmitContext fifoCancelBackend
    "fifo_cancel_side_test" phoenixAskCancel

private def fifoCancelUpToAssembly :=
  ProofForge.Svm.Component.Emit.emitCall recorderComponentEmitContext fifoCancelBackend
    "fifo_cancel_up_to_test" phoenixAskCancelUpTo

private def fifoEventCountAssembly :=
  ProofForge.Svm.Component.Emit.emitQuery recorderComponentEmitContext fifoEventCountQuery #[]
    160 0 "fifo_event_count_test"

#guard ProofForge.Svm.Heap.startAddress == 0x300000000
#guard ProofForge.Svm.Heap.defaultFrameBytes == 32 * 1024
#guard
  match recorderBeginAssembly with
  | .ok assembly =>
      assembly.contains "official Solana downward bump allocation bytes=1246 align=8" &&
        assembly.contains "lddw r4, 12884901888" &&
        assembly.contains "lddw r2, 12884934656" &&
        assembly.contains "lddw r3, 0xfffffffffffffff8" &&
        assembly.contains "stxdw [r10 - 416], r2" &&
        assembly.contains "stxdw [r10 - 448], r1"
  | .error _ => false
#guard
  match recorderAppendAssembly with
  | .ok assembly =>
      assembly.contains "jge r1, 32, recorder_append_flush_recorder_append_test" &&
        assembly.contains "add64 r1, 35" && assembly.contains "jgt r1, 1246" &&
        assembly.contains "dynamic signed self CPI account=1 data<=1246"
  | .error _ => false
#guard
  match recorderFinishAssembly with
  | .ok assembly =>
      assembly.contains "dynamic signed self CPI account=1 data<=1246" &&
        assembly.contains "lddw r1, 93" && assembly.contains "stxdw [r10 - 448], r1"
  | .error _ => false
#guard
  match fifoCancelBeginAssembly with
  | .ok assembly =>
      assembly.contains "open bounded FIFO cancellation accumulator" &&
        assembly.contains "stxdw [r10 - 2056], r1" &&
        assembly.contains "stxdw [r10 - 2072], r1" &&
        assembly.contains "stxdw [r10 - 2184], r1"
  | .error _ => false
#guard
  match fifoCancelSideAssembly with
  | .ok assembly =>
      assembly.contains
          "bounded key-based acc1 FIFO cursor root=4210 links=4214 stride=8 capacity=512" &&
        assembly.contains "; validated-remove-hook" &&
        !assembly.contains "; ordinary-remove-hook" && !assembly.contains "_preflight" &&
        assembly.contains "ldxdw r1, [r10 - 2056]" &&
        assembly.contains "jge r1, 65535, fifo_cancel_failure_fifo_cancel_side_test" &&
        assembly.contains "dynamic signed self CPI account=1 data<=1246"
  | .error _ => false
#guard
  match fifoCancelUpToAssembly with
  | .ok assembly =>
      assembly.contains "stxdw [r10 - 2264], r1" &&
        assembly.contains "stxdw [r10 - 2272], r1" &&
        assembly.contains "stxdw [r10 - 2280], r1" &&
        assembly.contains "ldxdw r1, [r10 - 2288]" &&
        assembly.contains "ldxdw r1, [r10 - 2296]" &&
        assembly.contains "jle r1, r2, fifo_cancel_price_matched_fifo_cancel_up_to_test" &&
        assembly.contains "; claim exactly this order's released collateral" &&
        assembly.contains "; validated-remove-hook" &&
        !assembly.contains "; ordinary-remove-hook"
  | .error _ => false
#guard
  match fifoEventCountAssembly with
  | .ok assembly =>
      assembly.contains "fifo_cancel_active_fifo_event_count_test" &&
        assembly.contains "ldxdw r1, [r10 - 2056]" &&
        assembly.contains "stxdw [r10 - 160], r1"
  | .error _ => false

#guard
  match ProofForge.Svm.IR.ofSourceOps #[validAccDataWordSetAtOp] with
  | .ok #[.component (.accountStorage (.writeWord field (.arg 0) (.arg 1)))] =>
      field.region.account == 1 && field.firstWord == 8314 &&
        field.region.strideWords == 18 && field.region.capacity == 128 &&
        field.region.indexBase == .zero
  | _ => false
#guard
  match ProofForge.Svm.IR.ofSourceOps
      #[.ext (.component (.accountStorage
        (.writeWordOneBased 1 8314 18 128 (.arg 0) (.arg 1))))] with
  | .ok #[.component (.accountStorage (.writeWord field (.arg 0) (.arg 1)))] =>
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
