import ProofForge.Svm.FifoCancel
import ProofForge.Svm.AccountStorage.Emit
import ProofForge.Svm.BatchRecorder.Emit

namespace ProofForge.Svm.FifoCancel.Emit

structure Context where
  loadValue : Ops.Val → Nat → Nat → String → Except String String
  loadOwnerIsSelf : Nat → Nat → String → String
  headerStack : Nat → Nat
  accountCount : Nat

private def activeMagic : Nat := 0x50464649464f4301

private def failClosed : String :=
  "  lddw r0, 0x1\n  exit\n"

private def emitRequireActive (label : String) : String :=
  s!"\
  ldxdw r1, [r10 - {FifoCancel.activeStack}]
  lddw r2, {activeMagic}
  jeq r1, r2, fifo_cancel_active_{label}
{failClosed}fifo_cancel_active_{label}:
"

private def copyStack (source destination : Nat) : String :=
  s!"  ldxdw r1, [r10 - {source}]\n  stxdw [r10 - {destination}], r1\n"

private def markerHasCursor : Nat := 1000000
private def markerCursorPrice : Nat := 1000001
private def markerCursorSequence : Nat := 1000002
private def markerOrderIndex : Nat := 1000003
private def markerPrice : Nat := 1000004
private def markerSequence : Nat := 1000005
private def markerEventIndex : Nat := 1000006
private def markerSize : Nat := 1000007
private def markerLocked : Nat := 1000008
private def markerFree : Nat := 1000009
private def markerTraderIndex : Nat := 1000010

private def markerStack? (marker : Nat) : Option Nat :=
  if marker == markerHasCursor then some FifoCancel.hasCursorStack
  else if marker == markerCursorPrice then some FifoCancel.cursorPriceStack
  else if marker == markerCursorSequence then some FifoCancel.cursorSequenceStack
  else if marker == markerOrderIndex then some FifoCancel.orderIndexStack
  else if marker == markerPrice then some FifoCancel.priceStack
  else if marker == markerSequence then some FifoCancel.sequenceStack
  else if marker == markerEventIndex then some FifoCancel.eventIndexStack
  else if marker == markerSize then some FifoCancel.sizeStack
  else if marker == markerLocked then some FifoCancel.lockedStack
  else if marker == markerFree then some FifoCancel.freeStack
  else if marker == markerTraderIndex then some FifoCancel.traderIndexStack
  else none

private def Context.internalLoad (context : Context) (value : Ops.Val)
    (stackOff nonce : Nat) (scope : String) : Except String String :=
  match value with
  | .local marker =>
      match markerStack? marker with
      | some source => .ok (copyStack source stackOff)
      | none => context.loadValue value stackOff nonce scope
  | _ => context.loadValue value stackOff nonce scope

private def Context.accountStorage (context : Context) : AccountStorage.Emit.Context :=
  { loadValue := context.internalLoad
    loadOwnerIsSelf := context.loadOwnerIsSelf
    headerStack := context.headerStack }

private def Context.batchRecorder (context : Context) : BatchRecorder.Emit.Context :=
  { loadValue := context.internalLoad
    headerStack := context.headerStack
    accountCount := context.accountCount }

private def marker (id : Nat) : Ops.Val := .local id

private def emitReadField (context : Context) (label : String)
    (field : AccountStorage.Field) (indexMarker destination nonce : Nat) : Except String String :=
  AccountStorage.Emit.emitQuery context.accountStorage (.readWord field)
    #[marker indexMarker] destination nonce label

private def emitWriteField (context : Context) (backend : AccountStorage.Emit.MutationBackend)
    (label : String) (field : AccountStorage.Field) (indexMarker valueMarker : Nat) :
    Except String String :=
  AccountStorage.Emit.emitCall context.accountStorage backend label
    (.writeWord field (marker indexMarker) (marker valueMarker))

private def emitBegin : String :=
  s!"\
  ; open bounded FIFO cancellation accumulator
  lddw r1, 0
  stxdw [r10 - {FifoCancel.eventIndexStack}], r1
  stxdw [r10 - {FifoCancel.quoteReleasedStack}], r1
  stxdw [r10 - {FifoCancel.baseReleasedStack}], r1
  lddw r1, {activeMagic}
  stxdw [r10 - {FifoCancel.activeStack}], r1
"

private def emitFinish (label : String) : String :=
  emitRequireActive label ++ s!"\
  lddw r1, 0
  stxdw [r10 - {FifoCancel.activeStack}], r1
"

private def emitReleased (context : Context) (config : FifoCancel.Config)
    (label : String) : Except String String :=
  match config.collateral with
  | .base =>
      .ok (copyStack FifoCancel.sizeStack FifoCancel.releasedStack)
  | .quote baseLotsPerBaseUnitWord tickSizeWord => do
      let account := config.map.account
      let loadBase ← context.loadValue (Ops.accDataWord account baseLotsPerBaseUnitWord)
        8 20 s!"{label}_base_lots_per_unit"
      let loadTick ← context.loadValue (Ops.accDataWord account tickSizeWord)
        16 21 s!"{label}_tick_size"
      let mulPriceOk := s!"fifo_cancel_price_mul_ok_{label}"
      let mulSizeOk := s!"fifo_cancel_size_mul_ok_{label}"
      return loadBase ++ loadTick ++ s!"\
  ldxdw r1, [r10 - 8]
  jeq r1, 0, fifo_cancel_failure_{label}
  ldxdw r2, [r10 - 16]
  ldxdw r3, [r10 - {FifoCancel.priceStack}]
  jeq r3, 0, {mulPriceOk}
  lddw r4, 0xffffffffffffffff
  div64 r4, r3
  jgt r2, r4, fifo_cancel_failure_{label}
{mulPriceOk}:
  mul64 r2, r3
  ldxdw r3, [r10 - {FifoCancel.sizeStack}]
  jeq r3, 0, {mulSizeOk}
  lddw r4, 0xffffffffffffffff
  div64 r4, r3
  jgt r2, r4, fifo_cancel_failure_{label}
{mulSizeOk}:
  mul64 r2, r3
  div64 r2, r1
  stxdw [r10 - {FifoCancel.releasedStack}], r2
"

private def emitCancelSide (context : Context) (backend : AccountStorage.Emit.MutationBackend)
    (label : String) (config : FifoCancel.Config) (traderIndex : Ops.Val) :
    Except String String := do
  let (.fifo rootWord tree) := config.map
    | throw "extract/ir: FIFO cancel requires a FIFO map"
  let loadTrader ← context.loadValue traderIndex FifoCancel.traderIndexStack 0
    s!"{label}_trader"
  let cursor ← AccountStorage.Emit.emitQuery context.accountStorage
    (.fifoCursor rootWord tree)
    #[marker markerHasCursor, marker markerCursorPrice, marker markerCursorSequence]
    FifoCancel.orderIndexStack 1 s!"{label}_cursor"
  let readPrice ← emitReadField context s!"{label}_price" tree.price markerOrderIndex
    FifoCancel.priceStack 5
  let readSequence ← emitReadField context s!"{label}_sequence" tree.sequence
    markerOrderIndex FifoCancel.sequenceStack 7
  let readOwner ← emitReadField context s!"{label}_owner" config.owner markerOrderIndex
    FifoCancel.ownerStack 9
  let readSize ← emitReadField context s!"{label}_size" config.size markerOrderIndex
    FifoCancel.sizeStack 11
  let released ← emitReleased context config label
  let readLocked ← emitReadField context s!"{label}_locked" config.locked
    markerTraderIndex FifoCancel.lockedStack 13
  let readFree ← emitReadField context s!"{label}_free" config.free markerTraderIndex
    FifoCancel.freeStack 15
  let remove ← backend.emitRemoveValidated context.internalLoad s!"{label}_remove"
    config.map #[marker markerPrice, marker markerSequence]
  let writeLocked ← emitWriteField context backend s!"{label}_locked_write" config.locked
    markerTraderIndex markerLocked
  let writeFree ← emitWriteField context backend s!"{label}_free_write" config.free
    markerTraderIndex markerFree
  let append ← BatchRecorder.Emit.emitCall context.batchRecorder s!"{label}_record"
    (.append config.recorder (.lit 1)
      #[.u8le (.lit 4), .u16le (marker markerEventIndex),
        .u64le (marker markerSequence), .u64le (marker markerPrice),
        .u64le (marker markerSize), .u64le (.lit 0)])
  let accumulatorStack := match config.collateral with
    | .quote .. => FifoCancel.quoteReleasedStack
    | .base => FifoCancel.baseReleasedStack
  let loop := s!"fifo_cancel_loop_{label}"
  let next := s!"fifo_cancel_next_{label}"
  let done := s!"fifo_cancel_done_{label}"
  let owned := s!"fifo_cancel_owned_{label}"
  return emitRequireActive label ++ loadTrader ++ s!"\
  ldxdw r1, [r10 - {FifoCancel.traderIndexStack}]
  jeq r1, 0, {done}
  lddw r1, 0
  stxdw [r10 - {FifoCancel.hasCursorStack}], r1
  stxdw [r10 - {FifoCancel.cursorPriceStack}], r1
  stxdw [r10 - {FifoCancel.cursorSequenceStack}], r1
  stxdw [r10 - {FifoCancel.loopStack}], r1
{loop}:
  ldxdw r1, [r10 - {FifoCancel.loopStack}]
  jge r1, {config.map.capacity}, {done}
{cursor}\
  ldxdw r1, [r10 - {FifoCancel.orderIndexStack}]
  jeq r1, 0, {done}
{readPrice}{readSequence}{readOwner}{readSize}\
  lddw r1, 1
  stxdw [r10 - {FifoCancel.hasCursorStack}], r1
  ldxdw r1, [r10 - {FifoCancel.priceStack}]
  stxdw [r10 - {FifoCancel.cursorPriceStack}], r1
  ldxdw r1, [r10 - {FifoCancel.sequenceStack}]
  stxdw [r10 - {FifoCancel.cursorSequenceStack}], r1
  ldxdw r1, [r10 - {FifoCancel.sizeStack}]
  jeq r1, 0, {next}
  ldxdw r1, [r10 - {FifoCancel.ownerStack}]
  ldxdw r2, [r10 - {FifoCancel.traderIndexStack}]
  jeq r1, r2, {owned}
  ja {next}
{owned}:
{released}{readLocked}{readFree}\
  ldxdw r1, [r10 - {FifoCancel.releasedStack}]
  ldxdw r2, [r10 - {FifoCancel.lockedStack}]
  jgt r1, r2, fifo_cancel_failure_{label}
  sub64 r2, r1
  stxdw [r10 - {FifoCancel.lockedStack}], r2
  ldxdw r2, [r10 - {FifoCancel.freeStack}]
  lddw r3, 0xffffffffffffffff
  sub64 r3, r1
  jgt r2, r3, fifo_cancel_failure_{label}
  add64 r2, r1
  stxdw [r10 - {FifoCancel.freeStack}], r2
  ldxdw r2, [r10 - {accumulatorStack}]
  lddw r3, 0xffffffffffffffff
  sub64 r3, r1
  jgt r2, r3, fifo_cancel_failure_{label}
  add64 r2, r1
  stxdw [r10 - {accumulatorStack}], r2
{remove}{writeLocked}{writeFree}{append}\
  ldxdw r1, [r10 - {FifoCancel.eventIndexStack}]
  jge r1, 65535, fifo_cancel_failure_{label}
  add64 r1, 1
  stxdw [r10 - {FifoCancel.eventIndexStack}], r1
{next}:
  ldxdw r1, [r10 - {FifoCancel.loopStack}]
  add64 r1, 1
  stxdw [r10 - {FifoCancel.loopStack}], r1
  ja {loop}
fifo_cancel_failure_{label}:
{failClosed}{done}:
"

def emitQuery (label : String) (query : FifoCancel.Query) (operands : Array Ops.Val)
    (stackOff : Nat) : Except String String := do
  unless operands.isEmpty do
    throw "extract/ir: FIFO cancel result query takes no operands"
  return emitRequireActive label ++ copyStack query.stack stackOff

def emitCall (context : Context) (backend : AccountStorage.Emit.MutationBackend)
    (label : String) : FifoCancel.Call Ops.Val → Except String String
  | .begin => .ok emitBegin
  | .cancelSide config traderIndex => emitCancelSide context backend label config traderIndex
  | .finish => .ok (emitFinish label)

end ProofForge.Svm.FifoCancel.Emit
