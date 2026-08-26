import ProofForge.Svm.BatchRecorder
import ProofForge.Svm.Cpi.Emit
import ProofForge.Svm.Heap
import ProofForge.Svm.Ops

namespace ProofForge.Svm.BatchRecorder.Emit

structure Context where
  loadValue : Ops.Val → Nat → Nat → String → Except String String
  headerStack : Nat → Nat
  accountCount : Nat

private def activeMagic : Nat := 0x5046424154434801

private def failClosed : String :=
  "  lddw r0, 0x1\n  exit\n"

private def emitRequireActive (label : String) : String :=
  s!"\
  ldxdw r1, [r10 - {BatchRecorder.activeStack}]
  lddw r2, {activeMagic}
  jeq r1, r2, recorder_active_{label}
{failClosed}recorder_active_{label}:
"

/-- Allocate from the same first-word, downward bump protocol used by Solana's Rust SDK. The SDK
global allocator is fixed to the default 32 KiB even when a transaction requests a larger frame,
so generated code deliberately uses the same conservative end address. -/
private def emitHeapAllocate (label : String) (bytes : Nat) : String :=
  let heapEnd := Heap.startAddress + Heap.defaultFrameBytes
  let usableStart := Heap.startAddress + Heap.bumpWordBytes
  s!"\
  ; official Solana downward bump allocation bytes={bytes} align=8
  lddw r4, {Heap.startAddress}
  ldxdw r2, [r4 + 0]
  jne r2, 0, recorder_heap_position_{label}
  lddw r2, {heapEnd}
recorder_heap_position_{label}:
  lddw r3, {bytes}
  jge r2, r3, recorder_heap_subtract_{label}
{failClosed}recorder_heap_subtract_{label}:
  sub64 r2, r3
  lddw r3, 0xfffffffffffffff8
  and64 r2, r3
  lddw r3, {usableStart}
  jge r2, r3, recorder_heap_commit_{label}
{failClosed}recorder_heap_commit_{label}:
  stxdw [r4 + 0], r2
  stxdw [r10 - {BatchRecorder.pointerStack}], r2
"

private def emitDestinationBase (dynamic : Bool) : String :=
  s!"  ldxdw r9, [r10 - {BatchRecorder.pointerStack}]\n" ++
    if dynamic then
      s!"  ldxdw r2, [r10 - {BatchRecorder.lengthStack}]\n  add64 r9, r2\n"
    else ""

private def emitInteger (context : Context) (label : String) (dynamic : Bool)
    (offset width nonce : Nat) (value : Ops.Val) : Except String String := do
  let store := match width with | 1 => "stxb" | 2 => "stxh" | 4 => "stxw" | _ => "stxdw"
  let load ← context.loadValue value 8 nonce s!"{label}_word_{offset}"
  return load ++ emitDestinationBase dynamic ++
    s!"  ldxdw r1, [r10 - 8]\n  {store} [r9 + {offset}], r1\n"

private def emitWords (context : Context) (label : String) (dynamic : Bool)
    (startOffset nonce : Nat) (words : Array (BatchRecorder.Word Ops.Val)) :
    Except String String := do
  let mut output := ""
  let mut offset := startOffset
  for i in [0:words.size] do
    match words[i]! with
    | .u8le value =>
        output := output ++ (← emitInteger context label dynamic offset 1 (nonce + i) value)
        offset := offset + 1
    | .u16le value =>
        output := output ++ (← emitInteger context label dynamic offset 2 (nonce + i) value)
        offset := offset + 2
    | .u32le value =>
        output := output ++ (← emitInteger context label dynamic offset 4 (nonce + i) value)
        offset := offset + 4
    | .u64le value =>
        output := output ++ (← emitInteger context label dynamic offset 8 (nonce + i) value)
        offset := offset + 8
    | .ascii value =>
        for j in [0:value.length] do
          output := output ++ emitDestinationBase dynamic ++
            s!"  lddw r1, {value.toList[j]!.toNat}\n  stxb [r9 + {offset + j}], r1\n"
        offset := offset + value.length
    | .programId =>
        output := output ++ emitDestinationBase dynamic ++ s!"\
  ldxdw r1, [r10 - {context.headerStack context.accountCount}]
  ldxdw r2, [r1 + 0]
  add64 r1, 8
  add64 r1, r2
  ldxdw r2, [r1 + 0]
  stxdw [r9 + {offset}], r2
  ldxdw r2, [r1 + 8]
  stxdw [r9 + {offset + 8}], r2
  ldxdw r2, [r1 + 16]
  stxdw [r9 + {offset + 16}], r2
  ldxdw r2, [r1 + 24]
  stxdw [r9 + {offset + 24}], r2
"
        offset := offset + 32
    | .accountKey account =>
        output := output ++ emitDestinationBase dynamic ++ s!"\
  ldxdw r1, [r10 - {context.headerStack (account + 1)}]
  add64 r1, 8
  ldxdw r2, [r1 + 0]
  stxdw [r9 + {offset}], r2
  ldxdw r2, [r1 + 8]
  stxdw [r9 + {offset + 8}], r2
  ldxdw r2, [r1 + 16]
  stxdw [r9 + {offset + 16}], r2
  ldxdw r2, [r1 + 24]
  stxdw [r9 + {offset + 24}], r2
"
        offset := offset + 32
  return output

private def emitFlushBody (context : Context) (config : BatchRecorder.Config)
    (label : String) : Except String String := do
  let invoke ← Cpi.Emit.emitDynamicSignedSelf
    { headerStack := context.headerStack, accountCount := context.accountCount }
    label config.logAccount config.authoritySeed BatchRecorder.pointerStack
    BatchRecorder.lengthStack BatchRecorder.bumpStack
  return s!"\
  ldxdw r9, [r10 - {BatchRecorder.pointerStack}]
  ldxdw r1, [r10 - {BatchRecorder.countStack}]
  stxh [r9 + {config.countOffset}], r1
{invoke}\
  lddw r1, {config.headerBytes}
  stxdw [r10 - {BatchRecorder.lengthStack}], r1
  lddw r1, 0
  stxdw [r10 - {BatchRecorder.countStack}], r1
  ldxdw r9, [r10 - {BatchRecorder.pointerStack}]
  stxh [r9 + {config.countOffset}], r1
"

private def emitBegin (context : Context) (label : String) (config : BatchRecorder.Config)
    (header : Array (BatchRecorder.Word Ops.Val)) (bump : Ops.Val) : Except String String := do
  let loadBump ← context.loadValue bump 8 0 s!"{label}_bump"
  let headerBytes ← emitWords context label false 1 1 header
  return emitHeapAllocate label config.maxBytes ++ loadBump ++ s!"\
  ldxdw r1, [r10 - 8]
  stxdw [r10 - {BatchRecorder.bumpStack}], r1
  ldxdw r9, [r10 - {BatchRecorder.pointerStack}]
  lddw r1, {config.selfEntryTag}
  stxb [r9 + 0], r1
{headerBytes}\
  ldxdw r9, [r10 - {BatchRecorder.pointerStack}]
  lddw r1, 0
  stxh [r9 + {config.countOffset}], r1
  stxdw [r10 - {BatchRecorder.countStack}], r1
  lddw r1, {config.headerBytes}
  stxdw [r10 - {BatchRecorder.lengthStack}], r1
  lddw r1, {activeMagic}
  stxdw [r10 - {BatchRecorder.activeStack}], r1
"

private def emitAppend (context : Context) (label : String) (config : BatchRecorder.Config)
    (enabled : Ops.Val) (record : Array (BatchRecorder.Word Ops.Val)) : Except String String := do
  let recordBytes := BatchRecorder.wordsByteSize record
  let loadEnabled ← context.loadValue enabled 8 0 s!"{label}_enabled"
  let flush ← emitFlushBody context config s!"{label}_auto"
  let appendWords ← emitWords context label true 0 1 record
  return emitRequireActive label ++ loadEnabled ++ s!"\
  ldxdw r1, [r10 - 8]
  jeq r1, 0, recorder_append_done_{label}
  ldxdw r1, [r10 - {BatchRecorder.countStack}]
  jge r1, {config.maxRecords}, recorder_append_flush_{label}
  ldxdw r1, [r10 - {BatchRecorder.lengthStack}]
  add64 r1, {recordBytes}
  jgt r1, {config.maxBytes}, recorder_append_flush_{label}
  ja recorder_append_ready_{label}
recorder_append_flush_{label}:
{flush}recorder_append_ready_{label}:
{appendWords}\
  ldxdw r1, [r10 - {BatchRecorder.lengthStack}]
  add64 r1, {recordBytes}
  stxdw [r10 - {BatchRecorder.lengthStack}], r1
  ldxdw r1, [r10 - {BatchRecorder.countStack}]
  add64 r1, 1
  stxdw [r10 - {BatchRecorder.countStack}], r1
  ldxdw r9, [r10 - {BatchRecorder.pointerStack}]
  stxh [r9 + {config.countOffset}], r1
recorder_append_done_{label}:
"

private def emitFinish (context : Context) (label : String)
    (config : BatchRecorder.Config) : Except String String := do
  let flush ← emitFlushBody context config s!"{label}_finish"
  return emitRequireActive label ++ flush ++ s!"\
  lddw r1, 0
  stxdw [r10 - {BatchRecorder.activeStack}], r1
"

def emitCall (context : Context) (label : String) :
    BatchRecorder.Call Ops.Val → Except String String
  | .begin config header bump => emitBegin context label config header bump
  | .append config enabled record => emitAppend context label config enabled record
  | .finish config => emitFinish context label config

end ProofForge.Svm.BatchRecorder.Emit
