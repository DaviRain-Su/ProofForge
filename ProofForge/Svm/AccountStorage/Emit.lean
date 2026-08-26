import ProofForge.Svm.IR

namespace ProofForge.Svm.AccountStorage.Emit

/-- Whole-tree validation reuses the bottom 512 bytes after all operand expressions have been
loaded. It makes no syscalls, so this fixed bitmap never overlaps live PDA/sysvar scratch. -/
private def rbTreeBitmapScratch : Nat := 4096

/-- The storage backend receives the surrounding method's value loader and walked-account frame
locations. Container routines own their labels, bounds, authorization, and account-data stores. -/
structure Context where
  loadValue : Ops.Val → Nat → Nat → String → Except String String
  loadOwnerIsSelf : Nat → Nat → String → String
  headerStack : Nat → Nat

private def emitWriteWord (context : Context) (label : String)
    (field : Field) (index value : Ops.Val) : Except String String := do
  let region := field.region
  let loadIndex ← context.loadValue index 8 0 s!"{label}_index"
  let loadValue ← context.loadValue value 16 1 s!"{label}_value"
  let ownerCheck := context.loadOwnerIsSelf region.account 24 s!"{label}_owner"
  let baseBytes := 8 * field.firstWord
  let strideBytes := 8 * region.strideWords
  let writable := s!"dws_writable_{label}"
  let ownerOk := s!"dws_owner_ok_{label}"
  let indexOk := s!"dws_index_ok_{label}"
  let dataOk := s!"dws_data_ok_{label}"
  let done := s!"dws_done_{label}"
  let failure := s!"dws_failure_{label}"
  let indexCheck :=
    match region.indexBase with
    | .zero => s!"  lddw r1, {region.capacity}\n  jlt r2, r1, {indexOk}\n"
    | .one => s!"\
  jeq r2, 0, {failure}
  lddw r1, {region.capacity}
  jle r2, r1, {indexOk}
"
  let normalizeIndex :=
    match region.indexBase with
    | .zero => ""
    | .one => "  sub64 r2, 1\n"
  return loadIndex ++ loadValue ++ ownerCheck ++ s!"\
  ; fixed-stride external account word write acc={region.account} base={field.firstWord} stride={region.strideWords} capacity={region.capacity}
  ldxdw r8, [r10 - {context.headerStack region.account}]
  ldxb r1, [r8 + 2]
  jne r1, 0, {writable}
  ja {failure}
{writable}:
  ldxdw r1, [r10 - 24]
  jeq r1, 0, {ownerOk}
  ja {failure}
{ownerOk}:
  ldxdw r2, [r10 - 8]
" ++ indexCheck ++ s!"  ja {failure}\n{indexOk}:\n" ++ normalizeIndex ++ s!"\
  lddw r1, {strideBytes}
  mul64 r2, r1
  add64 r2, {baseBytes}
  mov64 r3, r2
  add64 r3, 8
  ldxdw r1, [r8 + 80]
  jge r1, r3, {dataOk}
  ja {failure}
{dataOk}:
  add64 r8, 88
  add64 r8, r2
  ldxdw r1, [r10 - 16]
  stxdw [r8 + 0], r1
  ja {done}
{failure}:
  lddw r0, 0x1
  exit
{done}:
"

/-- Follow one account-resident parent path with constant memory. Every dereference is selected
from static one-based regions, while index/root/bump and the final account length are checked
before pointer formation. A cycle that excludes the root exhausts `maxDepth` and returns zero. -/
private def emitParentPathValid (context : Context) (path : ParentPath)
    (index root bumpIndex : Ops.Val) (stackOff nonce : Nat) (scope : String) :
    Except String String := do
  let region := path.links.region
  let acc := region.account
  let linksBaseWord := path.links.firstWord
  let parentBaseWord := path.parentColor.firstWord
  let strideWords := region.strideWords
  let capacity := region.capacity
  let maxDepth := path.maxDepth
  let loadIndex ← context.loadValue index (stackOff + 8) (nonce + 1) (scope ++ "_index")
  let loadRoot ← context.loadValue root (stackOff + 16) (nonce + 2) (scope ++ "_root")
  let loadBump ← context.loadValue bumpIndex (stackOff + 24) (nonce + 3) (scope ++ "_bump")
  let strideBytes := 8 * strideWords
  let linksBaseBytes := 8 * linksBaseWord
  let parentBaseBytes := 8 * parentBaseWord
  let finalWord := Nat.max linksBaseWord parentBaseWord + strideWords * (capacity - 1)
  let requiredBytes := 8 * (finalWord + 1)
  let token := IR.u64Hex (Core.IR.fnv1a64
    (s!"{scope}:{stackOff}:{nonce}:{acc}:{linksBaseWord}:{parentBaseWord}:" ++
      s!"{strideWords}:{capacity}:{maxDepth}"))
  let dataOk := s!"ok_parent_path_data_{token}"
  let loop := s!"parent_path_loop_{token}"
  let edgeOk := s!"parent_path_edge_{token}"
  let rootCheck := s!"parent_path_root_{token}"
  let success := s!"parent_path_success_{token}"
  let failure := s!"parent_path_failure_{token}"
  let done := s!"parent_path_done_{token}"
  let account :=
    if acc == 0 then
      s!"\
  ldxdw r1, [r6 + ACC0_DATA_LEN]
  lddw r2, {requiredBytes}
  jge r1, r2, {dataOk}
  lddw r0, 0x1
  exit
{dataOk}:
  mov64 r5, r6
  add64 r5, ACC0_DATA
"
    else
      s!"\
  ldxdw r1, [r10 - {context.headerStack acc}]
  ldxdw r2, [r1 + 80]
  lddw r3, {requiredBytes}
  jge r2, r3, {dataOk}
  lddw r0, 0x1
  exit
{dataOk}:
  mov64 r5, r1
  add64 r5, 88
"
  return loadIndex ++ loadRoot ++ loadBump ++ account ++
    s!"\
  ; validate bounded acc{acc} parent path links={linksBaseWord} parent={parentBaseWord} stride={strideWords} capacity={capacity} depth={maxDepth}
  ; r7 remains the walked instruction-data base outside this intrinsic.
  stxdw [r10 - {stackOff + 32}], r7
  ldxdw r2, [r10 - {stackOff + 8}]
  ldxdw r3, [r10 - {stackOff + 16}]
  ldxdw r4, [r10 - {stackOff + 24}]
  jeq r4, 0, {failure}
  lddw r1, {capacity + 1}
  jgt r4, r1, {failure}
  jeq r3, 0, {failure}
  lddw r1, {capacity}
  jgt r3, r1, {failure}
  jge r3, r4, {failure}
  jeq r2, 0, {failure}
  jgt r2, r1, {failure}
  jge r2, r4, {failure}
  lddw r7, 0
{loop}:
  jeq r2, r3, {rootCheck}
  lddw r1, {maxDepth}
  jge r7, r1, {failure}
  mov64 r8, r2
  sub64 r8, 1
  lddw r1, {strideBytes}
  mul64 r8, r1
  mov64 r9, r5
  lddw r1, {parentBaseBytes}
  add64 r9, r1
  add64 r9, r8
  ldxdw r8, [r9 + 0]
  mov64 r9, r8
  rsh64 r8, 32
  jgt r8, 1, {failure}
  lsh64 r9, 32
  rsh64 r9, 32
  jeq r9, 0, {failure}
  lddw r1, {capacity}
  jgt r9, r1, {failure}
  jge r9, r4, {failure}
  jeq r9, r2, {failure}
  mov64 r1, r9
  sub64 r1, 1
  lddw r8, {strideBytes}
  mul64 r1, r8
  mov64 r8, r5
  lddw r0, {linksBaseBytes}
  add64 r8, r0
  add64 r8, r1
  ldxdw r8, [r8 + 0]
  mov64 r1, r8
  lsh64 r1, 32
  rsh64 r1, 32
  jeq r1, r2, {edgeOk}
  rsh64 r8, 32
  jne r8, r2, {failure}
{edgeOk}:
  mov64 r2, r9
  add64 r7, 1
  ja {loop}
{rootCheck}:
  mov64 r8, r3
  sub64 r8, 1
  lddw r1, {strideBytes}
  mul64 r8, r1
  mov64 r9, r5
  lddw r1, {parentBaseBytes}
  add64 r9, r1
  add64 r9, r8
  ldxdw r8, [r9 + 0]
  jeq r8, 0, {success}
  ja {failure}
{success}:
  lddw r1, 1
  stxdw [r10 - {stackOff}], r1
  ja {done}
{failure}:
  lddw r1, 0
  stxdw [r10 - {stackOff}], r1
{done}:
  ldxdw r7, [r10 - {stackOff + 32}]
"

/-- Validate every live node and every released slot in a fixed-capacity Sokoban allocator. The
tree walk is iterative and follows parent pointers. A fixed stack bitmap proves that live and free
indices are disjoint and exactly partition `[1, bumpIndex)`, without heap allocation or node copies. -/
private def emitFifoRbTreeValid (context : Context) (tree : FifoRbTree)
    (root size bumpIndex freeListHead : Ops.Val)
    (stackOff nonce : Nat) (scope : String) : Except String String := do
  let region := tree.links.region
  let acc := region.account
  let linksBaseWord := tree.links.firstWord
  let parentBaseWord := tree.parentColor.firstWord
  let keyBaseWord := tree.price.firstWord
  let sequenceBaseWord := tree.sequence.firstWord
  let strideWords := region.strideWords
  let capacity := region.capacity
  let bid := tree.bid
  let loadRoot ← context.loadValue root (stackOff + 8) (nonce + 1) (scope ++ "_root")
  let loadSize ← context.loadValue size (stackOff + 16) (nonce + 2) (scope ++ "_size")
  let loadBump ← context.loadValue bumpIndex (stackOff + 24) (nonce + 3) (scope ++ "_bump")
  let loadFree ← context.loadValue freeListHead (stackOff + 32) (nonce + 4) (scope ++ "_free")
  let strideBytes := 8 * strideWords
  let linksBaseBytes := 8 * linksBaseWord
  let parentBaseBytes := 8 * parentBaseWord
  let keyBaseBytes := 8 * keyBaseWord
  let sequenceBaseBytes := 8 * sequenceBaseWord
  let finalWord := Nat.max (Nat.max linksBaseWord parentBaseWord)
    (Nat.max keyBaseWord sequenceBaseWord) + strideWords * (capacity - 1)
  let requiredBytes := 8 * (finalWord + 1)
  let bitmapWords := (capacity + 63) / 64
  let clearBitmap := (List.range bitmapWords).foldl (init := "") fun text i =>
    text ++ s!"  stxdw [r9 + {8 * i}], r1\n"
  let token := IR.u64Hex (Core.IR.fnv1a64
    (s!"{scope}:{stackOff}:{nonce}:{acc}:{linksBaseWord}:{parentBaseWord}:{keyBaseWord}:" ++
      s!"{sequenceBaseWord}:{strideWords}:{capacity}:{bid}"))
  let dataOk := s!"rb_data_ok_{token}"
  let nonEmpty := s!"rb_nonempty_{token}"
  let startLive := s!"rb_start_live_{token}"
  let liveLoop := s!"rb_live_loop_{token}"
  let entered := s!"rb_entered_{token}"
  let enteredNonRoot := s!"rb_entered_nonroot_{token}"
  let enteredShape := s!"rb_entered_shape_{token}"
  let marked := s!"rb_marked_{token}"
  let sideOk := s!"rb_side_ok_{token}"
  let leftOk := s!"rb_left_ok_{token}"
  let leftColorOk := s!"rb_left_color_ok_{token}"
  let rightColorOk := s!"rb_right_color_ok_{token}"
  let leftNull := s!"rb_left_null_{token}"
  let leftBhSet := s!"rb_left_bh_set_{token}"
  let leftBhOk := s!"rb_left_bh_ok_{token}"
  let afterLeft := s!"rb_after_left_{token}"
  let visit := s!"rb_visit_{token}"
  let firstKey := s!"rb_first_key_{token}"
  let priceEqual := s!"rb_price_equal_{token}"
  let orderOk := s!"rb_order_ok_{token}"
  let storeKey := s!"rb_store_key_{token}"
  let rightNull := s!"rb_right_null_{token}"
  let rightBhSet := s!"rb_right_bh_set_{token}"
  let rightBhOk := s!"rb_right_bh_ok_{token}"
  let descendRight := s!"rb_descend_right_{token}"
  let afterRight := s!"rb_after_right_{token}"
  let ascend := s!"rb_ascend_{token}"
  let ascendBlack := s!"rb_ascend_black_{token}"
  let ascendMove := s!"rb_ascend_move_{token}"
  let afterLive := s!"rb_after_live_{token}"
  let startFree := s!"rb_start_free_{token}"
  let freeLoop := s!"rb_free_loop_{token}"
  let freeMarked := s!"rb_free_marked_{token}"
  let freeDone := s!"rb_free_done_{token}"
  let success := s!"rb_success_{token}"
  let failure := s!"rb_failure_{token}"
  let done := s!"rb_done_{token}"
  let sideCheck :=
    if bid then s!"  jne r1, 1, {failure}\n" else s!"  jne r1, 0, {failure}\n"
  let orderCheck :=
    if bid then
      s!"\
  jgt r1, r2, {orderOk}
  jne r1, r2, {failure}
  ja {priceEqual}
"
    else
      s!"\
  jlt r1, r2, {orderOk}
  jne r1, r2, {failure}
  ja {priceEqual}
"
  let sequenceCheck :=
    if bid then s!"  jgt r1, r2, {orderOk}\n" else s!"  jlt r1, r2, {orderOk}\n"
  let account :=
    if acc == 0 then
      s!"\
  ldxdw r1, [r6 + ACC0_DATA_LEN]
  lddw r2, {requiredBytes}
  jge r1, r2, {dataOk}
  lddw r0, 0x1
  exit
{dataOk}:
  mov64 r5, r6
  add64 r5, ACC0_DATA
"
    else
      s!"\
  ldxdw r1, [r10 - {context.headerStack acc}]
  ldxdw r2, [r1 + 80]
  lddw r3, {requiredBytes}
  jge r2, r3, {dataOk}
  lddw r0, 0x1
  exit
{dataOk}:
  mov64 r5, r1
  add64 r5, 88
"
  return loadRoot ++ loadSize ++ loadBump ++ loadFree ++ account ++
    s!"\
  ; complete account-resident RB tree and allocator validation
  ; links={linksBaseWord} parent={parentBaseWord} key={keyBaseWord} sequence={sequenceBaseWord} stride={strideWords} capacity={capacity} bid={bid}
  ldxdw r2, [r10 - {stackOff + 16}]
  lddw r1, {capacity}
  jgt r2, r1, {failure}
  ldxdw r4, [r10 - {stackOff + 24}]
  jeq r4, 0, {failure}
  lddw r1, {capacity + 1}
  jgt r4, r1, {failure}
  jge r2, r4, {failure}
  ldxdw r1, [r10 - {stackOff + 32}]
  jeq r1, 0, {failure}
  jgt r1, r4, {failure}
  ldxdw r3, [r10 - {stackOff + 8}]
  jne r2, 0, {nonEmpty}
  jne r3, 0, {failure}
  ja {startLive}
{nonEmpty}:
  jeq r3, 0, {failure}
  lddw r1, {capacity}
  jgt r3, r1, {failure}
  jge r3, r4, {failure}
{startLive}:
  ; The bitmap occupies only r10-4096 .. r10-3585 and is fully initialized here.
  mov64 r9, r10
  add64 r9, -{rbTreeBitmapScratch}
  lddw r1, 0
{clearBitmap}  lddw r1, 0
  stxdw [r10 - {stackOff + 40}], r1
  stxdw [r10 - {stackOff + 56}], r1
  stxdw [r10 - {stackOff + 64}], r1
  stxdw [r10 - {stackOff + 72}], r1
  stxdw [r10 - {stackOff + 80}], r1
  stxdw [r10 - {stackOff + 104}], r1
  stxdw [r10 - {stackOff + 48}], r3
  jeq r3, 0, {afterLive}
{liveLoop}:
  ldxdw r1, [r10 - {stackOff + 56}]
  add64 r1, 1
  stxdw [r10 - {stackOff + 56}], r1
  lddw r2, {3 * capacity}
  jgt r1, r2, {failure}
  ldxdw r2, [r10 - {stackOff + 48}]
  jeq r2, 0, {failure}
  ldxdw r4, [r10 - {stackOff + 24}]
  jge r2, r4, {failure}
  lddw r1, {capacity}
  jgt r2, r1, {failure}
  mov64 r8, r2
  sub64 r8, 1
  lddw r1, {strideBytes}
  mul64 r8, r1
  mov64 r9, r5
  lddw r1, {linksBaseBytes}
  add64 r9, r1
  add64 r9, r8
  ldxdw r1, [r9 + 0]
  mov64 r9, r1
  lsh64 r9, 32
  rsh64 r9, 32
  stxdw [r10 - {stackOff + 112}], r9
  rsh64 r1, 32
  stxdw [r10 - {stackOff + 120}], r1
  mov64 r9, r5
  lddw r1, {parentBaseBytes}
  add64 r9, r1
  add64 r9, r8
  ldxdw r1, [r9 + 0]
  stxdw [r10 - {stackOff + 128}], r1
  mov64 r9, r5
  lddw r1, {keyBaseBytes}
  add64 r9, r1
  add64 r9, r8
  ldxdw r1, [r9 + 0]
  stxdw [r10 - {stackOff + 136}], r1
  mov64 r9, r5
  lddw r1, {sequenceBaseBytes}
  add64 r9, r1
  add64 r9, r8
  ldxdw r1, [r9 + 0]
  stxdw [r10 - {stackOff + 144}], r1
  ldxdw r8, [r10 - {stackOff + 128}]
  mov64 r9, r8
  lsh64 r9, 32
  rsh64 r9, 32
  ldxdw r1, [r10 - {stackOff + 40}]
  jeq r1, r9, {entered}
  ldxdw r9, [r10 - {stackOff + 112}]
  jeq r1, r9, {afterLeft}
  ldxdw r9, [r10 - {stackOff + 120}]
  jeq r1, r9, {afterRight}
  ja {failure}
{entered}:
  mov64 r9, r8
  rsh64 r9, 32
  jgt r9, 1, {failure}
  ldxdw r3, [r10 - {stackOff + 8}]
  jne r2, r3, {enteredNonRoot}
  jne r8, 0, {failure}
  ja {enteredShape}
{enteredNonRoot}:
  mov64 r1, r8
  lsh64 r1, 32
  rsh64 r1, 32
  jeq r1, 0, {failure}
{enteredShape}:
  ; Mark this live index; a repeated entry proves a cycle or shared child.
  mov64 r8, r2
  sub64 r8, 1
  mov64 r9, r8
  and64 r9, 63
  lddw r0, 1
  lsh64 r0, r9
  rsh64 r8, 6
  lsh64 r8, 3
  mov64 r9, r10
  add64 r9, -{rbTreeBitmapScratch}
  add64 r9, r8
  ldxdw r8, [r9 + 0]
  mov64 r1, r8
  and64 r1, r0
  jne r1, 0, {failure}
  or64 r8, r0
  stxdw [r9 + 0], r8
{marked}:
  ldxdw r1, [r10 - {stackOff + 64}]
  add64 r1, 1
  stxdw [r10 - {stackOff + 64}], r1
  ldxdw r8, [r10 - {stackOff + 16}]
  jgt r1, r8, {failure}
  ldxdw r1, [r10 - {stackOff + 144}]
  rsh64 r1, 63
{sideCheck}{sideOk}:
  ; Black depth includes the current node while its subtrees are traversed.
  ldxdw r8, [r10 - {stackOff + 128}]
  rsh64 r8, 32
  jne r8, 0, {leftOk}
  ldxdw r1, [r10 - {stackOff + 72}]
  add64 r1, 1
  stxdw [r10 - {stackOff + 72}], r1
{leftOk}:
  ; Validate left child envelope, reciprocal parent, and the red rule.
  ldxdw r1, [r10 - {stackOff + 112}]
  jeq r1, 0, {leftNull}
  jeq r1, r2, {failure}
  ldxdw r4, [r10 - {stackOff + 24}]
  jge r1, r4, {failure}
  lddw r4, {capacity}
  jgt r1, r4, {failure}
  sub64 r1, 1
  lddw r4, {strideBytes}
  mul64 r1, r4
  mov64 r9, r5
  lddw r4, {parentBaseBytes}
  add64 r9, r4
  add64 r9, r1
  ldxdw r1, [r9 + 0]
  mov64 r4, r1
  rsh64 r4, 32
  jgt r4, 1, {failure}
  lsh64 r1, 32
  rsh64 r1, 32
  jne r1, r2, {failure}
  ldxdw r1, [r10 - {stackOff + 128}]
  rsh64 r1, 32
  jeq r1, 0, {leftColorOk}
  jne r4, 0, {failure}
{leftColorOk}:
  ldxdw r1, [r10 - {stackOff + 40}]
  stxdw [r10 - {stackOff + 40}], r2
  ldxdw r2, [r10 - {stackOff + 112}]
  stxdw [r10 - {stackOff + 48}], r2
  ja {liveLoop}
{leftNull}:
  ldxdw r1, [r10 - {stackOff + 72}]
  ldxdw r8, [r10 - {stackOff + 80}]
  jeq r8, 0, {leftBhSet}
  jne r1, r8, {failure}
  ja {leftBhOk}
{leftBhSet}:
  stxdw [r10 - {stackOff + 80}], r1
{leftBhOk}:
  ja {visit}
{afterLeft}:
  ja {visit}
{visit}:
  ; Strict Phoenix FIFO in-order key: bids descend, asks ascend.
  ldxdw r8, [r10 - {stackOff + 104}]
  jeq r8, 0, {firstKey}
  ldxdw r1, [r10 - {stackOff + 88}]
  ldxdw r2, [r10 - {stackOff + 136}]
{orderCheck}{priceEqual}:
  ldxdw r1, [r10 - {stackOff + 96}]
  ldxdw r2, [r10 - {stackOff + 144}]
{sequenceCheck}  ja {failure}
{orderOk}:
  ja {storeKey}
{firstKey}:
  lddw r8, 1
  stxdw [r10 - {stackOff + 104}], r8
{storeKey}:
  ldxdw r1, [r10 - {stackOff + 136}]
  stxdw [r10 - {stackOff + 88}], r1
  ldxdw r1, [r10 - {stackOff + 144}]
  stxdw [r10 - {stackOff + 96}], r1
  ldxdw r2, [r10 - {stackOff + 48}]
  ; Validate right child before descending.
  ldxdw r1, [r10 - {stackOff + 120}]
  jeq r1, 0, {rightNull}
  jeq r1, r2, {failure}
  ldxdw r4, [r10 - {stackOff + 24}]
  jge r1, r4, {failure}
  lddw r4, {capacity}
  jgt r1, r4, {failure}
  sub64 r1, 1
  lddw r4, {strideBytes}
  mul64 r1, r4
  mov64 r9, r5
  lddw r4, {parentBaseBytes}
  add64 r9, r4
  add64 r9, r1
  ldxdw r1, [r9 + 0]
  mov64 r4, r1
  rsh64 r4, 32
  jgt r4, 1, {failure}
  lsh64 r1, 32
  rsh64 r1, 32
  jne r1, r2, {failure}
  ldxdw r1, [r10 - {stackOff + 128}]
  rsh64 r1, 32
  jeq r1, 0, {rightColorOk}
  jne r4, 0, {failure}
{rightColorOk}:
  ja {descendRight}
{rightNull}:
  ldxdw r1, [r10 - {stackOff + 72}]
  ldxdw r8, [r10 - {stackOff + 80}]
  jeq r8, 0, {rightBhSet}
  jne r1, r8, {failure}
  ja {rightBhOk}
{rightBhSet}:
  stxdw [r10 - {stackOff + 80}], r1
{rightBhOk}:
  ja {ascend}
{descendRight}:
  stxdw [r10 - {stackOff + 40}], r2
  ldxdw r1, [r10 - {stackOff + 120}]
  stxdw [r10 - {stackOff + 48}], r1
  ja {liveLoop}
{afterRight}:
  ja {ascend}
{ascend}:
  ldxdw r2, [r10 - {stackOff + 48}]
  ldxdw r8, [r10 - {stackOff + 128}]
  mov64 r1, r8
  rsh64 r1, 32
  jne r1, 0, {ascendMove}
{ascendBlack}:
  ldxdw r1, [r10 - {stackOff + 72}]
  jeq r1, 0, {failure}
  sub64 r1, 1
  stxdw [r10 - {stackOff + 72}], r1
{ascendMove}:
  lsh64 r8, 32
  rsh64 r8, 32
  jeq r8, 0, {afterLive}
  stxdw [r10 - {stackOff + 40}], r2
  stxdw [r10 - {stackOff + 48}], r8
  ja {liveLoop}
{afterLive}:
  ldxdw r1, [r10 - {stackOff + 64}]
  ldxdw r2, [r10 - {stackOff + 16}]
  jne r1, r2, {failure}
  ; expected free slots = (bumpIndex - 1) - live size.
  ldxdw r4, [r10 - {stackOff + 24}]
  sub64 r4, 1
  sub64 r4, r2
  lddw r1, 0
  stxdw [r10 - {stackOff + 56}], r1
  ldxdw r2, [r10 - {stackOff + 32}]
  jne r4, 0, {startFree}
  ldxdw r1, [r10 - {stackOff + 24}]
  jeq r2, r1, {success}
  ja {failure}
{startFree}:
  ldxdw r1, [r10 - {stackOff + 24}]
  jeq r2, r1, {failure}
{freeLoop}:
  jeq r2, 0, {failure}
  ldxdw r1, [r10 - {stackOff + 24}]
  jge r2, r1, {failure}
  lddw r1, {capacity}
  jgt r2, r1, {failure}
  ; The shared bitmap rejects free cycles, duplicates, and live/free overlap.
  mov64 r8, r2
  sub64 r8, 1
  mov64 r9, r8
  and64 r9, 63
  lddw r0, 1
  lsh64 r0, r9
  rsh64 r8, 6
  lsh64 r8, 3
  mov64 r9, r10
  add64 r9, -{rbTreeBitmapScratch}
  add64 r9, r8
  ldxdw r8, [r9 + 0]
  mov64 r1, r8
  and64 r1, r0
  jne r1, 0, {failure}
  or64 r8, r0
  stxdw [r9 + 0], r8
{freeMarked}:
  ldxdw r1, [r10 - {stackOff + 56}]
  add64 r1, 1
  stxdw [r10 - {stackOff + 56}], r1
  jgt r1, r4, {failure}
  mov64 r8, r2
  sub64 r8, 1
  lddw r1, {strideBytes}
  mul64 r8, r1
  mov64 r9, r5
  lddw r1, {linksBaseBytes}
  add64 r9, r1
  add64 r9, r8
  ldxdw r2, [r9 + 0]
  lsh64 r2, 32
  rsh64 r2, 32
  jeq r2, 0, {failure}
  ldxdw r1, [r10 - {stackOff + 24}]
  jne r2, r1, {freeLoop}
{freeDone}:
  ldxdw r1, [r10 - {stackOff + 56}]
  jne r1, r4, {failure}
{success}:
  lddw r1, 1
  stxdw [r10 - {stackOff}], r1
  ja {done}
{failure}:
  lddw r1, 0
  stxdw [r10 - {stackOff}], r1
{done}:
"

def emitQuery (context : Context) (query : Query) (operands : Array Ops.Val)
    (stackOff nonce : Nat) (scope : String) : Except String String :=
  match query, operands with
  | .parentPathValid path, #[index, root, bumpIndex] =>
      emitParentPathValid context path index root bumpIndex stackOff nonce scope
  | .fifoRbTreeValid tree, #[root, size, bumpIndex, freeListHead] =>
      emitFifoRbTreeValid context tree root size bumpIndex freeListHead stackOff nonce scope
  | _, _ => .error "extract/ir: malformed account-storage query operands"

def emitCall (context : Context) (label : String) : Call Ops.Val → Except String String
  | .writeWord field index value => emitWriteWord context label field index value

end ProofForge.Svm.AccountStorage.Emit
