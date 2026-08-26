import ProofForge.Svm.IR

namespace ProofForge.Svm.AccountStorage.Emit

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

def emitQuery (context : Context) (query : Query) (operands : Array Ops.Val)
    (stackOff nonce : Nat) (scope : String) : Except String String :=
  match query, operands with
  | .parentPathValid path, #[index, root, bumpIndex] =>
      emitParentPathValid context path index root bumpIndex stackOff nonce scope
  | _, _ => .error "extract/ir: malformed account-storage query operands"

def emitCall (context : Context) (label : String) : Call Ops.Val → Except String String
  | .writeWord field index value => emitWriteWord context label field index value

end ProofForge.Svm.AccountStorage.Emit
