import ProofForge.Svm.AccountStorage
import ProofForge.Svm.Ops

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

def emitCall (context : Context) (label : String) : Call Ops.Val → Except String String
  | .writeWord field index value => emitWriteWord context label field index value

end ProofForge.Svm.AccountStorage.Emit
