import SolanaLean.IR
import SolanaLean.Ops

namespace SolanaLean.Emit

def overflowCode : String := "0x1001"

private def handlerLabel (m : IR.Method) : String :=
  if m.ixName != "" then m.ixName else IR.ixNameOfLean (IR.lastName m.name)

private def ixLenOf (m : IR.Method) : Nat :=
  match m.kind with
  | .get => 8
  | _ => 16

/-- Loader V3 单账户预检。`ixLen` 是 instruction data 期望长度。 -/
private def prelude (p : IR.Program) (marker : String) (label : String) (ixLen : Nat)
    (needSigner needWritable needUninit : Bool) : String :=
  let dataLen := IR.dataLen p
  let err := s!"err_check_{label}"
  let signer :=
    if needSigner then
      s!"  ldxb r1, [r6 + ACC0_HEADER + 1]\n  jeq r1, 0, {err}\n"
    else ""
  let writable :=
    if needWritable then
      s!"  ldxb r1, [r6 + ACC0_HEADER + 2]\n  jeq r1, 0, {err}\n"
    else ""
  let header :=
    if needUninit then
      s!"  ldxdw r1, [r6 + ACC0_DATA + 0]\n  lddw r2, 0x0\n  jne r1, r2, {err}\n"
    else
      s!"  ldxdw r1, [r6 + ACC0_DATA + 0]\n  lddw r2, {marker}\n  jne r1, r2, {err}\n"
  s!"\
  ldxdw r1, [r6 + NUM_ACCOUNTS]
  jne r1, 1, {err}
  ldxb r1, [r6 + ACC0_HEADER + 0]
  jne r1, 0xff, {err}
  ldxdw r1, [r6 + INSTRUCTION_DATA_LEN]
  jne r1, {ixLen}, {err}
  ldxdw r1, [r6 + INSTRUCTION_DATA_LEN]
  mov64 r2, r6
  add64 r2, INSTRUCTION_DATA
  add64 r2, r1
  ldxdw r1, [r6 + ACC0_OWNER]
  ldxdw r3, [r2 + 0]
  jne r1, r3, {err}
  ldxdw r1, [r6 + ACC0_OWNER + 8]
  ldxdw r3, [r2 + 8]
  jne r1, r3, {err}
  ldxdw r1, [r6 + ACC0_OWNER + 16]
  ldxdw r3, [r2 + 16]
  jne r1, r3, {err}
  ldxdw r1, [r6 + ACC0_OWNER + 24]
  ldxdw r3, [r2 + 24]
  jne r1, r3, {err}
  ldxdw r1, [r6 + ACC0_DATA_LEN]
  jne r1, {dataLen}, {err}
{signer}{writable}{header}  ja body_{label}
{err}:
  lddw r0, 0x1
  exit
"

/-- `.field _ name` 按 `Program.fields` 顺序映射到 header 之后的槽。 -/
private def memOfVal (p : IR.Program) (v : Ops.Val) : Except String String :=
  match v with
  | .field _ name =>
    match IR.fieldOffset p name with
    | some off => .ok s!"[r6 + ACC0_DATA + {off}]"
    | none => .error s!"extract/unsupported: unknown field {name}"
  | .arg _ =>
    .ok "[r6 + INSTRUCTION_DATA + 8]"
  | .lit _ => .error "extract/unsupported: lit has no mem"

private def loadVal (p : IR.Program) (v : Ops.Val) (stackOff : Nat) : Except String String :=
  match v with
  | .lit n =>
    .ok s!"  ; load lit {n}\n  lddw r1, {n.toNat}\n  stxdw [r10 - {stackOff}], r1\n"
  | _ => do
    let mem ← memOfVal p v
    return s!"  ; load {repr v}\n  ldxdw r1, {mem}\n  stxdw [r10 - {stackOff}], r1\n"

private def storeField (p : IR.Program) (name : String) (fromStack : Nat) : Except String String :=
  match IR.fieldOffset p name with
  | none => .error s!"extract/unsupported: unknown field {name}"
  | some off =>
    .ok s!"  ldxdw r1, [r10 - {fromStack}]\n  stxdw [r6 + ACC0_DATA + {off}], r1\n"

private def emitInitBody (p : IR.Program) (marker : String) (v : Ops.Val) : Except String String := do
  let load ← loadVal p v 8
  let store ←
    match p.fields[0]? with
    | some name => storeField p name 8
    | none => .error "extract/unsupported: no fields"
  let mut zeroOthers := ""
  for name in p.fields[1:] do
    match IR.fieldOffset p name with
    | some off =>
      zeroOthers := zeroOthers ++ s!"  lddw r1, 0\n  stxdw [r6 + ACC0_DATA + {off}], r1\n"
    | none => pure ()
  return s!"\
body_initialize:
{zeroOthers}{load}{store}  lddw r1, {marker}
  stxdw [r6 + ACC0_DATA + 0], r1
  lddw r0, 0
  exit
"

private def emitCheckedArithBody (p : IR.Program) (label : String) (lhs rhs : Ops.Val) (isAdd : Bool) :
    Except String String := do
  let loadL ← loadVal p lhs 8
  let loadR ← loadVal p rhs 16
  let destName :=
    match lhs with
    | .field _ n => n
    | _ => p.fields[0]?.getD "value"
  let store ← storeField p destName 24
  let arith :=
    if isAdd then
      s!"  lddw r3, 0xffffffffffffffff\n  sub64 r3, r2\n  jgt r1, r3, err_{label}\n  mov64 r4, r1\n  add64 r4, r2\n"
    else
      s!"  jlt r1, r2, err_{label}\n  mov64 r4, r1\n  sub64 r4, r2\n"
  return s!"\
body_{label}:
{loadL}{loadR}  ldxdw r1, [r10 - 8]
  ldxdw r2, [r10 - 16]
{arith}  stxdw [r10 - 24], r4
  ja ok_{label}
err_{label}:
  lddw r0, {overflowCode}
  exit
ok_{label}:
{store}  ldxdw r1, [r10 - 24]
  stxdw [r10 - 32], r1
  mov64 r1, r10
  add64 r1, -32
  lddw r2, 8
  call sol_set_return_data
  lddw r0, 0
  exit
"

private def emitGetBody (p : IR.Program) (label : String) (v : Ops.Val) : Except String String := do
  let load ← loadVal p v 8
  return s!"\
body_{label}:
{load}  ldxdw r1, [r10 - 8]
  stxdw [r10 - 16], r1
  mov64 r1, r10
  add64 r1, -16
  lddw r2, 8
  call sol_set_return_data
  lddw r0, 0
  exit
"

private def initVal (ops : Array Ops.Op) : Except String Ops.Val :=
  match ops.findSome? (fun | .returnState v => some v | _ => none) with
  | some v => .ok v
  | none => .error "extract/unsupported: init missing returnState"

private def getVal (ops : Array Ops.Op) : Except String Ops.Val :=
  match ops.findSome? (fun | .returnU64 v => some v | _ => none) with
  | some v => .ok v
  | none => .error "extract/unsupported: get missing returnU64"

private def arithArgs (ops : Array Ops.Op) : Except String (Ops.Val × Ops.Val × Bool) :=
  match ops.findSome? (fun
    | .checkedAddU64 l r => some (l, r, true)
    | .checkedSubU64 l r => some (l, r, false)
    | _ => none) with
  | some p => .ok p
  | none => .error "extract/unsupported: increment missing checked arith"

private def hasReturnState (ops : Array Ops.Op) : Bool :=
  ops.any (fun | .returnState _ => true | _ => false)

private def hasErrorOverflow (ops : Array Ops.Op) : Bool :=
  ops.any (fun | .errorOverflow => true | _ => false)

private def hasOkState (ops : Array Ops.Op) : Bool :=
  ops.any (fun | .okState _ => true | _ => false)

private def hasReturnU64 (ops : Array Ops.Op) : Bool :=
  ops.any (fun | .returnU64 _ => true | _ => false)

private def emitHandler (p : IR.Program) (marker : String) (m : IR.Method) : Except String String := do
  let label := handlerLabel m
  match m.kind with
  | .init =>
    let v ← initVal m.ops
    let body ← emitInitBody p marker v
    return s!"{label}:\n{prelude p marker label (ixLenOf m) true true true}{body}"
  | .increment =>
    if !Ops.hasCheckedArith m.ops then
      .error "extract/unsupported: increment missing checked arith"
    else if !hasErrorOverflow m.ops then
      .error "extract/unsupported: increment missing errorOverflow"
    else if !hasOkState m.ops then
      .error "extract/unsupported: increment missing okState"
    else do
      let (lhs, rhs, isAdd) ← arithArgs m.ops
      let body ← emitCheckedArithBody p label lhs rhs isAdd
      return s!"{label}:\n{prelude p marker label (ixLenOf m) false true false}{body}"
  | .get =>
    let v ← getVal m.ops
    let body ← emitGetBody p label v
    return s!"{label}:\n{prelude p marker label (ixLenOf m) false false false}{body}"

private def emitDispatch (program : IR.Program) : Except String String := do
  if program.methods.isEmpty then
    throw "extract/unsupported: no methods"
  let mut out := "dispatch_begin:\n  ldxdw r1, [r6 + INSTRUCTION_DATA]\n"
  for i in [0:program.methods.size] do
    let m := program.methods[i]!
    let label := handlerLabel m
    let disc ← IR.discHex label m.kind
    let next :=
      if i + 1 == program.methods.size then "err_unknown_disc"
      else s!"dispatch_next_{label}"
    if i == 0 then
      out := out ++ s!"  lddw r2, {disc}\n  jne r1, r2, {next}\n  call {label}\n  exit\n"
    else
      out := out ++ s!"dispatch_next_{handlerLabel program.methods[i - 1]!}:\n  lddw r2, {disc}\n  jne r1, r2, {next}\n  call {label}\n  exit\n"
  return out

def emitCounterAsm (program : IR.Program) : Except String String := do
  unless IR.isCounterShape program do
    throw "extract/unsupported: not counter shape"
  let marker ← IR.layoutMarkerHex program
  let layout := IR.inputLayout program
  let dispatch ← emitDispatch program
  let mut handlers := ""
  for m in program.methods do
    handlers := handlers ++ (← emitHandler program marker m) ++ "\n"
  return s!"\
; SOLANA-LEAN-SBPF-ASM v0 (ops-driven handler bodies)
; Layout matches ProofForge StateCell: header u64 + count u64

.equ NUM_ACCOUNTS, 0x0
.equ ACC0_HEADER, 0x8
.equ ACC0_KEY, 0x10
.equ ACC0_OWNER, 0x30
.equ ACC0_LAMPORTS, 0x50
.equ ACC0_DATA_LEN, 0x58
.equ ACC0_DATA, 0x60
.equ MAX_PERMITTED_DATA_INCREASE, 0x2800
.equ EXACT_DATA_LEN, {IR.dataLen program}
.equ ACC0_RENT_EPOCH, {layout.rentEpoch}
.equ INSTRUCTION_DATA_LEN, {layout.instructionDataLen}
.equ INSTRUCTION_DATA, {layout.instructionData}

.globl entrypoint

entrypoint:
  mov64 r6, r1
  ldxdw r1, [r6 + NUM_ACCOUNTS]
  jne r1, 1, err_unknown_disc
  ldxb r1, [r6 + ACC0_HEADER + 0]
  jne r1, 0xff, err_unknown_disc
  ldxdw r1, [r6 + INSTRUCTION_DATA_LEN]
  jlt r1, 8, err_unknown_disc
  ja dispatch_begin
err_unknown_disc:
  lddw r0, 1
  exit
{dispatch}
{handlers}"

end SolanaLean.Emit
