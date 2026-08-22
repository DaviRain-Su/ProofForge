import SolanaLean.IR
import SolanaLean.Ops

namespace SolanaLean.Emit

def discInit : String := "0x642858a76747495e"
def discIncrement : String := "0x223edbd10397c79d"
def discGet : String := "0x37dd90d6b076a2a4"
def layoutMarker : String := "0xbbe897f0336e6fc"
def overflowCode : String := "0x1001"

/-- Loader V3 单账户预检。`ixLen` 是 instruction data 期望长度。 -/
private def prelude (label : String) (ixLen : Nat) (needSigner needWritable needUninit : Bool) :
    String :=
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
      s!"  ldxdw r1, [r6 + ACC0_DATA + 0]\n  lddw r2, {layoutMarker}\n  jne r1, r2, {err}\n"
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
  jne r1, 16, {err}
{signer}{writable}{header}  ja body_{label}
{err}:
  lddw r0, 0x1
  exit
"

/-- `.field _ "value"` 是账户 count；`.arg _` 是 instruction 里第一个 u64。 -/
private def memOfVal (v : Ops.Val) : Except String String :=
  match v with
  | .field _ "value" => .ok "[r6 + ACC0_DATA + 8]"
  | .arg _ => .ok "[r6 + INSTRUCTION_DATA + 8]"
  | .add .. => .error "extract/unsupported: cannot load add"
  | .subFromMax .. => .error "extract/unsupported: cannot load subFromMax"
  | .field _ name => .error s!"extract/unsupported: unknown field {name}"

private def loadVal (v : Ops.Val) (stackOff : Nat) : Except String String := do
  let mem ← memOfVal v
  return s!"  ; load {repr v}\n  ldxdw r1, {mem}\n  stxdw [r10 - {stackOff}], r1\n"

private def emitInitBody (v : Ops.Val) : Except String String := do
  let load ← loadVal v 8
  return s!"\
body_initialize:
  lddw r1, 0
  stxdw [r6 + ACC0_DATA + 8], r1
{load}  ldxdw r1, [r10 - 8]
  stxdw [r6 + ACC0_DATA + 8], r1
  lddw r1, {layoutMarker}
  stxdw [r6 + ACC0_DATA + 0], r1
  lddw r0, 0
  exit
"

private def emitCheckedAddBody (lhs rhs : Ops.Val) : Except String String := do
  let loadL ← loadVal lhs 8
  let loadR ← loadVal rhs 16
  return s!"\
body_increment:
{loadL}{loadR}  ldxdw r1, [r10 - 8]
  ldxdw r2, [r10 - 16]
  lddw r3, 0xffffffffffffffff
  sub64 r3, r2
  jgt r1, r3, err_add_0
  mov64 r4, r1
  add64 r4, r2
  stxdw [r10 - 24], r4
  ja ok_add_1
err_add_0:
  lddw r0, {overflowCode}
  exit
ok_add_1:
  ldxdw r1, [r10 - 24]
  stxdw [r6 + ACC0_DATA + 8], r1
  ldxdw r1, [r6 + ACC0_DATA + 8]
  stxdw [r10 - 8], r1
  ldxdw r1, [r10 - 8]
  stxdw [r10 - 32], r1
  mov64 r1, r10
  add64 r1, -32
  lddw r2, 8
  call sol_set_return_data
  lddw r0, 0
  exit
"

private def emitGetBody (v : Ops.Val) : Except String String := do
  let load ← loadVal v 8
  return s!"\
body_get:
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

private def addArgs (ops : Array Ops.Op) : Except String (Ops.Val × Ops.Val) :=
  match ops.findSome? (fun | .checkedAddU64 l r => some (l, r) | _ => none) with
  | some p => .ok p
  | none => .error "extract/unsupported: increment missing checkedAddU64"

private def hasReturnState (ops : Array Ops.Op) : Bool :=
  ops.any (fun | .returnState _ => true | _ => false)

private def hasErrorOverflow (ops : Array Ops.Op) : Bool :=
  ops.any (fun | .errorOverflow => true | _ => false)

private def hasOkState (ops : Array Ops.Op) : Bool :=
  ops.any (fun | .okState _ => true | _ => false)

private def hasReturnU64 (ops : Array Ops.Op) : Bool :=
  ops.any (fun | .returnU64 _ => true | _ => false)

private def emitHandler (m : IR.Method) : Except String String := do
  match m.kind with
  | .init =>
    let v ← initVal m.ops
    let body ← emitInitBody v
    return s!"initialize:\n{prelude "initialize" 16 true true true}{body}"
  | .increment =>
    if !Ops.hasCheckedAdd m.ops then
      .error "extract/unsupported: increment missing checkedAddU64"
    else if !hasErrorOverflow m.ops then
      .error "extract/unsupported: increment missing errorOverflow"
    else if !hasOkState m.ops then
      .error "extract/unsupported: increment missing okState"
    else do
      let (lhs, rhs) ← addArgs m.ops
      let body ← emitCheckedAddBody lhs rhs
      return s!"increment:\n{prelude "increment" 16 false true false}{body}"
  | .get =>
    let v ← getVal m.ops
    let body ← emitGetBody v
    return s!"get:\n{prelude "get" 8 false false false}{body}"

def emitCounterAsm (program : IR.Program) : Except String String := do
  unless IR.isCounterShape program do
    throw "extract/unsupported: not counter shape"
  let mut handlers := ""
  for m in program.methods do
    handlers := handlers ++ (← emitHandler m) ++ "\n"
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
.equ EXACT_DATA_LEN, 0x10
.equ ACC0_RENT_EPOCH, 0x2870
.equ INSTRUCTION_DATA_LEN, 0x2878
.equ INSTRUCTION_DATA, 0x2880

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
dispatch_begin:
  ldxdw r1, [r6 + INSTRUCTION_DATA]
  lddw r2, {discInit}
  jne r1, r2, dispatch_next_initialize
  call initialize
  exit
dispatch_next_initialize:
  lddw r2, {discIncrement}
  jne r1, r2, dispatch_next_increment
  call increment
  exit
dispatch_next_increment:
  lddw r2, {discGet}
  jne r1, r2, dispatch_next_get
  call get
  exit
dispatch_next_get:
  lddw r0, 1
  exit

{handlers}"

end SolanaLean.Emit
