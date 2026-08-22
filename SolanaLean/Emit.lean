import SolanaLean.IR
import SolanaLean.Ops

namespace SolanaLean.Emit

/-- 与 ProofForge StateCell / Loader V3 单账户布局对齐的常量。 -/
def discInit : String := "0x642858a76747495e"
def discIncrement : String := "0x223edbd10397c79d"
def discGet : String := "0x37dd90d6b076a2a4"
def layoutMarker : String := "0xbbe897f0336e6fc"
def overflowCode : String := "0x1001"

def emitCounterAsm (program : IR.Program) : Except String String := do
  unless IR.isCounterShape program do
    throw "extract/unsupported: not counter shape"
  let incrementOps :=
    (program.methods.find? (·.kind == .increment)).map (·.ops)
  match incrementOps with
  | some ops =>
    unless ops.isEmpty || Ops.hasCheckedAdd ops do
      throw "extract/unsupported: increment missing checkedAddU64"
  | none => throw "extract/unsupported: missing increment"
  return s!"\
; SOLANA-LEAN-SBPF-ASM v0 (Counter / Loader V3 single account)
; Layout matches ProofForge StateCell: header u64 + count u64
; Discriminators: initialize/increment/get (PF domain proof-forge-solana-v1)

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

initialize:
  ldxdw r1, [r6 + NUM_ACCOUNTS]
  jne r1, 1, err_check_initialize
  ldxb r1, [r6 + ACC0_HEADER + 0]
  jne r1, 0xff, err_check_initialize
  ldxdw r1, [r6 + INSTRUCTION_DATA_LEN]
  jne r1, 16, err_check_initialize
  ldxdw r1, [r6 + INSTRUCTION_DATA_LEN]
  mov64 r2, r6
  add64 r2, INSTRUCTION_DATA
  add64 r2, r1
  ldxdw r1, [r6 + ACC0_OWNER]
  ldxdw r3, [r2 + 0]
  jne r1, r3, err_check_initialize
  ldxdw r1, [r6 + ACC0_OWNER + 8]
  ldxdw r3, [r2 + 8]
  jne r1, r3, err_check_initialize
  ldxdw r1, [r6 + ACC0_OWNER + 16]
  ldxdw r3, [r2 + 16]
  jne r1, r3, err_check_initialize
  ldxdw r1, [r6 + ACC0_OWNER + 24]
  ldxdw r3, [r2 + 24]
  jne r1, r3, err_check_initialize
  ldxdw r1, [r6 + ACC0_DATA_LEN]
  jne r1, 16, err_check_initialize
  ldxb r1, [r6 + ACC0_HEADER + 1]
  jeq r1, 0, err_check_initialize
  ldxb r1, [r6 + ACC0_HEADER + 2]
  jeq r1, 0, err_check_initialize
  ldxdw r1, [r6 + ACC0_DATA + 0]
  lddw r2, 0x0
  jne r1, r2, err_check_initialize
  ja body_initialize
err_check_initialize:
  lddw r0, 0x1
  exit
body_initialize:
  lddw r1, 0
  stxdw [r6 + ACC0_DATA + 8], r1
  ldxdw r1, [r6 + INSTRUCTION_DATA + 8]
  stxdw [r10 - 8], r1
  ldxdw r1, [r10 - 8]
  stxdw [r6 + ACC0_DATA + 8], r1
  lddw r1, {layoutMarker}
  stxdw [r6 + ACC0_DATA + 0], r1
  lddw r0, 0
  exit

increment:
  ldxdw r1, [r6 + NUM_ACCOUNTS]
  jne r1, 1, err_check_increment
  ldxb r1, [r6 + ACC0_HEADER + 0]
  jne r1, 0xff, err_check_increment
  ldxdw r1, [r6 + INSTRUCTION_DATA_LEN]
  jne r1, 16, err_check_increment
  ldxdw r1, [r6 + INSTRUCTION_DATA_LEN]
  mov64 r2, r6
  add64 r2, INSTRUCTION_DATA
  add64 r2, r1
  ldxdw r1, [r6 + ACC0_OWNER]
  ldxdw r3, [r2 + 0]
  jne r1, r3, err_check_increment
  ldxdw r1, [r6 + ACC0_OWNER + 8]
  ldxdw r3, [r2 + 8]
  jne r1, r3, err_check_increment
  ldxdw r1, [r6 + ACC0_OWNER + 16]
  ldxdw r3, [r2 + 16]
  jne r1, r3, err_check_increment
  ldxdw r1, [r6 + ACC0_OWNER + 24]
  ldxdw r3, [r2 + 24]
  jne r1, r3, err_check_increment
  ldxdw r1, [r6 + ACC0_DATA_LEN]
  jne r1, 16, err_check_increment
  ldxb r1, [r6 + ACC0_HEADER + 2]
  jeq r1, 0, err_check_increment
  ldxdw r1, [r6 + ACC0_DATA + 0]
  lddw r2, {layoutMarker}
  jne r1, r2, err_check_increment
  ja body_increment
err_check_increment:
  lddw r0, 0x1
  exit
body_increment:
  ldxdw r1, [r6 + ACC0_DATA + 8]
  stxdw [r10 - 8], r1
  ldxdw r1, [r6 + INSTRUCTION_DATA + 8]
  stxdw [r10 - 16], r1
  ldxdw r1, [r10 - 8]
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

get:
  ldxdw r1, [r6 + NUM_ACCOUNTS]
  jne r1, 1, err_check_get
  ldxb r1, [r6 + ACC0_HEADER + 0]
  jne r1, 0xff, err_check_get
  ldxdw r1, [r6 + INSTRUCTION_DATA_LEN]
  jne r1, 8, err_check_get
  ldxdw r1, [r6 + INSTRUCTION_DATA_LEN]
  mov64 r2, r6
  add64 r2, INSTRUCTION_DATA
  add64 r2, r1
  ldxdw r1, [r6 + ACC0_OWNER]
  ldxdw r3, [r2 + 0]
  jne r1, r3, err_check_get
  ldxdw r1, [r6 + ACC0_OWNER + 8]
  ldxdw r3, [r2 + 8]
  jne r1, r3, err_check_get
  ldxdw r1, [r6 + ACC0_OWNER + 16]
  ldxdw r3, [r2 + 16]
  jne r1, r3, err_check_get
  ldxdw r1, [r6 + ACC0_OWNER + 24]
  ldxdw r3, [r2 + 24]
  jne r1, r3, err_check_get
  ldxdw r1, [r6 + ACC0_DATA_LEN]
  jne r1, 16, err_check_get
  ldxdw r1, [r6 + ACC0_DATA + 0]
  lddw r2, {layoutMarker}
  jne r1, r2, err_check_get
  ja body_get
err_check_get:
  lddw r0, 0x1
  exit
body_get:
  ldxdw r1, [r6 + ACC0_DATA + 8]
  stxdw [r10 - 8], r1
  ldxdw r1, [r10 - 8]
  stxdw [r10 - 16], r1
  mov64 r1, r10
  add64 r1, -16
  lddw r2, 8
  call sol_set_return_data
  lddw r0, 0
  exit
"

end SolanaLean.Emit
