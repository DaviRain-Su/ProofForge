import ProofForge.Svm.IR

namespace ProofForge.Svm.Emit

def overflowCode : String := "0x1001"

/-- Deep scratch stays clear of expression temporaries, walk headers, scalar locals, and CPI data. -/
private def sysvarScratch : Nat := 3072
private def sysvarProgramIdScratch : Nat := 3104
/-- Heterogeneous PDA discovery may need 480 seed bytes, 15 descriptors, and a 32-byte result.
It reuses the bottom of the frame with sysvar scratch, whose contents are never live across the
PDA syscall, and stays disjoint from the CPI scratch rooted at `r10-2048`. -/
private def pdaSeedsScratch : Nat := 4096
/-- Whole-tree validation reuses the bottom 512 bytes after all operand expressions have been
loaded. It makes no syscalls, so this fixed bitmap never overlaps live PDA/sysvar scratch. -/
private def rbTreeBitmapScratch : Nat := 4096
/-- Four-word-key trees reach 8321 slots. Their 1048-byte bitmap and 512-byte traversal stack
remain disjoint in the bottom half of the fixed 4096-byte SVM frame. -/
private def rbTreeKey4BitmapScratch : Nat := 4096
private def rbTreeKey4TraversalScratch : Nat := 3000
private def rbTreeKey4TraversalDepth : Nat := 64
/-- Loop control must not overlap expression temporaries (8..), scalar locals (320..), or
walked-account headers (512..). -/
private def loopCounterScratch : Nat := 304

private def handlerLabel (m : IR.Method) : String :=
  if m.ixName != "" then m.ixName else IR.ixNameOfLean (IR.lastName m.name)

private def ixLenOf (m : IR.Method) : Nat :=
  8 + 8 * m.paramCount

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

/-- 与 PF caller.s 相同：r5 = header+88+len+10240+align8(len)；读 rent；+8 下一 marker。 -/
private def emitSkipAccount (tag : String) : String :=
  s!"\
  mov64 r5, r8
  add64 r5, 88
  add64 r5, r4
  add64 r5, MAX_PERMITTED_DATA_INCREASE
  mov64 r1, r4
  and64 r1, 7
  jeq r1, 0, walk_al_{tag}
  lddw r3, 8
  sub64 r3, r1
  add64 r5, r3
walk_al_{tag}:
  ldxdw r1, [r5 + 0]
  add64 r5, 8
  mov64 r8, r5
"

/-- Account headers live above expression temporaries and scalar locals. The instruction-data
length pointer follows the final account header. -/
private def headerStack (i : Nat) : Nat :=
  512 + 8 * i

/-- Keep the first 24 scalar locals in the legacy compact window. Additional locals live above
the walked-account headers (at most 64) and below CPI scratch, so they remain live across invokes
without overlapping expression temporaries or account traversal state. -/
private def scalarLocalStackOff (p : IR.Program) (i : Nat) : Option Nat :=
  let offset :=
    if i < 24 then 320 + i * 8
    else max 1024 (headerStack (IR.cpiAccountCount p) + 8) + (i - 24) * 8
  if offset < 2048 then some offset else none

private def emitWalkAccounts (n : Nat) (tag err : String) : String :=
  Id.run do
    let mut out := "  mov64 r8, r6\n  add64 r8, 8\n"
    for i in [0:n] do
      out := out ++ s!"\
  ldxb r1, [r8 + 0]
  jne r1, 0xff, {err}
  stxdw [r10 - {headerStack i}], r8
  ldxdw r4, [r8 + 80]
{emitSkipAccount s!"{i}_{tag}"}"
    out ++ s!"  stxdw [r10 - {headerStack n}], r8\n"

private partial def walkInvokeMetas (ops : Array IR.Op)
    (acc : Array (Ops.CpiMeta × Bool)) : Array (Ops.CpiMeta × Bool) :=
  ops.foldl (init := acc) fun a op =>
    match op with
    | .invoke _ metas _ seeds _ => a ++ metas.map (·, !seeds.isEmpty)
    | .ite _ _ _ t f => walkInvokeMetas f (walkInvokeMetas t a)
    | .forBody _ body => walkInvokeMetas body a
    | _ => a

/-- State is writable (and signer for init); CPI-account flags are checked on physical index +1. -/
private def emitCpiFlagChecks (ops : Array IR.Op) (err : String) (stateSigner : Bool) : String :=
  let metas := walkInvokeMetas ops #[]
  let extra := Id.run do
    let mut seen : Array Nat := #[0]
    let mut out := ""
    for (m, seeded) in metas do
      let physical := m.acc + 1
      unless seen.any (· == physical) do
        seen := seen.push physical
        if m.writable then
          out := out ++
            s!"  ldxdw r8, [r10 - {headerStack physical}]\n  ldxb r1, [r8 + 2]\n  jeq r1, 0, {err}\n"
        -- PDA 用 seeds 签内层，不能要求外层 is_signer。
        if m.signer && !seeded then
          out := out ++
            s!"  ldxdw r8, [r10 - {headerStack physical}]\n  ldxb r1, [r8 + 1]\n  jeq r1, 0, {err}\n"
    return out
  let signer :=
    if stateSigner then s!"  ldxb r1, [r8 + 1]\n  jeq r1, 0, {err}\n" else ""
  s!"\
  ldxdw r8, [r10 - {headerStack 0}]
{signer}  ldxb r1, [r8 + 2]
  jeq r1, 0, {err}
{extra}"

/-- walk 入口要查 `is_signer` 的账户下标。 -/
private def valSignerAccs : Ops.Val → Array Nat
  | .ext .signerKey0 _ => #[0]
  | .ext (.signerKeyN a) _ => #[a]
  | .ext _ operands => operands.flatMap valSignerAccs
  | .field b _ => valSignerAccs b
  | .bitAnd l r | .bitOr l r | .bitXor l r | .shiftL l r | .shiftR l r
  | .addU64 l r | .subU64 l r | .mulU64 l r | .divU64 l r | .modU64 l r
      => valSignerAccs l ++ valSignerAccs r
  | .bitNot v => valSignerAccs v
  | .indexGet b _ i _ _ => valSignerAccs b ++ valSignerAccs i
  | .select _ l r t f =>
      valSignerAccs l ++ valSignerAccs r ++ valSignerAccs t ++ valSignerAccs f
  | _ => #[]

private partial def walkSignerAccs (ops : Array IR.Op) : Array Nat :=
  ops.foldl (init := #[]) fun acc op =>
      let here :=
        match op with
        | .letLocal _ v => valSignerAccs v
        | .joinLocal _ => #[]
        | .setLocal _ v => valSignerAccs v
        | .checkedAddU64 l r | .checkedSubU64 l r | .checkedMulU64 l r
        | .checkedDivU64 l r | .checkedModU64 l r | .ite _ l r _ _ =>
            valSignerAccs l ++ valSignerAccs r
        | .invoke _ _ data _ bump =>
            (data.flatMap fun word => word.value?.map valSignerAccs |>.getD #[]) ++
              (match bump with | some v => valSignerAccs v | none => #[])
        | .accDataWordSetAt _ _ _ _ index value =>
            valSignerAccs index ++ valSignerAccs value
        | .accDataRbTreeKey4Insert _ _ _ _ _ _ _ key0 key1 key2 key3 =>
            #[key0, key1, key2, key3].flatMap valSignerAccs
        | .okState v | .returnU64 v | .returnState v | .storeField _ v => valSignerAccs v
        | .errorOverflow | .errorNamed _ => #[]
        | .forAccum _ v _ => valSignerAccs v
        | .forBody _ _ => #[]
        | .indexSet _ i v _ _ => valSignerAccs i ++ valSignerAccs v
      let nested :=
        match op with
        | .ite _ _ _ t f => walkSignerAccs t ++ walkSignerAccs f
        | .forBody _ body => walkSignerAccs body
        | _ => #[]
      acc ++ here ++ nested

private def emitWalkSignerChecks (ops : Array IR.Op) (err : String) : String :=
  let accs := walkSignerAccs ops
  Id.run do
    let mut seen : Array Nat := #[]
    let mut out := ""
    for a in accs do
      unless seen.any (· == a) do
        seen := seen.push a
        out := out ++
          s!"  ldxdw r8, [r10 - {headerStack a}]\n  ldxb r1, [r8 + 1]\n  jeq r1, 0, {err}\n"
    return out

private def emitWalkStateChecks (p : IR.Program) (marker : String) (ixLen : Nat)
    (err : String) (needUninit : Bool) : String :=
  let expectedMarker := if needUninit then "0x0" else marker
  s!"\
  ; validate walked state account owner, data length, and layout marker
  ldxdw r8, [r10 - {headerStack 0}]
  ldxdw r7, [r10 - {headerStack (IR.cpiAccountCount p)}]
  mov64 r2, r7
  add64 r2, {8 + ixLen}
  ldxdw r1, [r8 + 40]
  ldxdw r3, [r2 + 0]
  jne r1, r3, {err}
  ldxdw r1, [r8 + 48]
  ldxdw r3, [r2 + 8]
  jne r1, r3, {err}
  ldxdw r1, [r8 + 56]
  ldxdw r3, [r2 + 16]
  jne r1, r3, {err}
  ldxdw r1, [r8 + 64]
  ldxdw r3, [r2 + 24]
  jne r1, r3, {err}
  ldxdw r1, [r8 + 80]
  jne r1, {IR.dataLen p}, {err}
  ldxdw r1, [r8 + 88]
  lddw r2, {expectedMarker}
  jne r1, r2, {err}
"

/-- Walk N account headers and authenticate account 0 as ProofForge state. -/
private def preludeWalk (p : IR.Program) (marker label : String) (ixLen : Nat)
    (needUninit : Bool) (ops : Array IR.Op := #[]) : String :=
  let err := s!"err_check_{label}"
  let n := IR.cpiAccountCount p
  s!"\
  ldxdw r1, [r6 + NUM_ACCOUNTS]
  jlt r1, {n}, {err}
{emitWalkAccounts n label err}  ldxdw r1, [r10 - {headerStack n}]
  ldxdw r1, [r1 + 0]
  jne r1, {ixLen}, {err}
{emitWalkStateChecks p marker ixLen err needUninit}{emitWalkSignerChecks ops err}  ja body_{label}
{err}:
  lddw r0, 0x1
  exit
"

/-- CPI prelude: authenticated walked state plus account-meta flags. -/
private def preludeCpi (p : IR.Program) (marker label : String) (ixLen : Nat)
    (needUninit : Bool) (ops : Array IR.Op) : String :=
  let err := s!"err_check_{label}"
  let n := IR.cpiAccountCount p
  s!"\
  ldxdw r1, [r6 + NUM_ACCOUNTS]
  jlt r1, {n}, {err}
{emitWalkAccounts n label err}  ldxdw r1, [r10 - {headerStack n}]
  ldxdw r1, [r1 + 0]
  jne r1, {ixLen}, {err}
{emitWalkStateChecks p marker ixLen err needUninit}{emitCpiFlagChecks ops err needUninit}  ja body_{label}
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
  | .arg i =>
    if IR.usesWalk p then
      .ok s!"[r7 + {8 + 8 * i}]"
    else
      .ok s!"[r6 + INSTRUCTION_DATA + {8 + 8 * i}]"
  | .ext _ _ => .error "extract/unsupported: runtime leaf has no mem"
  | _ => .error "extract/unsupported: runtime leaf has no mem"

private def loadInsn (width : Nat) : Except String String :=
  match width with
  | 1 => .ok "ldxb"
  | 2 => .ok "ldxh"
  | 4 => .ok "ldxw"
  | 8 => .ok "ldxdw"
  | n => .error s!"extract/unsupported: load width {n}"

private def storeInsn (width : Nat) : Except String String :=
  match width with
  | 1 => .ok "stxb"
  | 2 => .ok "stxh"
  | 4 => .ok "stxw"
  | 8 => .ok "stxdw"
  | n => .error s!"extract/unsupported: store width {n}"

private def widthOfVal (p : IR.Program) (v : Ops.Val) : Nat :=
  match v with
  | .field _ name => (IR.fieldWidth p name).getD 8
  | _ => 8

/-- Keep assembly comments byte-stable while the legacy public adapter is phased out. -/
private partial def sourceValRepr : Ops.Val → String
  | .arg i => s!"ProofForge.Ops.Val.arg {i}"
  | .field base name => s!"ProofForge.Ops.Val.field ({sourceValRepr base}) {repr name}"
  | value => reprStr value

/-- Clock 是 40 字节 `repr(C)`；`slot` 在 0，`epoch` 在 16。 -/
private def emitLoadClockField (field : String) (off stackOff : Nat) (scope : String) : String :=
  s!"\
  ; load clock.{field} via sol_get_clock_sysvar
  mov64 r1, r10
  add64 r1, -{sysvarScratch}
  call sol_get_clock_sysvar
  jeq r0, 0, clock_{field}_ok_{scope}_{stackOff}
  lddw r0, 0x1
  exit
clock_{field}_ok_{scope}_{stackOff}:
  ldxdw r1, [r10 - {sysvarScratch - off}]
  stxdw [r10 - {stackOff}], r1
"

private def emitLoadClockSlot (stackOff : Nat) (scope : String) : String :=
  emitLoadClockField "slot" 0 stackOff scope

private def emitLoadClockEpoch (stackOff : Nat) (scope : String) : String :=
  emitLoadClockField "epoch" 16 stackOff scope

private def emitLoadUnixTime (stackOff : Nat) (scope : String) : String :=
  emitLoadClockField "unix" 32 stackOff scope

/-- EpochSchedule 是 33 字节 `repr(C)`；`slots_per_epoch` 在偏移 0。 -/
private def emitLoadSlotsPerEpoch (stackOff : Nat) (scope : String) : String :=
  s!"\
  ; load slotsPerEpoch via sol_get_epoch_schedule_sysvar
  mov64 r1, r10
  add64 r1, -{sysvarScratch}
  call sol_get_epoch_schedule_sysvar
  jeq r0, 0, epoch_ok_{scope}_{stackOff}
  lddw r0, 0x1
  exit
epoch_ok_{scope}_{stackOff}:
  ldxdw r1, [r10 - {sysvarScratch}]
  stxdw [r10 - {stackOff}], r1
"

/-- 最近一次 CPI 的 8 字节返回。长度不是 8 则 Custom(1)。 -/
private def emitLoadCpiReturn (stackOff : Nat) (scope : String) : String :=
  s!"\
  ; load cpiReturn via sol_get_return_data
  mov64 r1, r10
  add64 r1, -{sysvarScratch}
  lddw r2, 8
  mov64 r3, r10
  add64 r3, -{sysvarProgramIdScratch}
  call sol_get_return_data
  jeq r0, 8, cpi_ret_ok_{scope}_{stackOff}
  lddw r0, 0x1
  exit
cpi_ret_ok_{scope}_{stackOff}:
  ldxdw r1, [r10 - {sysvarScratch}]
  stxdw [r10 - {stackOff}], r1
"

/-- Rent 是 17 字节 `repr(C)`；rate 在偏移 0。`exemption = rate * (128 + dataLen)`。 -/
private def emitLoadRentExemption (dataLen stackOff : Nat) (scope : String) : String :=
  s!"\
  ; load rentExemption {dataLen} via sol_get_rent_sysvar
  mov64 r1, r10
  add64 r1, -{sysvarScratch}
  call sol_get_rent_sysvar
  jeq r0, 0, rent_ok_{scope}_{stackOff}
  lddw r0, 0x1
  exit
rent_ok_{scope}_{stackOff}:
  ldxdw r1, [r10 - {sysvarScratch}]
  lddw r2, {128 + dataLen}
  mul64 r1, r2
  stxdw [r10 - {stackOff}], r1
"

private def emitLoadSignerKey0 (stackOff : Nat) : String :=
  s!"\
  ; load account-0 pubkey first u64 (ACC0_KEY+0)
  ldxdw r1, [r6 + ACC0_KEY + 0]
  stxdw [r10 - {stackOff}], r1
"

private def emitLoadAccU64 (comment offset : String) (stackOff : Nat) : String :=
  s!"\
  ; {comment}
  ldxdw r1, [r6 + {offset}]
  stxdw [r10 - {stackOff}], r1
"

private def emitLoadAccU8 (comment offset : String) (stackOff : Nat) : String :=
  s!"\
  ; {comment}
  ldxb r1, [r6 + {offset}]
  stxdw [r10 - {stackOff}], r1
"

/-- 从 walk 出的 header* 读账户 i 的 u64 字段。 -/
private def emitLoadWalkedU64 (i off stackOff : Nat) : String :=
  s!"\
  ; load walked acc{i} +{off}
  ldxdw r1, [r10 - {headerStack i}]
  ldxdw r1, [r1 + {off}]
  stxdw [r10 - {stackOff}], r1
"

/-- 从 walk 出的 header* 读账户 i 的 u8 旗。 -/
private def emitLoadWalkedU8 (i off stackOff : Nat) : String :=
  s!"\
  ; load walked acc{i} flag +{off}
  ldxdw r1, [r10 - {headerStack i}]
  ldxb r1, [r1 + {off}]
  stxdw [r10 - {stackOff}], r1
"

/--
账户 `acc` 的 key / owner 第 `word` 个小端 u64。
账户 0 走固定 Loader 偏移；账户 1 走 walk header（key+8，owner+40）。
不强制入口签名。
-/
private def emitLoadAccWord (kind : String) (acc word stackOff : Nat) : String :=
  let byteOff := 8 * word
  if acc == 0 then
    let base := if kind == "key" then "ACC0_KEY" else "ACC0_OWNER"
    s!"\
  ; load acc0 {kind} word {word}
  ldxdw r1, [r6 + {base} + {byteOff}]
  stxdw [r10 - {stackOff}], r1
"
  else
    let hdrOff := (if kind == "key" then 8 else 40) + byteOff
    emitLoadWalkedU64 acc hdrOff stackOff

/-- Read one statically selected little-endian u64 from account data. Check `data_len` before
forming the data pointer so a short or malformed account exits with `Custom(1)`. -/
private def emitLoadAccDataWord (acc word stackOff : Nat) (scope : String) : String :=
  let byteOff := 8 * word
  let required := byteOff + 8
  let ok := s!"ok_data_word_{scope}_{acc}_{word}_{stackOff}"
  if acc == 0 then
    s!"\
  ; load acc0 data word {word}
  ldxdw r2, [r6 + ACC0_DATA_LEN]
  lddw r3, {required}
  jge r2, r3, {ok}
  lddw r0, 0x1
  exit
{ok}:
  mov64 r1, r6
  add64 r1, ACC0_DATA
  lddw r2, {byteOff}
  add64 r1, r2
  ldxdw r1, [r1 + 0]
  stxdw [r10 - {stackOff}], r1
"
  else
    s!"\
  ; load walked acc{acc} data word {word}
  ldxdw r1, [r10 - {headerStack acc}]
  ldxdw r2, [r1 + 80]
  lddw r3, {required}
  jge r2, r3, {ok}
  lddw r0, 0x1
  exit
{ok}:
  add64 r1, 88
  lddw r2, {byteOff}
  add64 r1, r2
  ldxdw r1, [r1 + 0]
  stxdw [r10 - {stackOff}], r1
"

/--
账户 `acc` 的 header 字段。账户 0 走固定 Loader 偏移；≥1 走 walk。
`kind`：lamports / dataLen / signer / writable / executable / key0。
-/
private def emitLoadAccN (kind : String) (acc stackOff : Nat) : String :=
  if acc == 0 then
    match kind with
    | "lamports" => emitLoadAccU64 "load acc0 lamports" "ACC0_LAMPORTS" stackOff
    | "dataLen" => emitLoadAccU64 "load acc0 data_len" "ACC0_DATA_LEN" stackOff
    | "signer" => emitLoadAccU8 "load acc0 is_signer" "ACC0_HEADER + 1" stackOff
    | "writable" => emitLoadAccU8 "load acc0 is_writable" "ACC0_HEADER + 2" stackOff
    | "executable" => emitLoadAccU8 "load acc0 is_executable" "ACC0_HEADER + 3" stackOff
    | _ => emitLoadAccU64 "load acc0 key first u64" "ACC0_KEY + 0" stackOff
  else
    let (off, u8) :=
      match kind with
      | "lamports" => (72, false)
      | "dataLen" => (80, false)
      | "signer" => (1, true)
      | "writable" => (2, true)
      | "executable" => (3, true)
      | _ => (8, false)
    if u8 then emitLoadWalkedU8 acc off stackOff
    else emitLoadWalkedU64 acc off stackOff

/--
owner 32B 是否等于当前 program id。相等写 0，不等写 1。
program id 在 instruction data 之后（单账户）或 walk 出的 ix 长度字之后。
-/
private def emitLoadOwnerIsSelf (p : IR.Program) (acc stackOff : Nat) (scope : String) : String :=
  let progId :=
    if IR.usesWalk p then
      s!"\
  ldxdw r3, [r10 - {headerStack (IR.cpiAccountCount p)}]
  ldxdw r1, [r3 + 0]
  add64 r3, 8
  add64 r3, r1
"
    else
      s!"\
  ldxdw r1, [r6 + INSTRUCTION_DATA_LEN]
  mov64 r3, r6
  add64 r3, INSTRUCTION_DATA
  add64 r3, r1
"
  let owner :=
    if acc == 0 && !IR.usesWalk p then
      s!"\
  mov64 r2, r6
  add64 r2, ACC0_OWNER
"
    else if acc == 0 then
      s!"\
  ldxdw r2, [r10 - {headerStack 0}]
  add64 r2, 40
"
    else
      s!"\
  ldxdw r2, [r10 - {headerStack acc}]
  add64 r2, 40
"
  s!"\
  ; ownerIsSelf acc={acc}
{progId}{owner}  ldxdw r1, [r2 + 0]
  ldxdw r4, [r3 + 0]
  jne r1, r4, ois_no_{scope}_{acc}_{stackOff}
  ldxdw r1, [r2 + 8]
  ldxdw r4, [r3 + 8]
  jne r1, r4, ois_no_{scope}_{acc}_{stackOff}
  ldxdw r1, [r2 + 16]
  ldxdw r4, [r3 + 16]
  jne r1, r4, ois_no_{scope}_{acc}_{stackOff}
  ldxdw r1, [r2 + 24]
  ldxdw r4, [r3 + 24]
  jne r1, r4, ois_no_{scope}_{acc}_{stackOff}
  lddw r1, 0
  stxdw [r10 - {stackOff}], r1
  ja ois_done_{scope}_{acc}_{stackOff}
ois_no_{scope}_{acc}_{stackOff}:
  lddw r1, 1
  stxdw [r10 - {stackOff}], r1
ois_done_{scope}_{acc}_{stackOff}:
"

/--
`sol_try_find_program_address`：一条 ASCII 种子 + 当前 program id。
scratch 用 `r8` 基址 `r10-2800`，避开 invoke 的 `r9=r10-2048` 和 sysvar 的 `r10-3072`。
CPI 程序的 program id 在 walk 出的 ix 长度字之后。
-/
private def emitLoadFindPda (p : IR.Program) (seed : String) (stackOff : Nat)
    (scope : String) : String :=
  let (bytes, _) :=
    seed.toList.foldl (init := ("", 0)) fun (acc, i) c =>
      (acc ++ s!"  lddw r1, {c.toNat}\n  stxb [r8 + {i}], r1\n", i + 1)
  let progId :=
    if IR.usesWalk p then
      s!"\
  ldxdw r3, [r10 - {headerStack (IR.cpiAccountCount p)}]
  ldxdw r1, [r3 + 0]
  add64 r3, 8
  add64 r3, r1
"
    else
      s!"\
  ldxdw r1, [r6 + INSTRUCTION_DATA_LEN]
  mov64 r3, r6
  add64 r3, INSTRUCTION_DATA
  add64 r3, r1
"
  s!"\
  ; findPda seed={seed}
  mov64 r8, r10
  add64 r8, -2800
  lddw r1, 0
  stxdw [r8 + 0], r1
  stxdw [r8 + 8], r1
{bytes}  mov64 r5, r8
  add64 r5, 16
  stxdw [r5 + 0], r8
  lddw r1, {seed.length}
  stxdw [r5 + 8], r1
{progId}  mov64 r1, r5
  lddw r2, 1
  mov64 r4, r8
  add64 r4, 48
  mov64 r5, r8
  add64 r5, 80
  call sol_try_find_program_address
  jeq r0, 0, find_pda_ok_{scope}_{stackOff}
  lddw r0, 0x1
  exit
find_pda_ok_{scope}_{stackOff}:
  ldxb r1, [r8 + 80]
  jeq r1, 0, find_pda_bad_{scope}_{stackOff}
  stxdw [r10 - {stackOff}], r1
  ja find_pda_done_{scope}_{stackOff}
find_pda_bad_{scope}_{stackOff}:
  lddw r0, 0x1
  exit
find_pda_done_{scope}_{stackOff}:
"

/-- `sol_try_find_program_address` for a static heterogeneous seed list. Account-key seeds point
directly into walked input headers; literal bytes, descriptors, and syscall outputs live at the
bottom of the current stack frame, disjoint from an in-progress CPI layout. The returned value is
the canonical bump. -/
private def emitLoadFindPdaSeeds (p : IR.Program) (seeds : Array Ops.PdaSeed)
    (stackOff : Nat) (scope : String) : String := Id.run do
  let descOff := 512
  let outKeyOff := 1024
  let outBumpOff := 1056
  let mut bytes := ""
  let mut descriptors := ""
  let mut byteOff := 0
  for i in [0:seeds.size] do
    let descriptor := descOff + 16 * i
    match seeds[i]! with
    | .ascii value =>
        let start := byteOff
        for c in value.toList do
          bytes := bytes ++ s!"  lddw r1, {c.toNat}\n  stxb [r8 + {byteOff}], r1\n"
          byteOff := byteOff + 1
        descriptors := descriptors ++ s!"\
  mov64 r1, r8
  add64 r1, {start}
  stxdw [r8 + {descriptor}], r1
  lddw r1, {value.length}
  stxdw [r8 + {descriptor + 8}], r1
"
    | .stateKey =>
        descriptors := descriptors ++ s!"\
  ldxdw r1, [r10 - {headerStack 0}]
  add64 r1, 8
  stxdw [r8 + {descriptor}], r1
  lddw r1, 32
  stxdw [r8 + {descriptor + 8}], r1
"
    | .accKey account =>
        descriptors := descriptors ++ s!"\
  ldxdw r1, [r10 - {headerStack (account + 1)}]
  add64 r1, 8
  stxdw [r8 + {descriptor}], r1
  lddw r1, 32
  stxdw [r8 + {descriptor + 8}], r1
"
  let progId :=
    if IR.usesWalk p then
      s!"\
  ldxdw r3, [r10 - {headerStack (IR.cpiAccountCount p)}]
  ldxdw r1, [r3 + 0]
  add64 r3, 8
  add64 r3, r1
"
    else
      s!"\
  ldxdw r1, [r6 + INSTRUCTION_DATA_LEN]
  mov64 r3, r6
  add64 r3, INSTRUCTION_DATA
  add64 r3, r1
"
  return s!"\
  ; findPdaSeeds count={seeds.size}
  mov64 r8, r10
  add64 r8, -{pdaSeedsScratch}
{bytes}{descriptors}{progId}  mov64 r1, r8
  add64 r1, {descOff}
  lddw r2, {seeds.size}
  mov64 r4, r8
  add64 r4, {outKeyOff}
  mov64 r5, r8
  add64 r5, {outBumpOff}
  call sol_try_find_program_address
  jeq r0, 0, find_pdas_ok_{scope}_{stackOff}
  lddw r0, 0x1
  exit
find_pdas_ok_{scope}_{stackOff}:
  ldxb r1, [r8 + {outBumpOff}]
  stxdw [r10 - {stackOff}], r1
"

/-- Find a heterogeneous canonical PDA and compare all four 64-bit key words with one walked
external account. The result is 0 on equality and 1 on mismatch. -/
private def emitLoadCheckPdaSeeds (p : IR.Program) (account : Nat)
    (seeds : Array Ops.PdaSeed) (stackOff : Nat) (scope : String) : String :=
  let find := emitLoadFindPdaSeeds p seeds stackOff (scope ++ "_find")
  let tag := s!"{scope}_{stackOff}_{account}"
  find ++ s!"\
  ; checkPdaSeeds account={account} count={seeds.size}
  ldxdw r2, [r10 - {headerStack (account + 1)}]
  add64 r2, 8
  ldxdw r1, [r8 + 1024]
  ldxdw r3, [r2 + 0]
  jne r1, r3, check_pdas_bad_{tag}
  ldxdw r1, [r8 + 1032]
  ldxdw r3, [r2 + 8]
  jne r1, r3, check_pdas_bad_{tag}
  ldxdw r1, [r8 + 1040]
  ldxdw r3, [r2 + 16]
  jne r1, r3, check_pdas_bad_{tag}
  ldxdw r1, [r8 + 1048]
  ldxdw r3, [r2 + 24]
  jne r1, r3, check_pdas_bad_{tag}
  lddw r1, 0
  stxdw [r10 - {stackOff}], r1
  ja check_pdas_done_{tag}
check_pdas_bad_{tag}:
  lddw r1, 1
  stxdw [r10 - {stackOff}], r1
check_pdas_done_{tag}:
"

/--
一条 ASCII 字面量的哈希 syscall：`sol_sha256` / `sol_keccak256`。
r1 = SolBytes[1]，r2 = 1，r3 = 32B dest。返回 dest 第一个小端 u64。
scratch 同 findPda，用 `r8 = r10-2800`。空串合法（len=0）。
-/
private def emitLoadHashLit (kind syscall seed : String) (stackOff : Nat) : String :=
  let (bytes, _) :=
    seed.toList.foldl (init := ("", 0)) fun (acc, i) c =>
      (acc ++ s!"  lddw r1, {c.toNat}\n  stxb [r8 + {i}], r1\n", i + 1)
  s!"\
  ; {kind} seed={seed}
  mov64 r8, r10
  add64 r8, -2800
  lddw r1, 0
  stxdw [r8 + 0], r1
  stxdw [r8 + 8], r1
{bytes}  mov64 r5, r8
  add64 r5, 16
  stxdw [r5 + 0], r8
  lddw r1, {seed.length}
  stxdw [r5 + 8], r1
  mov64 r1, r5
  lddw r2, 1
  mov64 r3, r8
  add64 r3, 48
  call {syscall}
  ldxdw r1, [r8 + 48]
  stxdw [r10 - {stackOff}], r1
"

private def emitLoadSha256Lit (seed : String) (stackOff : Nat) : String :=
  emitLoadHashLit "sha256Lit" "sol_sha256" seed stackOff

private def emitLoadKeccak256Lit (seed : String) (stackOff : Nat) : String :=
  emitLoadHashLit "keccak256Lit" "sol_keccak256" seed stackOff


set_option maxRecDepth 4096 in
set_option linter.unusedVariables false in
mutual
private partial def emitLoadBitBin (p : IR.Program) (op : String) (l r : Ops.Val)
    (stackOff nonce : Nat) (scope : String) : Except String String := do
  let loadL ← loadVal p l (stackOff + 8) (nonce + 1) (scope ++ "_l")
  let loadR ← loadVal p r (stackOff + 16) (nonce + 2) (scope ++ "_r")
  return loadL ++ loadR ++
    s!"\
  ldxdw r1, [r10 - {stackOff + 8}]
  ldxdw r2, [r10 - {stackOff + 16}]
  {op} r1, r2
  stxdw [r10 - {stackOff}], r1
"

private partial def emitLoadBitNot (p : IR.Program) (v : Ops.Val) (stackOff nonce : Nat)
    (scope : String) : Except String String := do
  let load ← loadVal p v (stackOff + 8) (nonce + 1) (scope ++ "_v")
  return load ++
    s!"\
  ldxdw r1, [r10 - {stackOff + 8}]
  lddw r2, 0xffffffffffffffff
  xor64 r1, r2
  stxdw [r10 - {stackOff}], r1
"

private partial def emitLoadByteSwap64 (p : IR.Program) (v : Ops.Val) (stackOff nonce : Nat)
    (scope : String) : Except String String := do
  let load ← loadVal p v (stackOff + 8) (nonce + 1) (scope ++ "_v")
  return load ++
    s!"\
  ldxdw r1, [r10 - {stackOff + 8}]
  be64 r1
  stxdw [r10 - {stackOff}], r1
"

/-- Compact call site for `Nat.sub`, normalized as `select (lhs ≥ rhs) (lhs - rhs) 0`. -/
private partial def emitLoadNatSub (p : IR.Program) (l r : Ops.Val)
    (stackOff nonce : Nat) (scope : String) : Except String String := do
  let loadL ← loadVal p l (stackOff + 8) (nonce + 1) (scope ++ "_l")
  let loadR ← loadVal p r (stackOff + 16) (nonce + 2) (scope ++ "_r")
  return loadL ++ loadR ++
    s!"\
  ldxdw r1, [r10 - {stackOff + 8}]
  ldxdw r2, [r10 - {stackOff + 16}]
  call __pf_nat_sub_u64
  stxdw [r10 - {stackOff}], r1
"

private partial def natSubHelper : String := "\
__pf_nat_sub_u64:
  jge r1, r2, __pf_nat_sub_u64_subtract
  lddw r1, 0
  exit
__pf_nat_sub_u64_subtract:
  sub64 r1, r2
  exit
"

/-- Lean `UInt64` uses the low six bits of a `UInt64` shift amount. -/
private partial def emitLoadShift (p : IR.Program) (op : String) (l r : Ops.Val)
    (stackOff nonce : Nat) (scope : String) : Except String String := do
  let loadL ← loadVal p l (stackOff + 8) (nonce + 1) (scope ++ "_l")
  let loadR ← loadVal p r (stackOff + 16) (nonce + 2) (scope ++ "_r")
  return loadL ++ loadR ++
    s!"\
  ldxdw r1, [r10 - {stackOff + 8}]
  ldxdw r2, [r10 - {stackOff + 16}]
  and64 r2, 63
  {op} r1, r2
  stxdw [r10 - {stackOff}], r1
"

private partial def emitLoadSelect (p : IR.Program) (cmp : Ops.Cmp) (l r t f : Ops.Val)
    (stackOff nonce : Nat) (scope : String) : Except String String := do
  let loadL ← loadVal p l (stackOff + 8) (nonce + 1) (scope ++ "_l")
  let loadR ← loadVal p r (stackOff + 16) (nonce + 2) (scope ++ "_r")
  let loadT ← loadVal p t stackOff (nonce + 3) (scope ++ "_t")
  let loadF ← loadVal p f stackOff (nonce + 4) (scope ++ "_f")
  let token := IR.u64Hex (Core.IR.fnv1a64 s!"{scope}:{stackOff}:{nonce}")
  let thenLab := s!"then_select_{token}"
  let doneLab := s!"done_select_{token}"
  let jump :=
    match cmp with
    | .eq => s!"  jeq r1, r2, {thenLab}\n"
    | .ne => s!"  jne r1, r2, {thenLab}\n"
    | .lt => s!"  jlt r1, r2, {thenLab}\n"
    | .le => s!"  jle r1, r2, {thenLab}\n"
    | .gt => s!"  jgt r1, r2, {thenLab}\n"
    | .ge => s!"  jge r1, r2, {thenLab}\n"
  return loadL ++ loadR ++
    s!"  ldxdw r1, [r10 - {stackOff + 8}]\n  ldxdw r2, [r10 - {stackOff + 16}]\n" ++
    jump ++ loadF ++ s!"  ja {doneLab}\n{thenLab}:\n" ++ loadT ++ s!"{doneLab}:\n"


private partial def loadVal (p : IR.Program) (v : Ops.Val) (stackOff : Nat) (nonce : Nat := 0)
    (scope : String := "value") : Except String String :=
  match v with
  | .local i => do
    let some localOff := scalarLocalStackOff p i
      | .error "extract/unsupported: too many scalar locals"
    .ok s!"  ; load local {i}\n  ldxdw r1, [r10 - {localOff}]\n  stxdw [r10 - {stackOff}], r1\n"
  | .lit n =>
    .ok s!"  ; load lit {n}\n  lddw r1, 0x{IR.u64Hex n}\n  stxdw [r10 - {stackOff}], r1\n"
  | .ext .clockSlot #[] =>
    .ok (emitLoadClockSlot stackOff scope)
  | .ext .clockEpoch #[] =>
    .ok (emitLoadClockEpoch stackOff scope)
  | .ext .unixTime #[] =>
    .ok (emitLoadUnixTime stackOff scope)
  | .ext .slotsPerEpoch #[] =>
    .ok (emitLoadSlotsPerEpoch stackOff scope)
  | .ext .cpiReturn #[] =>
    .ok (emitLoadCpiReturn stackOff scope)
  | .ext .signerKey0 #[] =>
    .ok (emitLoadSignerKey0 stackOff)
  | .ext .accLamports0 #[] =>
    .ok (emitLoadAccU64 "load account-0 lamports" "ACC0_LAMPORTS" stackOff)
  | .ext .accOwner0 #[] =>
    .ok (emitLoadAccU64 "load account-0 owner first u64" "ACC0_OWNER + 0" stackOff)
  | .ext .accDataLen0 #[] =>
    .ok (emitLoadAccU64 "load account-0 data_len" "ACC0_DATA_LEN" stackOff)
  | .ext .accN #[] =>
    .ok (emitLoadAccU64 "load NUM_ACCOUNTS" "NUM_ACCOUNTS" stackOff)
  | .ext .isSigner0 #[] =>
    .ok (emitLoadAccU8 "load account-0 is_signer" "ACC0_HEADER + 1" stackOff)
  | .ext .isWritable0 #[] =>
    .ok (emitLoadAccU8 "load account-0 is_writable" "ACC0_HEADER + 2" stackOff)
  | .ext .isExecutable0 #[] =>
    .ok (emitLoadAccU8 "load account-0 is_executable" "ACC0_HEADER + 3" stackOff)
  | .ext .accLamports1 #[] =>
    .ok (emitLoadWalkedU64 1 72 stackOff)
  | .ext .accOwner1 #[] =>
    .ok (emitLoadWalkedU64 1 40 stackOff)
  | .ext .accDataLen1 #[] =>
    .ok (emitLoadWalkedU64 1 80 stackOff)
  | .ext .isSigner1 #[] =>
    .ok (emitLoadWalkedU8 1 1 stackOff)
  | .ext .isWritable1 #[] =>
    .ok (emitLoadWalkedU8 1 2 stackOff)
  | .ext .isExecutable1 #[] =>
    .ok (emitLoadWalkedU8 1 3 stackOff)
  | .ext (.findPda seed) #[] =>
    .ok (emitLoadFindPda p seed stackOff scope)
  | .ext (.findPdaSeeds seeds) #[] =>
    .ok (emitLoadFindPdaSeeds p seeds stackOff scope)
  | .ext (.checkPdaSeeds account seeds) #[] =>
    .ok (emitLoadCheckPdaSeeds p account seeds stackOff scope)
  | .ext (.sha256Lit seed) #[] =>
    .ok (emitLoadSha256Lit seed stackOff)
  | .ext (.keccak256Lit seed) #[] =>
    .ok (emitLoadKeccak256Lit seed stackOff)
  | .ext .byteSwap64 #[word] =>
    emitLoadByteSwap64 p word stackOff nonce scope
  | .ext (.accKeyWord acc word) #[] =>
    .ok (emitLoadAccWord "key" acc word stackOff)
  | .ext (.accOwnerWord acc word) #[] =>
    .ok (emitLoadAccWord "owner" acc word stackOff)
  | .ext (.accDataWord acc word) #[] =>
    .ok (emitLoadAccDataWord acc word stackOff scope)
  | .ext (.accDataWordAt acc baseWord strideWords capacity) #[index] =>
    emitLoadAccDataWordAt p acc baseWord strideWords capacity index stackOff nonce scope
  | .ext (.accDataParentPathValid
      acc linksBaseWord parentBaseWord strideWords capacity maxDepth)
      #[index, root, bumpIndex] =>
    emitLoadAccDataParentPathValid p acc linksBaseWord parentBaseWord strideWords capacity
      maxDepth index root bumpIndex stackOff nonce scope
  | .ext (.accDataRbTreeValid acc linksBaseWord parentBaseWord keyBaseWord sequenceBaseWord
      strideWords capacity bid) #[root, size, bumpIndex, freeListHead] =>
    emitLoadAccDataRbTreeValid p acc linksBaseWord parentBaseWord keyBaseWord sequenceBaseWord
      strideWords capacity bid root size bumpIndex freeListHead stackOff nonce scope
  | .ext (.accDataRbTreeKey4Valid acc linksBaseWord parentBaseWord keyBaseWord
      strideWords capacity) #[root, size, bumpIndex, freeListHead] =>
    emitLoadAccDataRbTreeKey4Valid p acc linksBaseWord parentBaseWord keyBaseWord
      strideWords capacity root size bumpIndex freeListHead stackOff nonce scope
  | .ext (.accLamportsN acc) #[] =>
    .ok (emitLoadAccN "lamports" acc stackOff)
  | .ext (.accDataLenN acc) #[] =>
    .ok (emitLoadAccN "dataLen" acc stackOff)
  | .ext (.isSignerN acc) #[] =>
    .ok (emitLoadAccN "signer" acc stackOff)
  | .ext (.isWritableN acc) #[] =>
    .ok (emitLoadAccN "writable" acc stackOff)
  | .ext (.isExecutableN acc) #[] =>
    .ok (emitLoadAccN "executable" acc stackOff)
  | .ext (.signerKeyN acc) #[] =>
    .ok (emitLoadAccN "key0" acc stackOff)
  | .ext (.ownerIsSelf acc) #[] =>
    .ok (emitLoadOwnerIsSelf p acc stackOff scope)
  | .ext (.checkPda seed) #[bump] =>
    emitLoadCheckPda p seed bump stackOff nonce scope
  | .ext (.rentExemption n) #[] =>
    .ok (emitLoadRentExemption n.toNat stackOff scope)
  | .loopIx =>
    .ok s!"  ; load loop index\n  ldxdw r1, [r10 - {loopCounterScratch}]\n  stxdw [r10 - {stackOff}], r1\n"
  | .select .ge l r (.subU64 tl tr) (.lit 0) =>
    if l == tl && r == tr then emitLoadNatSub p l r stackOff nonce scope
    else emitLoadSelect p .ge l r (.subU64 tl tr) (.lit 0) stackOff nonce scope
  | .select cmp l r t f => emitLoadSelect p cmp l r t f stackOff nonce scope
  | .indexGet _ name idx len off =>
    emitLoadIndexGet p name idx len off stackOff nonce scope
  | .bitAnd l r => emitLoadBitBin p "and64" l r stackOff nonce scope
  | .bitOr l r => emitLoadBitBin p "or64" l r stackOff nonce scope
  | .bitXor l r => emitLoadBitBin p "xor64" l r stackOff nonce scope
  | .bitNot v => emitLoadBitNot p v stackOff nonce scope
  | .shiftL l r => emitLoadShift p "lsh64" l r stackOff nonce scope
  | .shiftR l r => emitLoadShift p "rsh64" l r stackOff nonce scope
  | .addU64 l r => emitLoadBitBin p "add64" l r stackOff nonce scope
  | .subU64 l r => emitLoadBitBin p "sub64" l r stackOff nonce scope
  | .mulU64 l r => emitLoadBitBin p "mul64" l r stackOff nonce scope
  | .divU64 l r => emitLoadBitBin p "div64" l r stackOff nonce scope
  | .modU64 l r => emitLoadBitBin p "mod64" l r stackOff nonce scope
  | .ext _ _ => .error "extract/ir: malformed SVM value operands"
  | v => do
    let mem ← memOfVal p v
    let insn ← loadInsn (widthOfVal p v)
    return s!"  ; load {sourceValRepr v}\n  {insn} r1, {mem}\n  stxdw [r10 - {stackOff}], r1\n"

/-- `cells_0` / `nodes_0_*` 起的定长向量。`idx ≥ len` → Custom(1)。 -/
private partial def emitLoadIndexGet (p : IR.Program) (name : String) (idx : Ops.Val)
    (len elemOff stackOff nonce : Nat) (scope : String) : Except String String := do
  let some baseOff := IR.vectorBaseOffset p name
    | .error s!"extract/unsupported: unknown vector {name}"
  let some width := IR.vectorLeafWidth p name elemOff
    | .error s!"extract/unsupported: unknown vector leaf {name}+{elemOff}"
  let load ← loadInsn width
  let loadIdx ← loadVal p idx (stackOff + 8) (nonce + 1) (scope ++ "_i")
  let bound := IR.vectorLenOf p name len
  let bound := if bound == 0 then 1 else bound
  let stride := IR.vectorStride p name
  let tag := s!"{scope}_{name}_{stackOff}_{elemOff}_{nonce}"
  return loadIdx ++
    s!"\
  ; indexGet {name}[{bound}]+{elemOff}
  ldxdw r2, [r10 - {stackOff + 8}]
  lddw r3, {bound}
  jlt r2, r3, ok_idx_{tag}
  lddw r0, 0x1
  exit
ok_idx_{tag}:
  mul64 r2, {stride}
  mov64 r1, r6
  add64 r1, ACC0_DATA
  add64 r1, {baseOff + elemOff}
  add64 r1, r2
  {load} r1, [r1 + 0]
  stxdw [r10 - {stackOff}], r1
  "

/-- Read one runtime-selected slot from a compile-time fixed account-data region. The static
shape makes byte arithmetic overflow impossible; runtime index and final data length are checked
before the data pointer is formed. -/
private partial def emitLoadAccDataWordAt (p : IR.Program) (acc baseWord strideWords capacity : Nat)
    (index : Ops.Val) (stackOff nonce : Nat) (scope : String) : Except String String := do
  let loadIndex ← loadVal p index (stackOff + 8) (nonce + 1) (scope ++ "_index")
  let baseBytes := 8 * baseWord
  let strideBytes := 8 * strideWords
  let token := IR.u64Hex (Core.IR.fnv1a64
    s!"{scope}:{stackOff}:{nonce}:{acc}:{baseWord}:{strideWords}:{capacity}")
  let indexOk := s!"ok_data_index_{token}"
  let dataOk := s!"ok_indexed_data_word_{token}"
  let account :=
    if acc == 0 then
      s!"\
  ldxdw r4, [r6 + ACC0_DATA_LEN]
  jge r4, r3, {dataOk}
  lddw r0, 0x1
  exit
{dataOk}:
  mov64 r1, r6
  add64 r1, ACC0_DATA
"
    else
      s!"\
  ldxdw r1, [r10 - {headerStack acc}]
  ldxdw r4, [r1 + 80]
  jge r4, r3, {dataOk}
  lddw r0, 0x1
  exit
{dataOk}:
  add64 r1, 88
"
  return loadIndex ++
    s!"\
  ; load bounded acc{acc} data word base={baseWord} stride={strideWords} capacity={capacity}
  ldxdw r2, [r10 - {stackOff + 8}]
  lddw r3, {capacity}
  jlt r2, r3, {indexOk}
  lddw r0, 0x1
  exit
{indexOk}:
  lddw r3, {strideBytes}
  mul64 r2, r3
  mov64 r3, r2
  lddw r4, {baseBytes + 8}
  add64 r3, r4
" ++ account ++
    s!"\
  lddw r3, {baseBytes}
  add64 r1, r3
  add64 r1, r2
  ldxdw r1, [r1 + 0]
  stxdw [r10 - {stackOff}], r1
"

/-- Follow one account-resident parent path with constant memory. Every dereference is selected
from a compile-time fixed region, while index/root/bump and the final account length are checked
before pointer formation. A cycle that excludes the root exhausts `maxDepth` and returns zero. -/
private partial def emitLoadAccDataParentPathValid (p : IR.Program)
    (acc linksBaseWord parentBaseWord strideWords capacity maxDepth : Nat)
    (index root bumpIndex : Ops.Val) (stackOff nonce : Nat) (scope : String) :
    Except String String := do
  let loadIndex ← loadVal p index (stackOff + 8) (nonce + 1) (scope ++ "_index")
  let loadRoot ← loadVal p root (stackOff + 16) (nonce + 2) (scope ++ "_root")
  let loadBump ← loadVal p bumpIndex (stackOff + 24) (nonce + 3) (scope ++ "_bump")
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
  ldxdw r1, [r10 - {headerStack acc}]
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
private partial def emitLoadAccDataRbTreeValid (p : IR.Program)
    (acc linksBaseWord parentBaseWord keyBaseWord sequenceBaseWord strideWords capacity : Nat)
    (bid : Bool) (root size bumpIndex freeListHead : Ops.Val)
    (stackOff nonce : Nat) (scope : String) : Except String String := do
  let loadRoot ← loadVal p root (stackOff + 8) (nonce + 1) (scope ++ "_root")
  let loadSize ← loadVal p size (stackOff + 16) (nonce + 2) (scope ++ "_size")
  let loadBump ← loadVal p bumpIndex (stackOff + 24) (nonce + 3) (scope ++ "_bump")
  let loadFree ← loadVal p freeListHead (stackOff + 32) (nonce + 4) (scope ++ "_free")
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
  let rightOk := s!"rb_right_ok_{token}"
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
  ldxdw r1, [r10 - {headerStack acc}]
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

/-- Validate a fixed-capacity account-resident red-black tree whose key is four consecutive words.
The traversal marks each live node once on descent, uses a fixed stack for in-order visitation, and
then reuses the bitmap for the allocator free list. `be64` turns each loaded little-endian word into
the unsigned byte-lexicographic limb used by `[u8; 32]` ordering. -/
private partial def emitLoadAccDataRbTreeKey4Valid (p : IR.Program)
    (acc linksBaseWord parentBaseWord keyBaseWord strideWords capacity : Nat)
    (root size bumpIndex freeListHead : Ops.Val)
    (stackOff nonce : Nat) (scope : String) : Except String String := do
  let loadRoot ← loadVal p root (stackOff + 8) (nonce + 1) (scope ++ "_root")
  let loadSize ← loadVal p size (stackOff + 16) (nonce + 2) (scope ++ "_size")
  let loadBump ← loadVal p bumpIndex (stackOff + 24) (nonce + 3) (scope ++ "_bump")
  let loadFree ← loadVal p freeListHead (stackOff + 32) (nonce + 4) (scope ++ "_free")
  let strideBytes := 8 * strideWords
  let linksBaseBytes := 8 * linksBaseWord
  let parentBaseBytes := 8 * parentBaseWord
  let keyBaseBytes := 8 * keyBaseWord
  let finalWord :=
    Nat.max linksBaseWord (Nat.max parentBaseWord (keyBaseWord + 3)) +
      strideWords * (capacity - 1)
  let requiredBytes := 8 * (finalWord + 1)
  let bitmapWords := (capacity + 63) / 64
  let clearBitmap := (List.range bitmapWords).foldl (init := "") fun text i =>
    text ++ s!"  stxdw [r9 + {8 * i}], r1\n"
  let token := IR.u64Hex (Core.IR.fnv1a64
    (s!"{scope}:{stackOff}:{nonce}:{acc}:{linksBaseWord}:{parentBaseWord}:" ++
      s!"{keyBaseWord}:{strideWords}:{capacity}"))
  let dataOk := s!"rb4_data_ok_{token}"
  let nonEmpty := s!"rb4_nonempty_{token}"
  let startLive := s!"rb4_start_live_{token}"
  let liveLoop := s!"rb4_live_loop_{token}"
  let nonRoot := s!"rb4_nonroot_{token}"
  let parentOk := s!"rb4_parent_ok_{token}"
  let depthReady := s!"rb4_depth_ready_{token}"
  let nullChild := s!"rb4_null_{token}"
  let blackHeightSet := s!"rb4_bh_set_{token}"
  let blackHeightOk := s!"rb4_bh_ok_{token}"
  let firstKey := s!"rb4_first_key_{token}"
  let keyLimb1 := s!"rb4_key_limb1_{token}"
  let keyLimb2 := s!"rb4_key_limb2_{token}"
  let keyLimb3 := s!"rb4_key_limb3_{token}"
  let keyOk := s!"rb4_key_ok_{token}"
  let storeKey := s!"rb4_store_key_{token}"
  let rightNull := s!"rb4_right_null_{token}"
  let afterLive := s!"rb4_after_live_{token}"
  let startFree := s!"rb4_start_free_{token}"
  let freeLoop := s!"rb4_free_loop_{token}"
  let freeDone := s!"rb4_free_done_{token}"
  let success := s!"rb4_success_{token}"
  let failure := s!"rb4_failure_{token}"
  let done := s!"rb4_done_{token}"
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
  ldxdw r1, [r10 - {headerStack acc}]
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
  ; complete four-word-key account-resident RB tree and allocator validation
  ; links={linksBaseWord} parent={parentBaseWord} key4={keyBaseWord} stride={strideWords} capacity={capacity}
  ; r7 remains the walked instruction-data base outside this intrinsic.
  stxdw [r10 - {stackOff + 168}], r7
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
  ; bitmap: r10-4096 .. r10-3049; traversal stack: r10-3000 .. r10-2489.
  mov64 r9, r10
  add64 r9, -{rbTreeKey4BitmapScratch}
  lddw r1, 0
{clearBitmap}  lddw r1, 0
  stxdw [r10 - {stackOff + 40}], r1
  stxdw [r10 - {stackOff + 48}], r1
  stxdw [r10 - {stackOff + 64}], r1
  stxdw [r10 - {stackOff + 72}], r1
  stxdw [r10 - {stackOff + 80}], r1
  stxdw [r10 - {stackOff + 88}], r1
  stxdw [r10 - {stackOff + 96}], r1
  stxdw [r10 - {stackOff + 56}], r3
{liveLoop}:
  ; Descend once into each live node. Current/depth/expected-parent/parent-color are fixed scalars.
  ldxdw r2, [r10 - {stackOff + 56}]
  jeq r2, 0, {nullChild}
  ldxdw r4, [r10 - {stackOff + 24}]
  jge r2, r4, {failure}
  lddw r1, {capacity}
  jgt r2, r1, {failure}
  mov64 r7, r2
  sub64 r7, 1
  lddw r1, {strideBytes}
  mul64 r7, r1
  mov64 r9, r5
  lddw r1, {parentBaseBytes}
  add64 r9, r1
  add64 r9, r7
  ldxdw r8, [r9 + 0]
  mov64 r4, r8
  rsh64 r4, 32
  jgt r4, 1, {failure}
  mov64 r1, r8
  lsh64 r1, 32
  rsh64 r1, 32
  ldxdw r9, [r10 - {stackOff + 72}]
  jne r9, 0, {nonRoot}
  ldxdw r3, [r10 - {stackOff + 8}]
  jne r2, r3, {failure}
  jne r8, 0, {failure}
  ja {parentOk}
{nonRoot}:
  jne r1, r9, {failure}
  ldxdw r9, [r10 - {stackOff + 80}]
  jeq r9, 0, {parentOk}
  jne r4, 0, {failure}
{parentOk}:
  ; A shared child, structural cycle, or live/free overlap reuses a bitmap bit and fails.
  mov64 r8, r2
  sub64 r8, 1
  mov64 r9, r8
  and64 r9, 63
  lddw r0, 1
  lsh64 r0, r9
  rsh64 r8, 6
  lsh64 r8, 3
  mov64 r9, r10
  add64 r9, -{rbTreeKey4BitmapScratch}
  add64 r9, r8
  ldxdw r8, [r9 + 0]
  mov64 r1, r8
  and64 r1, r0
  jne r1, 0, {failure}
  or64 r8, r0
  stxdw [r9 + 0], r8
  ldxdw r1, [r10 - {stackOff + 40}]
  add64 r1, 1
  stxdw [r10 - {stackOff + 40}], r1
  ldxdw r8, [r10 - {stackOff + 16}]
  jgt r1, r8, {failure}
  ; Black depth includes the current node. A red parent may only reach a black child.
  ldxdw r1, [r10 - {stackOff + 64}]
  jne r4, 0, {depthReady}
  add64 r1, 1
{depthReady}:
  stxdw [r10 - {stackOff + 64}], r1
  ; One packed stack word stores low-u32 node index and high-u32 black depth.
  ldxdw r8, [r10 - {stackOff + 88}]
  lddw r9, {rbTreeKey4TraversalDepth}
  jge r8, r9, {failure}
  mov64 r9, r10
  add64 r9, -{rbTreeKey4TraversalScratch}
  mov64 r0, r8
  lsh64 r0, 3
  add64 r9, r0
  mov64 r0, r1
  lsh64 r0, 32
  or64 r0, r2
  stxdw [r9 + 0], r0
  add64 r8, 1
  stxdw [r10 - {stackOff + 88}], r8
  stxdw [r10 - {stackOff + 72}], r2
  stxdw [r10 - {stackOff + 80}], r4
  mov64 r9, r5
  lddw r1, {linksBaseBytes}
  add64 r9, r1
  add64 r9, r7
  ldxdw r1, [r9 + 0]
  lsh64 r1, 32
  rsh64 r1, 32
  stxdw [r10 - {stackOff + 56}], r1
  ja {liveLoop}
{nullChild}:
  ; Every sentinel leaf must observe the same black depth.
  ldxdw r1, [r10 - {stackOff + 64}]
  ldxdw r8, [r10 - {stackOff + 48}]
  jeq r8, 0, {blackHeightSet}
  jne r1, r8, {failure}
  ja {blackHeightOk}
{blackHeightSet}:
  stxdw [r10 - {stackOff + 48}], r1
{blackHeightOk}:
  ldxdw r8, [r10 - {stackOff + 88}]
  jeq r8, 0, {afterLive}
  sub64 r8, 1
  stxdw [r10 - {stackOff + 88}], r8
  mov64 r9, r10
  add64 r9, -{rbTreeKey4TraversalScratch}
  mov64 r1, r8
  lsh64 r1, 3
  add64 r9, r1
  ldxdw r8, [r9 + 0]
  mov64 r2, r8
  lsh64 r2, 32
  rsh64 r2, 32
  rsh64 r8, 32
  stxdw [r10 - {stackOff + 64}], r8
  stxdw [r10 - {stackOff + 72}], r2
  ; Load the current key once, byte-swap each storage word, then compare lexicographically.
  mov64 r7, r2
  sub64 r7, 1
  lddw r1, {strideBytes}
  mul64 r7, r1
  mov64 r9, r5
  lddw r1, {keyBaseBytes}
  add64 r9, r1
  add64 r9, r7
  ldxdw r1, [r9 + 0]
  be64 r1
  stxdw [r10 - {stackOff + 136}], r1
  ldxdw r1, [r9 + 8]
  be64 r1
  stxdw [r10 - {stackOff + 144}], r1
  ldxdw r1, [r9 + 16]
  be64 r1
  stxdw [r10 - {stackOff + 152}], r1
  ldxdw r1, [r9 + 24]
  be64 r1
  stxdw [r10 - {stackOff + 160}], r1
  ldxdw r8, [r10 - {stackOff + 96}]
  jeq r8, 0, {firstKey}
  ldxdw r1, [r10 - {stackOff + 136}]
  ldxdw r2, [r10 - {stackOff + 104}]
  jgt r1, r2, {keyOk}
  jne r1, r2, {failure}
  ja {keyLimb1}
{keyLimb1}:
  ldxdw r1, [r10 - {stackOff + 144}]
  ldxdw r2, [r10 - {stackOff + 112}]
  jgt r1, r2, {keyOk}
  jne r1, r2, {failure}
  ja {keyLimb2}
{keyLimb2}:
  ldxdw r1, [r10 - {stackOff + 152}]
  ldxdw r2, [r10 - {stackOff + 120}]
  jgt r1, r2, {keyOk}
  jne r1, r2, {failure}
  ja {keyLimb3}
{keyLimb3}:
  ldxdw r1, [r10 - {stackOff + 160}]
  ldxdw r2, [r10 - {stackOff + 128}]
  jgt r1, r2, {keyOk}
  ja {failure}
{firstKey}:
  lddw r8, 1
  stxdw [r10 - {stackOff + 96}], r8
  ja {storeKey}
{keyOk}:
  ja {storeKey}
{storeKey}:
  ldxdw r1, [r10 - {stackOff + 136}]
  stxdw [r10 - {stackOff + 104}], r1
  ldxdw r1, [r10 - {stackOff + 144}]
  stxdw [r10 - {stackOff + 112}], r1
  ldxdw r1, [r10 - {stackOff + 152}]
  stxdw [r10 - {stackOff + 120}], r1
  ldxdw r1, [r10 - {stackOff + 160}]
  stxdw [r10 - {stackOff + 128}], r1
  ; Continue into the right child with this node's depth and color.
  ldxdw r2, [r10 - {stackOff + 72}]
  mov64 r9, r5
  lddw r1, {linksBaseBytes}
  add64 r9, r1
  add64 r9, r7
  ldxdw r1, [r9 + 0]
  rsh64 r1, 32
  jeq r1, 0, {rightNull}
  stxdw [r10 - {stackOff + 56}], r1
  mov64 r9, r5
  lddw r1, {parentBaseBytes}
  add64 r9, r1
  add64 r9, r7
  ldxdw r1, [r9 + 0]
  rsh64 r1, 32
  stxdw [r10 - {stackOff + 80}], r1
  ja {liveLoop}
{rightNull}:
  lddw r1, 0
  stxdw [r10 - {stackOff + 56}], r1
  ja {liveLoop}
{afterLive}:
  ldxdw r1, [r10 - {stackOff + 40}]
  ldxdw r2, [r10 - {stackOff + 16}]
  jne r1, r2, {failure}
  ; Exact free cardinality plus the shared bitmap proves the full pre-bump partition.
  ldxdw r4, [r10 - {stackOff + 24}]
  sub64 r4, 1
  sub64 r4, r2
  lddw r1, 0
  stxdw [r10 - {stackOff + 40}], r1
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
  mov64 r8, r2
  sub64 r8, 1
  mov64 r9, r8
  and64 r9, 63
  lddw r0, 1
  lsh64 r0, r9
  rsh64 r8, 6
  lsh64 r8, 3
  mov64 r9, r10
  add64 r9, -{rbTreeKey4BitmapScratch}
  add64 r9, r8
  ldxdw r8, [r9 + 0]
  mov64 r1, r8
  and64 r1, r0
  jne r1, 0, {failure}
  or64 r8, r0
  stxdw [r9 + 0], r8
  ldxdw r1, [r10 - {stackOff + 40}]
  add64 r1, 1
  stxdw [r10 - {stackOff + 40}], r1
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
  ldxdw r1, [r10 - {stackOff + 40}]
  jne r1, r4, {failure}
{success}:
  lddw r1, 1
  stxdw [r10 - {stackOff}], r1
  ja {done}
{failure}:
  lddw r1, 0
  stxdw [r10 - {stackOff}], r1
{done}:
  ldxdw r7, [r10 - {stackOff + 168}]
"

/--
`sol_create_program_address`：一条 ASCII 种子 + bump 字节 + 当前 program id。
成功写 0，失败写 1。scratch 同 findPda，用 `r8 = r10-2800`。
-/
private partial def emitLoadCheckPda (p : IR.Program) (seed : String) (bump : Ops.Val)
    (stackOff nonce : Nat) (scope : String) : Except String String := do
  let bumpOff := stackOff + 8
  let loadBump ← loadVal p bump bumpOff (nonce + 1) (scope ++ "_bump")
  -- 必须复用 findPda 那条 `s!\"…\\n…\"` 字面量；`String.push '\\n'` 在 4.31 会编成字面 `\\n`。
  let (bytes, _) :=
    seed.toList.foldl (init := ("", 0)) fun (acc, i) c =>
      (acc ++ s!"  lddw r1, {c.toNat}\n  stxb [r8 + {i}], r1\n", i + 1)
  let progId :=
    if IR.usesWalk p then
      s!"\
  ldxdw r3, [r10 - {headerStack (IR.cpiAccountCount p)}]
  ldxdw r1, [r3 + 0]
  add64 r3, 8
  add64 r3, r1
"
    else
      s!"\
  ldxdw r1, [r6 + INSTRUCTION_DATA_LEN]
  mov64 r3, r6
  add64 r3, INSTRUCTION_DATA
  add64 r3, r1
"
  return loadBump ++
    s!"\
  ; checkPda seed={seed}
  mov64 r8, r10
  add64 r8, -2800
  lddw r1, 0
  stxdw [r8 + 0], r1
  stxdw [r8 + 8], r1
  stxdw [r8 + 16], r1
" ++ bytes ++
    s!"\
  ldxdw r1, [r10 - {bumpOff}]
  stxb [r8 + {seed.length}], r1
  mov64 r5, r8
  add64 r5, 32
  stxdw [r5 + 0], r8
  lddw r1, {seed.length + 1}
  stxdw [r5 + 8], r1
" ++ progId ++
    s!"\
  mov64 r1, r5
  lddw r2, 1
  mov64 r4, r8
  add64 r4, 64
  call sol_create_program_address
  stxdw [r10 - {stackOff}], r0
"

end

private def storeField (p : IR.Program) (name : String) (fromStack : Nat) : Except String String :=
  match IR.fieldOffset p name, IR.fieldWidth p name with
  | none, _ => .error s!"extract/unsupported: unknown field {name}"
  | _, none => .error s!"extract/unsupported: unknown field {name}"
  | some off, some w => do
    let insn ← storeInsn w
    .ok s!"  ldxdw r1, [r10 - {fromStack}]\n  {insn} [r6 + ACC0_DATA + {off}], r1\n"

private def destField (p : IR.Program) (lhs : Ops.Val) : String :=
  match lhs with
  | .field _ n => n
  | _ => (p.slots[0]?.map (·.name)).getD "slot0"

private partial def valUsesSigner (v : Ops.Val) : Bool :=
  match v with
  | .ext .signerKey0 _ | .ext (.signerKeyN _) _ => true
  | .ext _ operands => operands.any valUsesSigner
  | .field b _ => valUsesSigner b
  | .bitNot b => valUsesSigner b
  | .bitAnd l r | .bitOr l r | .bitXor l r | .shiftL l r | .shiftR l r
  | .addU64 l r | .subU64 l r | .mulU64 l r | .divU64 l r | .modU64 l r
      => valUsesSigner l || valUsesSigner r
  | .indexGet b _ i _ _ => valUsesSigner b || valUsesSigner i
  | .select _ l r t f =>
      valUsesSigner l || valUsesSigner r || valUsesSigner t || valUsesSigner f
  | _ => false

private partial def walkUsesSigner (ops : Array IR.Op) : Bool :=
  ops.any fun
      | .letLocal _ v => valUsesSigner v
      | .joinLocal _ => false
      | .setLocal _ v => valUsesSigner v
      | .checkedAddU64 l r => valUsesSigner l || valUsesSigner r
      | .checkedSubU64 l r => valUsesSigner l || valUsesSigner r
      | .checkedMulU64 l r => valUsesSigner l || valUsesSigner r
      | .checkedDivU64 l r => valUsesSigner l || valUsesSigner r
      | .checkedModU64 l r => valUsesSigner l || valUsesSigner r
      | .ite _ l r t f =>
          valUsesSigner l || valUsesSigner r ||
            walkUsesSigner t || walkUsesSigner f
      | .forAccum _ v _ => valUsesSigner v
      | .forBody _ body => walkUsesSigner body
      | .indexSet _ i v _ _ => valUsesSigner i || valUsesSigner v
      | .invoke _ metas data seeds bump =>
          (seeds.isEmpty && metas.any (·.signer)) ||
            data.any (fun word => word.value?.any valUsesSigner) ||
              (match bump with | some v => valUsesSigner v | none => false)
      | .accDataWordSetAt _ _ _ _ index value =>
          valUsesSigner index || valUsesSigner value
      | .accDataRbTreeKey4Insert _ _ _ _ _ _ _ key0 key1 key2 key3 =>
          #[key0, key1, key2, key3].any valUsesSigner
      | .okState v => valUsesSigner v
      | .returnU64 v => valUsesSigner v
      | .returnState v => valUsesSigner v
      | .storeField _ v => valUsesSigner v
      | .errorOverflow | .errorNamed _ => false

private def usesSignerKey (ops : Array IR.Op) : Bool :=
  walkUsesSigner ops

private def emitOverflowExit (label : String) : String :=
  s!"err_{label}:\n  lddw r0, {overflowCode}\n  exit\n"

private def emitOverflowReturn : String :=
  s!"  lddw r0, {overflowCode}\n  exit\n"

private def emitReturnU64 (fromStack : Nat) : String :=
  s!"  ldxdw r1, [r10 - {fromStack}]\n  stxdw [r10 - 32], r1\n  mov64 r1, r10\n  add64 r1, -32\n  lddw r2, 8\n  call sol_set_return_data\n  lddw r0, 0\n  exit\n"

/-- 从 walk 出的 header* 填一个 `SolAccountInfo`（56 字节），r5 指向槽。 -/
private def emitFillAccountInfoFromHeader (tag : String) (srcStack : Nat) : String :=
  let lab := "fill_rent_" ++ tag ++ "_" ++ toString srcStack
  "  ldxdw r8, [r10 - " ++ toString srcStack ++ "]\n" ++
  "  mov64 r1, r8\n  add64 r1, 8\n  stxdw [r5 + 0], r1\n" ++
  "  mov64 r1, r8\n  add64 r1, 72\n  stxdw [r5 + 8], r1\n" ++
  "  ldxdw r1, [r8 + 80]\n  stxdw [r5 + 16], r1\n" ++
  "  mov64 r1, r8\n  add64 r1, 88\n  stxdw [r5 + 24], r1\n" ++
  "  mov64 r1, r8\n  add64 r1, 40\n  stxdw [r5 + 32], r1\n" ++
  "  mov64 r1, r8\n  add64 r1, 88\n  ldxdw r4, [r8 + 80]\n" ++
  "  add64 r1, r4\n  add64 r1, MAX_PERMITTED_DATA_INCREASE\n" ++
  "  mov64 r2, r4\n  and64 r2, 7\n  jeq r2, 0, " ++ lab ++ "\n" ++
  "  lddw r3, 8\n  sub64 r3, r2\n  add64 r1, r3\n" ++
  lab ++ ":\n" ++
  "  ldxdw r1, [r1 + 0]\n  stxdw [r5 + 40], r1\n" ++
  "  ldxb r1, [r8 + 1]\n  stxb [r5 + 48], r1\n" ++
  "  ldxb r1, [r8 + 2]\n  stxb [r5 + 49], r1\n" ++
  "  ldxb r1, [r8 + 3]\n  stxb [r5 + 50], r1\n" ++
  "  lddw r1, 0\n  stxb [r5 + 51], r1\n  stxb [r5 + 52], r1\n" ++
  "  stxb [r5 + 53], r1\n  stxb [r5 + 54], r1\n  stxb [r5 + 55], r1\n"

private def emitCpiInteger (p : IR.Program) (scope : String) (base off : Nat)
    (store : String) (value : Ops.Val) : Except String String := do
  match value with
  | .lit n =>
      return s!"  lddw r1, {n.toNat}\n  {store} [r9 + {base + off}], r1\n"
  | _ =>
      let load ← loadVal p value 8 off s!"{scope}_data_{off}"
      return load ++
        s!"  ldxdw r1, [r10 - 8]\n  {store} [r9 + {base + off}], r1\n"

private def emitCpiData (p : IR.Program) (scope : String) (base : Nat)
    (data : Array (Ops.CpiWord Ops.Val)) : Except String (String × Nat) := do
  -- CreateAccount 是 52B：u32+u64 不对齐。先清 64B，避免残留污染 space。
  let mut body :=
    s!"  lddw r1, 0\n  stxdw [r9 + {base}], r1\n  stxdw [r9 + {base + 8}], r1\n" ++
    s!"  stxdw [r9 + {base + 16}], r1\n  stxdw [r9 + {base + 24}], r1\n" ++
    s!"  stxdw [r9 + {base + 32}], r1\n  stxdw [r9 + {base + 40}], r1\n" ++
    s!"  stxdw [r9 + {base + 48}], r1\n  stxdw [r9 + {base + 56}], r1\n"
  let mut off : Nat := 0
  for w in data do
    match w with
    | .u8le value =>
      body := body ++ (← emitCpiInteger p scope base off "stxb" value)
      off := off + 1
    | .u16le value =>
      body := body ++ (← emitCpiInteger p scope base off "stxh" value)
      off := off + 2
    | .u32le value =>
      body := body ++ (← emitCpiInteger p scope base off "stxw" value)
      off := off + 4
    | .u64le value =>
      body := body ++ (← emitCpiInteger p scope base off "stxdw" value)
      off := off + 8
    | .selfEntry tag _ =>
      body := body ++ s!"  lddw r1, {tag.toNat}\n  stxb [r9 + {base + off}], r1\n"
      off := off + 1
    | .ascii s =>
      -- 逐字节；本切片字面量很短。
      let mut i : Nat := 0
      for c in s.toList do
        body := body ++ s!"  lddw r1, {c.toNat}\n  stxb [r9 + {base + off + i}], r1\n"
        i := i + 1
      off := off + s.length
    | .programId =>
      let copy :=
        if IR.usesWalk p then
          s!"\
  ldxdw r1, [r10 - {headerStack (IR.cpiAccountCount p)}]
  ldxdw r2, [r1 + 0]
  add64 r1, 8
  add64 r1, r2
"
        else
          s!"\
  ldxdw r2, [r6 + INSTRUCTION_DATA_LEN]
  mov64 r1, r6
  add64 r1, INSTRUCTION_DATA
  add64 r1, r2
"
      body := body ++ copy ++
        s!"  ldxdw r2, [r1 + 0]\n  stxdw [r9 + {base + off}], r2\n" ++
        s!"  ldxdw r2, [r1 + 8]\n  stxdw [r9 + {base + off + 8}], r2\n" ++
        s!"  ldxdw r2, [r1 + 16]\n  stxdw [r9 + {base + off + 16}], r2\n" ++
        s!"  ldxdw r2, [r1 + 24]\n  stxdw [r9 + {base + off + 24}], r2\n"
      off := off + 32
    | .accKey i =>
      let physical := i + 1
      body := body ++
        s!"  ldxdw r1, [r10 - {headerStack physical}]\n  add64 r1, 8\n" ++
        s!"  ldxdw r2, [r1 + 0]\n  stxdw [r9 + {base + off}], r2\n" ++
        s!"  ldxdw r2, [r1 + 8]\n  stxdw [r9 + {base + off + 8}], r2\n" ++
        s!"  ldxdw r2, [r1 + 16]\n  stxdw [r9 + {base + off + 16}], r2\n" ++
        s!"  ldxdw r2, [r1 + 24]\n  stxdw [r9 + {base + off + 24}], r2\n"
      off := off + 32
  return (body, off)

/-- `r5` 已是 metas 基址（`r9 + metaOff`）；第 i 条相对偏移是 `16*i`，不要再加 16。 -/
private def emitOneMeta (i : Nat) (m : Ops.CpiMeta) : String :=
  let base := 16 * i
  let w := if m.writable then 1 else 0
  let s := if m.signer then 1 else 0
  let physical := m.acc + 1
  s!"\
  ldxdw r8, [r10 - {headerStack physical}]
  mov64 r1, r8
  add64 r1, 8
  stxdw [r5 + {base}], r1
  lddw r1, {w}
  stxb [r5 + {base + 8}], r1
  lddw r1, {s}
  stxb [r5 + {base + 9}], r1
  lddw r1, 0
  stxb [r5 + {base + 10}], r1
  stxb [r5 + {base + 11}], r1
  stxb [r5 + {base + 12}], r1
  stxb [r5 + {base + 13}], r1
  stxb [r5 + {base + 14}], r1
  stxb [r5 + {base + 15}], r1
"

/-- Optional target-owned account shape constraints run immediately before the CPI. -/
private def emitCpiDataLenChecks (label : String) (metas : Array Ops.CpiMeta) : String :=
  let constrained := metas.filter (·.expectedDataLen.isSome)
  if constrained.isEmpty then ""
  else Id.run do
    let err := s!"cpi_data_len_err_{label}"
    let ok := s!"cpi_data_len_ok_{label}"
    let mut out := "  ; validate statically constrained CPI account data lengths\n"
    for entry in constrained do
      let some expected := entry.expectedDataLen | unreachable!
      let physical := entry.acc + 1
      out := out ++
        s!"  ldxdw r8, [r10 - {headerStack physical}]\n" ++
        s!"  ldxdw r1, [r8 + 80]\n  jne r1, {expected}, {err}\n"
    return out ++ s!"\
  ja {ok}
{err}:
  lddw r0, 0x1
  exit
{ok}:
"

private def emitSignerSeeds (p : IR.Program) (scope : String) (seedOff : Nat)
    (seeds : Array Ops.PdaSeed) (bump : Option Ops.Val) : Except String (String × String) :=
  match bump with
  | some b => do
    if seeds.isEmpty then
      throw "extract/unsupported: invoke signer seeds cannot be empty"
    let load ← loadVal p b 8 seedOff s!"{scope}_seed"
    let byteCount := seeds.foldl (init := 0) fun total seed =>
      match seed with
      | .ascii value => total + value.length
      | _ => total
    let bumpByte := ((seedOff + byteCount + 7) / 8) * 8
    let seedsArr := bumpByte + 8
    let mut bytes := ""
    let mut entries := ""
    let mut byteOff := seedOff
    for i in [0:seeds.size] do
      match seeds[i]! with
      | .ascii value =>
          let start := byteOff
          for c in value.toList do
            bytes := bytes ++ s!"  lddw r1, {c.toNat}\n  stxb [r9 + {byteOff}], r1\n"
            byteOff := byteOff + 1
          entries := entries ++ s!"\
  mov64 r1, r9
  add64 r1, {start}
  stxdw [r9 + {seedsArr + 16 * i}], r1
  lddw r1, {value.length}
  stxdw [r9 + {seedsArr + 16 * i + 8}], r1
"
      | .stateKey =>
          entries := entries ++ s!"\
  ldxdw r1, [r10 - {headerStack 0}]
  add64 r1, 8
  stxdw [r9 + {seedsArr + 16 * i}], r1
  lddw r1, 32
  stxdw [r9 + {seedsArr + 16 * i + 8}], r1
"
      | .accKey account =>
          entries := entries ++ s!"\
  ldxdw r1, [r10 - {headerStack (account + 1)}]
  add64 r1, 8
  stxdw [r9 + {seedsArr + 16 * i}], r1
  lddw r1, 32
  stxdw [r9 + {seedsArr + 16 * i + 8}], r1
"
    let bumpEntry := seedsArr + 16 * seeds.size
    let groupOff := bumpEntry + 16
    let txt :=
      load ++ bytes ++ entries ++ s!"\
  ldxdw r1, [r10 - 8]
  stxb [r9 + {bumpByte}], r1
  mov64 r1, r9
  add64 r1, {bumpByte}
  stxdw [r9 + {bumpEntry}], r1
  lddw r1, 1
  stxdw [r9 + {bumpEntry + 8}], r1
  mov64 r1, r9
  add64 r1, {seedsArr}
  stxdw [r9 + {groupOff}], r1
  lddw r1, {seeds.size + 1}
  stxdw [r9 + {groupOff + 8}], r1
"
    let regs :=
      s!"  mov64 r4, r9\n  add64 r4, {groupOff}\n  lddw r5, 1\n"
    return (txt, regs)
  | none =>
    if seeds.isEmpty then
      return ("", "  lddw r4, 0\n  lddw r5, 0\n")
    else
      throw "extract/unsupported: invoke signer seeds require a bump"

private def emitInvoke (p : IR.Program) (label : String)
    (programIx : Nat) (metas : Array Ops.CpiMeta) (data : Array (Ops.CpiWord Ops.Val))
    (seeds : Array Ops.PdaSeed) (bump : Option Ops.Val) :
    Except String String := do
  let n := IR.cpiAccountCount p
  let physicalProgramIx := programIx + 1
  let metaOff := 0
  let ixOff := metaOff + 16 * metas.size
  let dataOff := ixOff + 40
  let (dataTxt, dataLen) ← emitCpiData p label dataOff data
  let infoOff := dataOff + ((dataLen + 7) / 8) * 8
  let seedOff := infoOff + 56 * n
  let (seedTxt, seedRegs) ← emitSignerSeeds p label seedOff seeds bump
  let mut metasTxt := ""
  for i in [0:metas.size] do
    metasTxt := metasTxt ++ emitOneMeta i metas[i]!
  let mut infos := ""
  for i in [0:n] do
    infos := infos ++ emitFillAccountInfoFromHeader label (headerStack i)
    if i + 1 < n then
      infos := infos ++ "  add64 r5, 56\n"
  let programIdPtr :=
    match data[0]? with
    | some (.selfEntry _ _) =>
        s!"\
  ldxdw r1, [r10 - {headerStack n}]
  ldxdw r2, [r1 + 0]
  add64 r1, 8
  add64 r1, r2
"
    | _ =>
        s!"  ldxdw r1, [r10 - {headerStack physicalProgramIx}]\n  add64 r1, 8\n"
  let dataLenChecks := emitCpiDataLenChecks label metas
  return s!"\
  ; invoke programIx={physicalProgramIx} metas={metas.size} dataLen={dataLen}
{dataLenChecks}\
  mov64 r9, r10
  add64 r9, -2048
{dataTxt}  mov64 r5, r9
  add64 r5, {metaOff}
{metasTxt}  mov64 r8, r9
  add64 r8, {ixOff}
{programIdPtr}  ; raw self-entry invocations use the current program id, not caller-supplied data
  stxdw [r8 + 0], r1
  mov64 r1, r9
  add64 r1, {metaOff}
  stxdw [r8 + 8], r1
  lddw r1, {metas.size}
  stxdw [r8 + 16], r1
  mov64 r1, r9
  add64 r1, {dataOff}
  stxdw [r8 + 24], r1
  lddw r1, {dataLen}
  stxdw [r8 + 32], r1
  stxdw [r10 - 112], r8
  mov64 r5, r9
  add64 r5, {infoOff}
{infos}{seedTxt}  ldxdw r1, [r10 - 112]
  mov64 r2, r9
  add64 r2, {infoOff}
  lddw r3, {n}
{seedRegs}  call sol_invoke_signed_c
  jeq r0, 0, xfer_ok_{label}
  exit
xfer_ok_{label}:
"

/-- Store one u64 in a statically shaped external-account slot. All authorization and bounds
checks precede the store, so failure cannot expose a partial write from this effect. -/
private def emitAccDataWordSetAt (p : IR.Program) (label : String)
    (acc baseWord strideWords capacity : Nat) (index value : Ops.Val) :
    Except String String := do
  let loadIndex ← loadVal p index 8 0 s!"{label}_index"
  let loadValue ← loadVal p value 16 1 s!"{label}_value"
  let ownerCheck := emitLoadOwnerIsSelf p acc 24 s!"{label}_owner"
  let baseBytes := 8 * baseWord
  let strideBytes := 8 * strideWords
  let writable := s!"dws_writable_{label}"
  let ownerOk := s!"dws_owner_ok_{label}"
  let indexOk := s!"dws_index_ok_{label}"
  let dataOk := s!"dws_data_ok_{label}"
  let done := s!"dws_done_{label}"
  let failure := s!"dws_failure_{label}"
  return loadIndex ++ loadValue ++ ownerCheck ++ s!"\
  ; fixed-stride external account word write acc={acc} base={baseWord} stride={strideWords} capacity={capacity}
  ldxdw r8, [r10 - {headerStack acc}]
  ldxb r1, [r8 + 2]
  jne r1, 0, {writable}
  ja {failure}
{writable}:
  ldxdw r1, [r10 - 24]
  jeq r1, 0, {ownerOk}
  ja {failure}
{ownerOk}:
  ldxdw r2, [r10 - 8]
  lddw r1, {capacity}
  jlt r2, r1, {indexOk}
  ja {failure}
{indexOk}:
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

/-- Insert into a complete account-resident Sokoban red-black tree. Validation and every
duplicate/full check precede the first store. The insertion search and fixup retain only bounded
scalar indexes; the two local rotation helpers receive the account-data pointer and one-based
indexes, and never expose pointers to persistent state. -/
private def emitAccDataRbTreeKey4Insert (p : IR.Program) (label : String)
    (acc rootWord linksBaseWord parentBaseWord keyBaseWord strideWords capacity : Nat)
    (key0 key1 key2 key3 : Ops.Val) : Except String String := do
  let loadKey0 ← loadVal p key0 8 0 s!"{label}_key0"
  let loadKey1 ← loadVal p key1 16 1 s!"{label}_key1"
  let loadKey2 ← loadVal p key2 24 2 s!"{label}_key2"
  let loadKey3 ← loadVal p key3 32 3 s!"{label}_key3"
  let ownerCheck := emitLoadOwnerIsSelf p acc 216 s!"{label}_owner"
  let validate ← emitLoadAccDataRbTreeKey4Valid p acc linksBaseWord parentBaseWord
    keyBaseWord strideWords capacity
    (Ops.accDataWord acc rootWord) (Ops.accDataWord acc (rootWord + 2))
    (.bitAnd (Ops.accDataWord acc (rootWord + 3)) (.lit 0xffffffff))
    (.shiftR (Ops.accDataWord acc (rootWord + 3)) (.lit 32))
    40 4 s!"{label}_preflight"
  let strideBytes := 8 * strideWords
  let linksBaseBytes := 8 * linksBaseWord
  let parentBaseBytes := 8 * parentBaseWord
  let keyBaseBytes := 8 * keyBaseWord
  let rootBytes := 8 * rootWord
  let finalWord := linksBaseWord + strideWords - 1 + strideWords * (capacity - 1)
  let requiredBytes := 8 * (Nat.max (rootWord + 3) finalWord + 1)
  let keyRelativeBytes := keyBaseBytes - linksBaseBytes
  let parentRelativeBytes := parentBaseBytes - linksBaseBytes
  let clearNode := (List.range strideWords).foldl (init := "") fun text i =>
    text ++ s!"  stxdw [r9 + {8 * i}], r1\n"
  let token := IR.u64Hex (Core.IR.fnv1a64
    (s!"{label}:{acc}:{rootWord}:{linksBaseWord}:{parentBaseWord}:{keyBaseWord}:" ++
      s!"{strideWords}:{capacity}"))
  let tag := s!"rb4i_{token}"
  let authFailure := tag ++ "_auth_failure"
  let failure := tag ++ "_failure"
  let full := tag ++ "_full"
  let dataOk := tag ++ "_data_ok"
  let searchLoop := tag ++ "_search_loop"
  let searchBefore := tag ++ "_search_before"
  let searchAfter := tag ++ "_search_after"
  let searchNext := tag ++ "_search_next"
  let searchDone := tag ++ "_search_done"
  let freePath := tag ++ "_free_path"
  let allocated := tag ++ "_allocated"
  let attachRight := tag ++ "_attach_right"
  let attached := tag ++ "_attached"
  let firstRoot := tag ++ "_first_root"
  let fixLoop := tag ++ "_fix_loop"
  let fixLeft := tag ++ "_fix_left"
  let fixRight := tag ++ "_fix_right"
  let leftBlackUncle := tag ++ "_left_black_uncle"
  let rightBlackUncle := tag ++ "_right_black_uncle"
  let leftAligned := tag ++ "_left_aligned"
  let rightAligned := tag ++ "_right_aligned"
  let fixDone := tag ++ "_fix_done"
  let publish := tag ++ "_publish"
  let helpersDone := tag ++ "_helpers_done"
  let rotateLeft := "function_" ++ tag ++ "_rotate_left"
  let rotateRight := "function_" ++ tag ++ "_rotate_right"
  let leftHasGrand := tag ++ "_rotl_has_grand"
  let leftGrandRight := tag ++ "_rotl_grand_right"
  let leftGrandDone := tag ++ "_rotl_grand_done"
  let leftNoChild := tag ++ "_rotl_no_child"
  let rightHasGrand := tag ++ "_rotr_has_grand"
  let rightGrandRight := tag ++ "_rotr_grand_right"
  let rightGrandDone := tag ++ "_rotr_grand_done"
  let rightNoChild := tag ++ "_rotr_no_child"
  let rotationHelpers := s!"\
{rotateLeft}:
  ; args: r1=data, r2=x, r3=root; result: r0=new root
  stxdw [r10 - 8], r1
  stxdw [r10 - 16], r2
  stxdw [r10 - 24], r3
  mov64 r4, r2
  sub64 r4, 1
  lddw r5, {strideBytes}
  mul64 r4, r5
  mov64 r5, r1
  add64 r5, {linksBaseBytes}
  add64 r5, r4
  stxdw [r10 - 32], r5
  ; Save x's old parent before connecting the pivot.
  mov64 r5, r1
  add64 r5, {parentBaseBytes}
  add64 r5, r4
  ldxdw r4, [r5 + 0]
  lsh64 r4, 32
  rsh64 r4, 32
  stxdw [r10 - 40], r4
  ldxdw r5, [r10 - 32]
  ldxdw r4, [r5 + 0]
  rsh64 r4, 32
  stxdw [r10 - 48], r4
  ; y links pointer and beta=y.left.
  sub64 r4, 1
  lddw r5, {strideBytes}
  mul64 r4, r5
  ldxdw r1, [r10 - 8]
  mov64 r5, r1
  add64 r5, {linksBaseBytes}
  add64 r5, r4
  stxdw [r10 - 56], r5
  ldxdw r4, [r5 + 0]
  mov64 r1, r4
  lsh64 r1, 32
  rsh64 r1, 32
  stxdw [r10 - 64], r1
  ; y.left=x.
  rsh64 r4, 32
  lsh64 r4, 32
  ldxdw r2, [r10 - 16]
  or64 r4, r2
  stxdw [r5 + 0], r4
  ; x.right=beta.
  ldxdw r5, [r10 - 32]
  ldxdw r4, [r5 + 0]
  lsh64 r4, 32
  rsh64 r4, 32
  ldxdw r1, [r10 - 64]
  lsh64 r1, 32
  or64 r4, r1
  stxdw [r5 + 0], r4
  ; x.parent=y, preserving x color.
  ldxdw r1, [r10 - 8]
  ldxdw r2, [r10 - 16]
  sub64 r2, 1
  lddw r4, {strideBytes}
  mul64 r2, r4
  add64 r2, {parentBaseBytes}
  add64 r2, r1
  ldxdw r4, [r2 + 0]
  rsh64 r4, 32
  lsh64 r4, 32
  ldxdw r5, [r10 - 48]
  or64 r4, r5
  stxdw [r2 + 0], r4
  ; beta.parent=x when beta is non-sentinel.
  ldxdw r2, [r10 - 64]
  jeq r2, 0, {leftNoChild}
  sub64 r2, 1
  lddw r4, {strideBytes}
  mul64 r2, r4
  add64 r2, {parentBaseBytes}
  add64 r2, r1
  ldxdw r4, [r2 + 0]
  rsh64 r4, 32
  lsh64 r4, 32
  ldxdw r5, [r10 - 16]
  or64 r4, r5
  stxdw [r2 + 0], r4
{leftNoChild}:
  ; y.parent=old grandparent, preserving y color.
  ldxdw r2, [r10 - 48]
  sub64 r2, 1
  lddw r4, {strideBytes}
  mul64 r2, r4
  mov64 r5, r1
  add64 r5, {parentBaseBytes}
  add64 r5, r2
  ldxdw r4, [r5 + 0]
  rsh64 r4, 32
  lsh64 r4, 32
  ldxdw r2, [r10 - 40]
  or64 r4, r2
  stxdw [r5 + 0], r4
  jne r2, 0, {leftHasGrand}
  ldxdw r2, [r10 - 48]
  stxdw [r10 - 24], r2
  ja {leftGrandDone}
{leftHasGrand}:
  sub64 r2, 1
  lddw r4, {strideBytes}
  mul64 r2, r4
  add64 r2, {linksBaseBytes}
  add64 r2, r1
  ldxdw r4, [r2 + 0]
  mov64 r5, r4
  lsh64 r5, 32
  rsh64 r5, 32
  ldxdw r3, [r10 - 16]
  jne r5, r3, {leftGrandRight}
  rsh64 r4, 32
  lsh64 r4, 32
  ldxdw r5, [r10 - 48]
  or64 r4, r5
  stxdw [r2 + 0], r4
  ja {leftGrandDone}
{leftGrandRight}:
  lsh64 r4, 32
  rsh64 r4, 32
  ldxdw r5, [r10 - 48]
  lsh64 r5, 32
  or64 r4, r5
  stxdw [r2 + 0], r4
{leftGrandDone}:
  ldxdw r0, [r10 - 24]
  exit

{rotateRight}:
  ; symmetric right rotation
  stxdw [r10 - 8], r1
  stxdw [r10 - 16], r2
  stxdw [r10 - 24], r3
  mov64 r4, r2
  sub64 r4, 1
  lddw r5, {strideBytes}
  mul64 r4, r5
  mov64 r5, r1
  add64 r5, {linksBaseBytes}
  add64 r5, r4
  stxdw [r10 - 32], r5
  mov64 r5, r1
  add64 r5, {parentBaseBytes}
  add64 r5, r4
  ldxdw r4, [r5 + 0]
  lsh64 r4, 32
  rsh64 r4, 32
  stxdw [r10 - 40], r4
  ldxdw r5, [r10 - 32]
  ldxdw r4, [r5 + 0]
  lsh64 r4, 32
  rsh64 r4, 32
  stxdw [r10 - 48], r4
  ; y links pointer and beta=y.right.
  sub64 r4, 1
  lddw r5, {strideBytes}
  mul64 r4, r5
  ldxdw r1, [r10 - 8]
  mov64 r5, r1
  add64 r5, {linksBaseBytes}
  add64 r5, r4
  stxdw [r10 - 56], r5
  ldxdw r4, [r5 + 0]
  mov64 r1, r4
  rsh64 r1, 32
  stxdw [r10 - 64], r1
  ; y.right=x.
  lsh64 r4, 32
  rsh64 r4, 32
  ldxdw r2, [r10 - 16]
  lsh64 r2, 32
  or64 r4, r2
  stxdw [r5 + 0], r4
  ; x.left=beta.
  ldxdw r5, [r10 - 32]
  ldxdw r4, [r5 + 0]
  rsh64 r4, 32
  lsh64 r4, 32
  ldxdw r1, [r10 - 64]
  or64 r4, r1
  stxdw [r5 + 0], r4
  ; x.parent=y, preserving x color.
  ldxdw r1, [r10 - 8]
  ldxdw r2, [r10 - 16]
  sub64 r2, 1
  lddw r4, {strideBytes}
  mul64 r2, r4
  add64 r2, {parentBaseBytes}
  add64 r2, r1
  ldxdw r4, [r2 + 0]
  rsh64 r4, 32
  lsh64 r4, 32
  ldxdw r5, [r10 - 48]
  or64 r4, r5
  stxdw [r2 + 0], r4
  ; beta.parent=x when beta is non-sentinel.
  ldxdw r2, [r10 - 64]
  jeq r2, 0, {rightNoChild}
  sub64 r2, 1
  lddw r4, {strideBytes}
  mul64 r2, r4
  add64 r2, {parentBaseBytes}
  add64 r2, r1
  ldxdw r4, [r2 + 0]
  rsh64 r4, 32
  lsh64 r4, 32
  ldxdw r5, [r10 - 16]
  or64 r4, r5
  stxdw [r2 + 0], r4
{rightNoChild}:
  ; y.parent=old grandparent, preserving y color.
  ldxdw r2, [r10 - 48]
  sub64 r2, 1
  lddw r4, {strideBytes}
  mul64 r2, r4
  mov64 r5, r1
  add64 r5, {parentBaseBytes}
  add64 r5, r2
  ldxdw r4, [r5 + 0]
  rsh64 r4, 32
  lsh64 r4, 32
  ldxdw r2, [r10 - 40]
  or64 r4, r2
  stxdw [r5 + 0], r4
  jne r2, 0, {rightHasGrand}
  ldxdw r2, [r10 - 48]
  stxdw [r10 - 24], r2
  ja {rightGrandDone}
{rightHasGrand}:
  sub64 r2, 1
  lddw r4, {strideBytes}
  mul64 r2, r4
  add64 r2, {linksBaseBytes}
  add64 r2, r1
  ldxdw r4, [r2 + 0]
  mov64 r5, r4
  lsh64 r5, 32
  rsh64 r5, 32
  ldxdw r3, [r10 - 16]
  jne r5, r3, {rightGrandRight}
  rsh64 r4, 32
  lsh64 r4, 32
  ldxdw r5, [r10 - 48]
  or64 r4, r5
  stxdw [r2 + 0], r4
  ja {rightGrandDone}
{rightGrandRight}:
  lsh64 r4, 32
  rsh64 r4, 32
  ldxdw r5, [r10 - 48]
  lsh64 r5, 32
  or64 r4, r5
  stxdw [r2 + 0], r4
{rightGrandDone}:
  ldxdw r0, [r10 - 24]
  exit
"
  return loadKey0 ++ loadKey1 ++ loadKey2 ++ loadKey3 ++ ownerCheck ++ s!"\
  ; bounded account-resident four-word-key RB insertion
  ; root={rootWord} links={linksBaseWord} parent={parentBaseWord} key4={keyBaseWord} stride={strideWords} capacity={capacity}
  ldxdw r1, [r10 - 216]
  jne r1, 0, {authFailure}
  ldxdw r8, [r10 - {headerStack acc}]
  ldxb r1, [r8 + 2]
  jeq r1, 0, {authFailure}
  ldxdw r1, [r8 + 80]
  lddw r2, {requiredBytes}
  jge r1, r2, {dataOk}
  ja {authFailure}
{dataOk}:
" ++ validate ++ s!"\
  ldxdw r1, [r10 - 40]
  jeq r1, 0, {failure}
  ldxdw r8, [r10 - {headerStack acc}]
  add64 r8, 88
  stxdw [r10 - 248], r8
  mov64 r9, r8
  lddw r1, {rootBytes}
  add64 r9, r1
  ldxdw r1, [r9 + 0]
  stxdw [r10 - 216], r1
  ldxdw r1, [r9 + 16]
  stxdw [r10 - 224], r1
  ldxdw r1, [r9 + 24]
  mov64 r2, r1
  lsh64 r2, 32
  rsh64 r2, 32
  stxdw [r10 - 232], r2
  rsh64 r1, 32
  stxdw [r10 - 240], r1
  ldxdw r1, [r10 - 216]
  stxdw [r10 - 256], r1
  lddw r1, 0
  stxdw [r10 - 264], r1
  stxdw [r10 - 272], r1
  stxdw [r10 - 296], r1
{searchLoop}:
  ldxdw r2, [r10 - 256]
  jeq r2, 0, {searchDone}
  ldxdw r1, [r10 - 296]
  lddw r3, {rbTreeKey4TraversalDepth}
  jge r1, r3, {failure}
  mov64 r4, r2
  sub64 r4, 1
  lddw r1, {strideBytes}
  mul64 r4, r1
  ldxdw r8, [r10 - 248]
  mov64 r9, r8
  add64 r9, {linksBaseBytes}
  add64 r9, r4
  add64 r8, {keyBaseBytes}
  add64 r8, r4
  ldxdw r1, [r10 - 8]
  be64 r1
  ldxdw r3, [r8 + 0]
  be64 r3
  jlt r1, r3, {searchBefore}
  jgt r1, r3, {searchAfter}
  ldxdw r1, [r10 - 16]
  be64 r1
  ldxdw r3, [r8 + 8]
  be64 r3
  jlt r1, r3, {searchBefore}
  jgt r1, r3, {searchAfter}
  ldxdw r1, [r10 - 24]
  be64 r1
  ldxdw r3, [r8 + 16]
  be64 r3
  jlt r1, r3, {searchBefore}
  jgt r1, r3, {searchAfter}
  ldxdw r1, [r10 - 32]
  be64 r1
  ldxdw r3, [r8 + 24]
  be64 r3
  jlt r1, r3, {searchBefore}
  jgt r1, r3, {searchAfter}
  ; Duplicate registrations fail instead of replacing TraderState.
  ja {failure}
{searchBefore}:
  lddw r1, 0
  stxdw [r10 - 272], r1
  ldxdw r1, [r9 + 0]
  lsh64 r1, 32
  rsh64 r1, 32
  ja {searchNext}
{searchAfter}:
  lddw r1, 1
  stxdw [r10 - 272], r1
  ldxdw r1, [r9 + 0]
  rsh64 r1, 32
{searchNext}:
  stxdw [r10 - 264], r2
  stxdw [r10 - 256], r1
  ldxdw r1, [r10 - 296]
  add64 r1, 1
  stxdw [r10 - 296], r1
  ja {searchLoop}
{searchDone}:
  ldxdw r1, [r10 - 224]
  lddw r2, {capacity}
  jge r1, r2, {full}
  ldxdw r1, [r10 - 240]
  ldxdw r2, [r10 - 232]
  jne r1, r2, {freePath}
  stxdw [r10 - 280], r2
  add64 r2, 1
  stxdw [r10 - 232], r2
  stxdw [r10 - 240], r2
  ja {allocated}
{freePath}:
  stxdw [r10 - 280], r1
  mov64 r2, r1
  sub64 r2, 1
  lddw r3, {strideBytes}
  mul64 r2, r3
  ldxdw r8, [r10 - 248]
  add64 r8, {linksBaseBytes}
  add64 r8, r2
  ldxdw r1, [r8 + 0]
  lsh64 r1, 32
  rsh64 r1, 32
  stxdw [r10 - 240], r1
{allocated}:
  ; Fully initialize the allocated slot before linking it into the tree.
  ldxdw r2, [r10 - 280]
  sub64 r2, 1
  lddw r3, {strideBytes}
  mul64 r2, r3
  ldxdw r8, [r10 - 248]
  mov64 r9, r8
  add64 r9, {linksBaseBytes}
  add64 r9, r2
  lddw r1, 0
{clearNode}  ldxdw r1, [r10 - 8]
  stxdw [r9 + {keyRelativeBytes}], r1
  ldxdw r1, [r10 - 16]
  stxdw [r9 + {keyRelativeBytes + 8}], r1
  ldxdw r1, [r10 - 24]
  stxdw [r9 + {keyRelativeBytes + 16}], r1
  ldxdw r1, [r10 - 32]
  stxdw [r9 + {keyRelativeBytes + 24}], r1
  ldxdw r1, [r10 - 264]
  lddw r3, 1
  lsh64 r3, 32
  or64 r1, r3
  stxdw [r9 + {parentRelativeBytes}], r1
  ldxdw r1, [r10 - 264]
  jeq r1, 0, {firstRoot}
  sub64 r1, 1
  lddw r3, {strideBytes}
  mul64 r1, r3
  add64 r8, {linksBaseBytes}
  add64 r8, r1
  ldxdw r3, [r8 + 0]
  ldxdw r1, [r10 - 272]
  jne r1, 0, {attachRight}
  rsh64 r3, 32
  lsh64 r3, 32
  ldxdw r1, [r10 - 280]
  or64 r3, r1
  stxdw [r8 + 0], r3
  ja {attached}
{attachRight}:
  lsh64 r3, 32
  rsh64 r3, 32
  ldxdw r1, [r10 - 280]
  lsh64 r1, 32
  or64 r3, r1
  stxdw [r8 + 0], r3
{attached}:
  ldxdw r1, [r10 - 280]
  stxdw [r10 - 256], r1
  lddw r1, 0
  stxdw [r10 - 296], r1
  ja {fixLoop}
{firstRoot}:
  ldxdw r1, [r10 - 280]
  stxdw [r10 - 216], r1
  lddw r1, 0
  stxdw [r9 + {parentRelativeBytes}], r1
  ja {publish}
{fixLoop}:
  ldxdw r1, [r10 - 296]
  lddw r2, {rbTreeKey4TraversalDepth}
  jge r1, r2, {failure}
  add64 r1, 1
  stxdw [r10 - 296], r1
  ; parent and color of z
  ldxdw r2, [r10 - 256]
  sub64 r2, 1
  lddw r3, {strideBytes}
  mul64 r2, r3
  ldxdw r8, [r10 - 248]
  add64 r8, {parentBaseBytes}
  add64 r8, r2
  ldxdw r3, [r8 + 0]
  mov64 r1, r3
  lsh64 r1, 32
  rsh64 r1, 32
  jeq r1, 0, {fixDone}
  stxdw [r10 - 264], r1
  ; Continue only when parent p is red, then load its parent g.
  mov64 r2, r1
  sub64 r2, 1
  lddw r3, {strideBytes}
  mul64 r2, r3
  ldxdw r8, [r10 - 248]
  mov64 r9, r8
  add64 r9, {parentBaseBytes}
  add64 r9, r2
  ldxdw r3, [r9 + 0]
  mov64 r4, r3
  rsh64 r4, 32
  jeq r4, 0, {fixDone}
  lsh64 r3, 32
  rsh64 r3, 32
  jeq r3, 0, {fixDone}
  stxdw [r10 - 288], r3
  ; Determine whether p is grandparent.left.
  sub64 r3, 1
  lddw r4, {strideBytes}
  mul64 r3, r4
  add64 r8, {linksBaseBytes}
  add64 r8, r3
  ldxdw r4, [r8 + 0]
  mov64 r2, r4
  lsh64 r2, 32
  rsh64 r2, 32
  ldxdw r1, [r10 - 264]
  jeq r1, r2, {fixLeft}
  ja {fixRight}
{fixLeft}:
  ; Uncle is grandparent.right. Sentinel color is black.
  rsh64 r4, 32
  jeq r4, 0, {leftBlackUncle}
  mov64 r2, r4
  sub64 r2, 1
  lddw r3, {strideBytes}
  mul64 r2, r3
  ldxdw r9, [r10 - 248]
  add64 r9, {parentBaseBytes}
  add64 r9, r2
  ldxdw r3, [r9 + 0]
  rsh64 r3, 32
  jeq r3, 0, {leftBlackUncle}
  ; Red uncle: p and uncle black, grandparent red, then continue at grandparent.
  ldxdw r1, [r10 - 288]
  ldxdw r2, [r10 - 264]
  sub64 r2, 1
  lddw r3, {strideBytes}
  mul64 r2, r3
  ldxdw r8, [r10 - 248]
  add64 r8, {parentBaseBytes}
  add64 r8, r2
  stxdw [r8 + 0], r1
  stxdw [r9 + 0], r1
  mov64 r2, r1
  sub64 r2, 1
  lddw r3, {strideBytes}
  mul64 r2, r3
  ldxdw r8, [r10 - 248]
  add64 r8, {parentBaseBytes}
  add64 r8, r2
  ldxdw r3, [r8 + 0]
  lsh64 r3, 32
  rsh64 r3, 32
  lddw r2, 1
  lsh64 r2, 32
  or64 r3, r2
  stxdw [r8 + 0], r3
  stxdw [r10 - 256], r1
  ja {fixLoop}
{leftBlackUncle}:
  ; Inner child: rotate p left and continue with z=old p.
  ldxdw r2, [r10 - 264]
  sub64 r2, 1
  lddw r3, {strideBytes}
  mul64 r2, r3
  ldxdw r8, [r10 - 248]
  add64 r8, {linksBaseBytes}
  add64 r8, r2
  ldxdw r3, [r8 + 0]
  rsh64 r3, 32
  ldxdw r1, [r10 - 256]
  jne r1, r3, {leftAligned}
  ldxdw r1, [r10 - 248]
  ldxdw r2, [r10 - 264]
  ldxdw r3, [r10 - 216]
  call {rotateLeft}
  stxdw [r10 - 216], r0
  ldxdw r1, [r10 - 264]
  stxdw [r10 - 256], r1
{leftAligned}:
  ; Recompute p/g, recolor, and rotate g right.
  ldxdw r2, [r10 - 256]
  sub64 r2, 1
  lddw r3, {strideBytes}
  mul64 r2, r3
  ldxdw r8, [r10 - 248]
  add64 r8, {parentBaseBytes}
  add64 r8, r2
  ldxdw r1, [r8 + 0]
  lsh64 r1, 32
  rsh64 r1, 32
  stxdw [r10 - 264], r1
  mov64 r2, r1
  sub64 r2, 1
  lddw r3, {strideBytes}
  mul64 r2, r3
  ldxdw r8, [r10 - 248]
  add64 r8, {parentBaseBytes}
  add64 r8, r2
  ldxdw r2, [r8 + 0]
  lsh64 r2, 32
  rsh64 r2, 32
  stxdw [r10 - 288], r2
  ; p becomes black while retaining g as its parent.
  stxdw [r8 + 0], r2
  ; g becomes red while retaining its own parent.
  sub64 r2, 1
  lddw r3, {strideBytes}
  mul64 r2, r3
  ldxdw r9, [r10 - 248]
  add64 r9, {parentBaseBytes}
  add64 r9, r2
  ldxdw r2, [r9 + 0]
  lsh64 r2, 32
  rsh64 r2, 32
  lddw r3, 1
  lsh64 r3, 32
  or64 r2, r3
  stxdw [r9 + 0], r2
  ldxdw r1, [r10 - 248]
  ldxdw r2, [r10 - 288]
  ldxdw r3, [r10 - 216]
  call {rotateRight}
  stxdw [r10 - 216], r0
  ja {fixLoop}
{fixRight}:
  ; Uncle is grandparent.left. Sentinel color is black.
  lsh64 r4, 32
  rsh64 r4, 32
  jeq r4, 0, {rightBlackUncle}
  mov64 r2, r4
  sub64 r2, 1
  lddw r3, {strideBytes}
  mul64 r2, r3
  ldxdw r9, [r10 - 248]
  add64 r9, {parentBaseBytes}
  add64 r9, r2
  ldxdw r3, [r9 + 0]
  rsh64 r3, 32
  jeq r3, 0, {rightBlackUncle}
  ldxdw r1, [r10 - 288]
  ldxdw r2, [r10 - 264]
  sub64 r2, 1
  lddw r3, {strideBytes}
  mul64 r2, r3
  ldxdw r8, [r10 - 248]
  add64 r8, {parentBaseBytes}
  add64 r8, r2
  stxdw [r8 + 0], r1
  stxdw [r9 + 0], r1
  mov64 r2, r1
  sub64 r2, 1
  lddw r3, {strideBytes}
  mul64 r2, r3
  ldxdw r8, [r10 - 248]
  add64 r8, {parentBaseBytes}
  add64 r8, r2
  ldxdw r3, [r8 + 0]
  lsh64 r3, 32
  rsh64 r3, 32
  lddw r2, 1
  lsh64 r2, 32
  or64 r3, r2
  stxdw [r8 + 0], r3
  stxdw [r10 - 256], r1
  ja {fixLoop}
{rightBlackUncle}:
  ; Inner child: rotate p right and continue with z=old p.
  ldxdw r2, [r10 - 264]
  sub64 r2, 1
  lddw r3, {strideBytes}
  mul64 r2, r3
  ldxdw r8, [r10 - 248]
  add64 r8, {linksBaseBytes}
  add64 r8, r2
  ldxdw r3, [r8 + 0]
  lsh64 r3, 32
  rsh64 r3, 32
  ldxdw r1, [r10 - 256]
  jne r1, r3, {rightAligned}
  ldxdw r1, [r10 - 248]
  ldxdw r2, [r10 - 264]
  ldxdw r3, [r10 - 216]
  call {rotateRight}
  stxdw [r10 - 216], r0
  ldxdw r1, [r10 - 264]
  stxdw [r10 - 256], r1
{rightAligned}:
  ; Recompute p/g, recolor, and rotate g left.
  ldxdw r2, [r10 - 256]
  sub64 r2, 1
  lddw r3, {strideBytes}
  mul64 r2, r3
  ldxdw r8, [r10 - 248]
  add64 r8, {parentBaseBytes}
  add64 r8, r2
  ldxdw r1, [r8 + 0]
  lsh64 r1, 32
  rsh64 r1, 32
  stxdw [r10 - 264], r1
  mov64 r2, r1
  sub64 r2, 1
  lddw r3, {strideBytes}
  mul64 r2, r3
  ldxdw r8, [r10 - 248]
  add64 r8, {parentBaseBytes}
  add64 r8, r2
  ldxdw r2, [r8 + 0]
  lsh64 r2, 32
  rsh64 r2, 32
  stxdw [r10 - 288], r2
  ; p becomes black while retaining g as its parent.
  stxdw [r8 + 0], r2
  ; g becomes red while retaining its own parent.
  sub64 r2, 1
  lddw r3, {strideBytes}
  mul64 r2, r3
  ldxdw r9, [r10 - 248]
  add64 r9, {parentBaseBytes}
  add64 r9, r2
  ldxdw r2, [r9 + 0]
  lsh64 r2, 32
  rsh64 r2, 32
  lddw r3, 1
  lsh64 r3, 32
  or64 r2, r3
  stxdw [r9 + 0], r2
  ldxdw r1, [r10 - 248]
  ldxdw r2, [r10 - 288]
  ldxdw r3, [r10 - 216]
  call {rotateLeft}
  stxdw [r10 - 216], r0
  ja {fixLoop}
{fixDone}:
  ; Root parent/color is always the packed black sentinel.
  ldxdw r2, [r10 - 216]
  sub64 r2, 1
  lddw r3, {strideBytes}
  mul64 r2, r3
  ldxdw r8, [r10 - 248]
  add64 r8, {parentBaseBytes}
  add64 r8, r2
  lddw r1, 0
  stxdw [r8 + 0], r1
{publish}:
  ldxdw r8, [r10 - 248]
  lddw r1, {rootBytes}
  add64 r8, r1
  ldxdw r1, [r10 - 216]
  stxdw [r8 + 0], r1
  ldxdw r1, [r10 - 224]
  add64 r1, 1
  stxdw [r8 + 16], r1
  ldxdw r1, [r10 - 240]
  lsh64 r1, 32
  ldxdw r2, [r10 - 232]
  or64 r1, r2
  stxdw [r8 + 24], r1
  ja {helpersDone}
{authFailure}:
  lddw r0, 0x1
  exit
{failure}:
  lddw r0, {overflowCode}
  exit
{full}:
  lddw r0, 0x1003
  exit
" ++ rotationHelpers ++ s!"{helpersDone}:\n"

private def emitInitBody (p : IR.Program) (marker : String) (label : String) (ops : Array IR.Op) :
    Except String String := do
  let vs := ops.filterMap (fun | .returnState v => some v | _ => none)
  let effects := ops.filter fun | .returnState _ => false | _ => true
  if vs.isEmpty then
    .error "extract/unsupported: init missing returnState"
  else if !p.schema.isEmpty && vs.size != p.slots.size then
    .error (s!"extract/unsupported: init initializes {vs.size} state leaves, " ++
      s!"schema requires {p.slots.size}")
  else if !effects.all (fun | .invoke .. => true | _ => false) then
    .error "extract/unsupported: init contains a non-CPI effect"
  else do
    let mut effectBody := ""
    for i in [0:effects.size] do
      match effects[i]! with
      | .invoke programIx metas data seeds bump =>
          effectBody := effectBody ++
            (← emitInvoke p s!"{label}_init_{i}" programIx metas data seeds bump)
      | _ => pure ()
    let mut body :=
      if IR.usesWalk p then
        s!"  ldxdw r7, [r10 - {headerStack (IR.cpiAccountCount p)}]\n  add64 r7, 8\n"
      else ""
    body := body ++ effectBody
    let mut i : Nat := 0
    for s in p.slots do
      if h : i < vs.size then
        let load ← loadVal p vs[i] 8 i s!"{label}_init_{i}"
        let store ← storeField p s.name 8
        body := body ++ load ++ store
      else
        match IR.fieldOffset p s.name with
        | some off =>
          let insn ← storeInsn s.width
          body := body ++ s!"  lddw r1, 0\n  {insn} [r6 + ACC0_DATA + {off}], r1\n"
        | none => pure ()
      i := i + 1
    return s!"\
body_{label}:
{body}  lddw r1, {marker}
  stxdw [r6 + ACC0_DATA + 0], r1
  lddw r0, 0
  exit
"

private def emitStoreAndReturn (p : IR.Program) (dest : String) (fromStack : Nat) : Except String String := do
  let store ← storeField p dest fromStack
  return store ++ emitReturnU64 fromStack

private def jmpIf (cmp : Ops.Cmp) (thenLab : String) : String :=
  match cmp with
  | .eq => s!"  jeq r1, r2, {thenLab}\n"
  | .ne => s!"  jne r1, r2, {thenLab}\n"
  | .lt => s!"  jlt r1, r2, {thenLab}\n"
  | .le => s!"  jle r1, r2, {thenLab}\n"
  | .gt => s!"  jgt r1, r2, {thenLab}\n"
  | .ge => s!"  jge r1, r2, {thenLab}\n"

private def emitArithOp (errorLabel opLabel : String) (kind : String) : String :=
  match kind with
  | "add" =>
      s!"  lddw r3, 0xffffffffffffffff\n  sub64 r3, r2\n  jgt r1, r3, err_{errorLabel}\n  mov64 r4, r1\n  add64 r4, r2\n"
  | "sub" =>
      s!"  jlt r1, r2, err_{errorLabel}\n  mov64 r4, r1\n  sub64 r4, r2\n"
  | "mul" =>
      s!"  lddw r3, 0xffffffffffffffff\n  jeq r2, 0, mul_ok_{opLabel}\n  div64 r3, r2\n  jgt r1, r3, err_{errorLabel}\nmul_ok_{opLabel}:\n  mov64 r4, r1\n  mul64 r4, r2\n"
  | "div" =>
      s!"  jeq r2, 0, err_{errorLabel}\n  mov64 r4, r1\n  div64 r4, r2\n"
  | "mod" =>
      s!"  jeq r2, 0, err_{errorLabel}\n  mov64 r4, r1\n  mod64 r4, r2\n"
  | _ => ""

private partial def opsTerminate (ops : Array IR.Op) : Bool :=
  ops.any fun
    | .okState _ | .errorOverflow | .errorNamed _ | .returnU64 _ | .returnState _ => true
    | .ite _ _ _ thn els => opsTerminate thn && opsTerminate els
    | _ => false

/--
sBPF branch offsets are signed 16-bit instruction counts. Split large rendered regions by source
line count (an `lddw` is the worst case at two instructions per line) and place relay islands
between chunks. Normal execution jumps over each island; a bypass stays in the same stack frame
while hopping between its relay labels.
-/
private def relayChunks (text : String) (maxLines : Nat := 4096) : Array String := Id.run do
  let mut chunks : Array String := #[]
  let mut current : Array String := #[]
  for line in text.splitOn "\n" do
    current := current.push line
    if current.size == maxLines then
      chunks := chunks.push (String.intercalate "\n" current.toList ++ "\n")
      current := #[]
  unless current.isEmpty do
    chunks := chunks.push (String.intercalate "\n" current.toList ++ "\n")
  return chunks

/-- Preserve normal execution of `body` while exposing a short-hop entry that bypasses it. -/
private def wrapRelayBypass (tag target body : String) : String × String := Id.run do
  let chunks := relayChunks body
  if chunks.size ≤ 1 then
    return (target, body)
  let relay (i : Nat) := s!"relay_jump_{tag}_{i}"
  let normal (i : Nat) := s!"relay_normal_{tag}_{i}"
  let mut out := ""
  for i in [0:chunks.size] do
    out := out ++ chunks[i]!
    let next := if i + 1 == chunks.size then target else relay (i + 1)
    out := out ++ s!"  ja {normal i}\n{relay i}:\n  ja {next}\n{normal i}:\n"
  return (relay 0, out)

/-- Add forward and backward relay chains around a large loop body. -/
private def wrapLoopRelays (tag loopTarget doneTarget body : String) : String × String × String :=
    Id.run do
  let chunks := relayChunks body
  if chunks.size ≤ 1 then
    return (doneTarget, body, loopTarget)
  let forward (i : Nat) := s!"relay_forward_{tag}_{i}"
  let backward (i : Nat) := s!"relay_backward_{tag}_{i}"
  let normal (i : Nat) := s!"relay_loop_normal_{tag}_{i}"
  let mut out := ""
  for i in [0:chunks.size] do
    out := out ++ chunks[i]!
    let nextForward := if i + 1 == chunks.size then doneTarget else forward (i + 1)
    let nextBackward := if i == 0 then loopTarget else backward (i - 1)
    out := out ++ s!"\
  ja {normal i}
{forward i}:
  ja {nextForward}
{backward i}:
  ja {nextBackward}
{normal i}:
"
  return (forward 0, out, backward (chunks.size - 1))

private def emitOkState (p : IR.Program) (label : String) (v : Ops.Val) (fresh : Nat)
    (destHint : String) (hasStore hasIndexSet hasChecked : Bool) :
    Except String (String × Nat) := do
  let mut acc := ""
  let mut n := fresh
  let optionNames := IR.optionLeafNames? p
  if hasStore || hasIndexSet then
    match v with
    | .lit k =>
      acc := acc ++ s!"  lddw r1, 0x{IR.u64Hex k}\n  stxdw [r10 - 24], r1\n"
      acc := acc ++ emitReturnU64 24
    | _ =>
      let load ← loadVal p v 24 n s!"{label}_{n}_ok"
      n := n + 1
      acc := acc ++ load
      acc := acc ++ emitReturnU64 24
  else if optionNames.isSome then
    let (tagName, payName) := optionNames.getD (destHint, destHint)
    match v with
    | .lit 0 =>
      acc := acc ++ "  lddw r1, 0\n  stxdw [r10 - 24], r1\n"
      acc := acc ++ (← storeField p tagName 24)
      acc := acc ++ (← storeField p payName 24)
      acc := acc ++ emitReturnU64 24
    | .lit k =>
      acc := acc ++ "  lddw r1, 1\n  stxdw [r10 - 16], r1\n"
      acc := acc ++ (← storeField p tagName 16)
      acc := acc ++ s!"  lddw r1, 0x{IR.u64Hex k}\n  stxdw [r10 - 24], r1\n"
      acc := acc ++ (← storeField p payName 24)
      acc := acc ++ emitReturnU64 24
    | _ =>
      let load ← loadVal p v 24 n s!"{label}_{n}_option"
      n := n + 1
      acc := acc ++ "  lddw r1, 1\n  stxdw [r10 - 16], r1\n"
      acc := acc ++ (← storeField p tagName 16)
      acc := acc ++ load
      acc := acc ++ (← storeField p payName 24)
      acc := acc ++ emitReturnU64 24
  else
    match v with
    | .lit k =>
      acc := acc ++ s!"  lddw r1, 0x{IR.u64Hex k}\n  stxdw [r10 - 24], r1\n"
      acc := acc ++ (← emitStoreAndReturn p destHint 24)
    | .field _ fname =>
      if hasChecked then
        acc := acc ++ (← emitStoreAndReturn p destHint 24)
      else if fname.contains '_' && (IR.fieldOffset p fname).isSome then
        let load ← loadVal p (.arg 0) 24 n s!"{label}_{n}_field"
        n := n + 1
        acc := acc ++ load
        acc := acc ++ (← emitStoreAndReturn p fname 24)
      else do
        -- 窄字段赋值：okState 抽出的是未改槽，写回指令参数到 dest。
        let load ← loadVal p (.arg 0) 24 n s!"{label}_{n}_narrow"
        n := n + 1
        acc := acc ++ load
        acc := acc ++ (← emitStoreAndReturn p destHint 24)
    | .ext _ _ => do
      let load ← loadVal p v 24 n s!"{label}_{n}_leaf"
      n := n + 1
      acc := acc ++ load
      acc := acc ++ (← emitStoreAndReturn p destHint 24)
    | v =>
      if hasChecked then
        acc := acc ++ (← emitStoreAndReturn p destHint 24)
      else do
        let load ← loadVal p v 24 n s!"{label}_{n}_value"
        n := n + 1
        acc := acc ++ load
        acc := acc ++ (← emitStoreAndReturn p destHint 24)
  return (acc, n)

private partial def emitOps (p : IR.Program) (label errorLabel : String)
    (ops : Array IR.Op) (fresh : Nat) : Except String (String × Nat) := do
  let mut acc := ""
  let mut n := fresh
  let destHint :=
    match ops.findSome? (fun
      | .checkedAddU64 l _ => some (destField p l)
      | .checkedSubU64 l _ => some (destField p l)
      | .checkedMulU64 l _ => some (destField p l)
      | .checkedDivU64 l _ => some (destField p l)
      | .checkedModU64 l _ => some (destField p l)
      | _ => none) with
    | some d => d
    | none => match p.slots[0]? with | some slot => slot.name | none => "slot0"
  for op in ops do
    match op with
    | .letLocal i value =>
      let some localOff := scalarLocalStackOff p i
        | throw "extract/unsupported: too many scalar locals"
      let load ← loadVal p value 8 n s!"{label}_{n}_local_{i}"
      n := n + 1
      acc := acc ++ load ++
        s!"  ldxdw r1, [r10 - 8]\n  stxdw [r10 - {localOff}], r1\n"
    | .joinLocal i =>
      let some localOff := scalarLocalStackOff p i
        | throw "extract/unsupported: too many scalar locals"
      acc := acc ++ s!"  ; declare join local {i}\n  lddw r1, 0\n  stxdw [r10 - {localOff}], r1\n"
    | .setLocal i value =>
      let some localOff := scalarLocalStackOff p i
        | throw "extract/unsupported: too many scalar locals"
      let load ← loadVal p value 8 n s!"{label}_{n}_join_{i}"
      n := n + 1
      acc := acc ++ load ++
        s!"  ; set join local {i}\n  ldxdw r1, [r10 - 8]\n  stxdw [r10 - {localOff}], r1\n"
    | .checkedAddU64 l r =>
      let arithLabel := s!"{label}_{n}"
      let loadL ← loadVal p l 8 n s!"{label}_{n}_l"
      let loadR ← loadVal p r 16 (n + 1) s!"{label}_{n}_r"
      n := n + 2
      acc := acc ++ loadL ++ loadR ++
        "  ldxdw r1, [r10 - 8]\n  ldxdw r2, [r10 - 16]\n" ++
        emitArithOp errorLabel arithLabel "add" ++
        "  stxdw [r10 - 24], r4\n"
    | .checkedSubU64 l r =>
      let arithLabel := s!"{label}_{n}"
      let loadL ← loadVal p l 8 n s!"{label}_{n}_l"
      let loadR ← loadVal p r 16 (n + 1) s!"{label}_{n}_r"
      n := n + 2
      acc := acc ++ loadL ++ loadR ++
        "  ldxdw r1, [r10 - 8]\n  ldxdw r2, [r10 - 16]\n" ++
        emitArithOp errorLabel arithLabel "sub" ++
        "  stxdw [r10 - 24], r4\n"
    | .checkedMulU64 l r =>
      let arithLabel := s!"{label}_{n}"
      let loadL ← loadVal p l 8 n s!"{label}_{n}_l"
      let loadR ← loadVal p r 16 (n + 1) s!"{label}_{n}_r"
      n := n + 2
      acc := acc ++ loadL ++ loadR ++
        "  ldxdw r1, [r10 - 8]\n  ldxdw r2, [r10 - 16]\n" ++
        emitArithOp errorLabel arithLabel "mul" ++
        "  stxdw [r10 - 24], r4\n"
    | .checkedDivU64 l r =>
      let arithLabel := s!"{label}_{n}"
      let loadL ← loadVal p l 8 n s!"{label}_{n}_l"
      let loadR ← loadVal p r 16 (n + 1) s!"{label}_{n}_r"
      n := n + 2
      acc := acc ++ loadL ++ loadR ++
        "  ldxdw r1, [r10 - 8]\n  ldxdw r2, [r10 - 16]\n" ++
        emitArithOp errorLabel arithLabel "div" ++
        "  stxdw [r10 - 24], r4\n"
    | .checkedModU64 l r =>
      let arithLabel := s!"{label}_{n}"
      let loadL ← loadVal p l 8 n s!"{label}_{n}_l"
      let loadR ← loadVal p r 16 (n + 1) s!"{label}_{n}_r"
      n := n + 2
      acc := acc ++ loadL ++ loadR ++
        "  ldxdw r1, [r10 - 8]\n  ldxdw r2, [r10 - 16]\n" ++
        emitArithOp errorLabel arithLabel "mod" ++
        "  stxdw [r10 - 24], r4\n"
    | .ite cmp l r thn els =>
      let loadL ← loadVal p l 8 n s!"{label}_{n}_l"
      let loadR ← loadVal p r 16 (n + 1) s!"{label}_{n}_r"
      n := n + 2
      let thenLab := s!"then_{label}_{n}"
      let elseLab := s!"else_{label}_{n}"
      -- `label` grows with every nesting level; the method-level error label plus the fresh
      -- counter is already unique and keeps join labels bounded in large decision trees.
      let doneLab := s!"done_{errorLabel}_{n}"
      let thenTerminates := opsTerminate thn
      let doneLabel := if opsTerminate thn then "" else s!"{doneLab}:\n"
      n := n + 1
      let (thenTxt, n1) ← emitOps p thenLab errorLabel thn n
      let (elseTxt, n2) ← emitOps p elseLab errorLabel els n1
      n := n2
      let (falseTarget, thenTxt) :=
        wrapRelayBypass s!"{thenLab}_body" elseLab thenTxt
      let (doneTarget, elseTxt) :=
        if thenTerminates then (doneLab, elseTxt)
        else wrapRelayBypass s!"{elseLab}_body" doneLab elseTxt
      let thenJump := if thenTerminates then "" else s!"  ja {doneTarget}\n"
      acc := acc ++ loadL ++ loadR ++
        "  ldxdw r1, [r10 - 8]\n  ldxdw r2, [r10 - 16]\n" ++
        jmpIf cmp thenLab ++
        s!"  ja {falseTarget}\n{thenLab}:\n{thenTxt}{thenJump}" ++
        s!"{elseLab}:\n{elseTxt}{doneLabel}"
    | .invoke prog metas data seed bump =>
      let invokeLabel := s!"{label}_{n}"
      n := n + 1
      acc := acc ++ (← emitInvoke p invokeLabel prog metas data seed bump)
    | .accDataWordSetAt account baseWord strideWords capacity index value =>
      let writeLabel := s!"{label}_{n}"
      n := n + 1
      acc := acc ++
        (← emitAccDataWordSetAt p writeLabel account baseWord strideWords capacity index value)
    | .accDataRbTreeKey4Insert account rootWord linksBaseWord parentBaseWord keyBaseWord
        strideWords capacity key0 key1 key2 key3 =>
      let insertLabel := s!"{label}_{n}"
      n := n + 1
      acc := acc ++ (← emitAccDataRbTreeKey4Insert p insertLabel account rootWord
        linksBaseWord parentBaseWord keyBaseWord strideWords capacity key0 key1 key2 key3)
    | .errorNamed name =>
      let code :=
        match name with
        | "unauthorized" => "0x1002"
        | "full" => "0x1003"
        | "selfTrade" => "0x1004"
        | _ => "0x1"
      acc := acc ++ s!"  ; named error {name}\n  lddw r0, {code}\n  exit\n"
    | .forAccum bound addend resultLocal =>
      let loopLab := s!"loop_{label}_{n}"
      let doneLab := s!"done_{label}_{n}"
      let some localOff := scalarLocalStackOff p resultLocal
        | throw "extract/unsupported: too many scalar locals"
      n := n + 1
      let loadAdd ← loadVal p addend 16 n s!"{label}_{n}_acc"
      n := n + 1
      acc := acc ++
        s!"\
  ; forAccum {bound}
  lddw r1, 0
  stxdw [r10 - {localOff}], r1
  stxdw [r10 - {loopCounterScratch}], r1
{loopLab}:
  ldxdw r1, [r10 - {loopCounterScratch}]
  lddw r2, {bound}
  jge r1, r2, {doneLab}
{loadAdd}  ldxdw r1, [r10 - {localOff}]
  ldxdw r2, [r10 - 16]
  lddw r3, 0xffffffffffffffff
  sub64 r3, r2
  jgt r1, r3, err_{errorLabel}
  add64 r1, r2
  stxdw [r10 - {localOff}], r1
  ldxdw r1, [r10 - {loopCounterScratch}]
  add64 r1, 1
  stxdw [r10 - {loopCounterScratch}], r1
  ja {loopLab}
  {doneLab}:
  "
    | .forBody bound body =>
      let loopLab := s!"loop_{label}_{n}"
      let doneLab := s!"done_{label}_{n}"
      n := n + 1
      let (bodyTxt, n1) ← emitOps p loopLab errorLabel body n
      n := n1
      let (doneTarget, bodyTxt, loopTarget) :=
        wrapLoopRelays s!"{loopLab}_body" loopLab doneLab bodyTxt
      acc := acc ++
        s!"  ; forBody {bound}
  lddw r1, 0
  stxdw [r10 - {loopCounterScratch}], r1
  {loopLab}:
  ldxdw r1, [r10 - {loopCounterScratch}]
  lddw r2, {bound}
  jge r1, r2, {doneTarget}
  {bodyTxt}  ldxdw r1, [r10 - {loopCounterScratch}]
  add64 r1, 1
  stxdw [r10 - {loopCounterScratch}], r1
  ja {loopTarget}
  {doneLab}:
  "
    | .indexSet name idx value len elemOff =>
      let some baseOff := IR.vectorBaseOffset p name
        | throw s!"extract/unsupported: unknown vector {name}"
      let some width := IR.vectorLeafWidth p name elemOff
        | throw s!"extract/unsupported: unknown vector leaf {name}+{elemOff}"
      let store ← storeInsn width
      let loadI ← loadVal p idx 8 n s!"{label}_{n}_idx"
      let loadV ← loadVal p value 16 (n + 1) s!"{label}_{n}_value"
      n := n + 2
      let bound := IR.vectorLenOf p name len
      let bound := if bound == 0 then 1 else bound
      let stride := IR.vectorStride p name
      let ok := s!"ok_iset_{label}_{n}"
      n := n + 1
      acc := acc ++ loadI ++ loadV ++
        s!"\
  ; indexSet {name}[{bound}]+{elemOff}
  ldxdw r2, [r10 - 8]
  lddw r3, {bound}
  jlt r2, r3, {ok}
  lddw r0, 0x1
  exit
{ok}:
  mul64 r2, {stride}
  mov64 r1, r6
  add64 r1, ACC0_DATA
  add64 r1, {baseOff + elemOff}
  add64 r1, r2
  ldxdw r3, [r10 - 16]
  {store} [r1 + 0], r3
  stxdw [r10 - 24], r3
"
    | .storeField name v =>
      let load ← loadVal p v 24 n s!"{label}_{n}_store"
      n := n + 1
      acc := acc ++ load
      acc := acc ++ (← storeField p name 24)
    | .okState v =>
      let (text, next) ← emitOkState p label v n destHint
        (IR.hasStoreField ops) (IR.hasIndexSet ops) (IR.hasCheckedArith ops)
      acc := acc ++ text
      n := next
    | .errorOverflow =>
      acc := acc ++ emitOverflowReturn
    | .returnU64 v =>
      let load ← loadVal p v 8 n s!"{label}_{n}_return"
      n := n + 1
      acc := acc ++ load ++ emitReturnU64 8
    | .returnState v =>
      let load ← loadVal p v 8 n s!"{label}_{n}_return_state"
      n := n + 1
      let dest := (p.slots[0]?.map (·.name)).getD "slot0"
      acc := acc ++ load ++ (← emitStoreAndReturn p dest 8)
  return (acc, n)

private inductive CFGResultHint where
  | plain
  | checked (destination : String)
  | stored
  | conflict
  deriving BEq, Inhabited

private def mergeCFGHint (old next : CFGResultHint) : CFGResultHint :=
  if old == next then old else .conflict

private def updateCFGHint (hints : Array (Core.CFG.BlockId × CFGResultHint))
    (id : Core.CFG.BlockId) (next : CFGResultHint) :
    Array (Core.CFG.BlockId × CFGResultHint) × Bool :=
  match hints.findIdx? (·.1 == id) with
  | none => (hints.push (id, next), true)
  | some index =>
      let old := hints[index]!.2
      let merged := mergeCFGHint old next
      if merged == old then (hints, false)
      else (hints.set! index (id, merged), true)

private def hintAfterInstructions (instructions : Array Ops.Op)
    (incoming : CFGResultHint) : CFGResultHint :=
  if instructions.any fun
      | .storeField .. | .indexSet .. | .indexSetLeaf .. => true
      | _ => false then
    .stored
  else
    incoming

/-- Track the implicit result cell used by the legacy ABI convention. CFG control flow makes
the convention path-sensitive: a checked result and an explicit store may only flow to an exit
through graph edges, never through the emitter's recursive call stack. Ambiguous joins fail closed. -/
private def cfgResultHints (p : IR.Program)
    (graph : Core.CFG.Graph Ops.ValKind Ops.OpExt) :
    Array (Core.CFG.BlockId × CFGResultHint) := Id.run do
  let mut hints : Array (Core.CFG.BlockId × CFGResultHint) := #[(graph.entry, .plain)]
  let fuel := graph.blocks.size * 4 + 1
  for _ in [0:fuel] do
    let mut changed := false
    for block in graph.blocks do
      match hints.find? (·.1 == block.id) with
      | none => pure ()
      | some entry =>
          let outgoing := hintAfterInstructions block.instructions entry.2
          let mut flows : Array (Core.CFG.Edge Ops.ValKind × CFGResultHint) := #[]
          match block.terminator with
          | .jump next => flows := #[(next, outgoing)]
          | .branch _ _ _ thenEdge elseEdge =>
              flows := #[(thenEdge, outgoing), (elseEdge, outgoing)]
          | .checked operation success overflow =>
              let successHint := match operation with
                | .addU64 lhs _ | .subU64 lhs _ | .mulU64 lhs _
                | .divU64 lhs _ | .modU64 lhs _ => .checked (destField p lhs)
                | .forAccum .. => outgoing
              flows := #[(success, successHint), (overflow, .plain)]
          | .exit _ | .unreachable => pure ()
          for flow in flows do
            let (nextHints, didChange) := updateCFGHint hints flow.1.target flow.2
            hints := nextHints
            changed := changed || didChange
    unless changed do break
  return hints

private structure CFGAsmNode where
  id : Nat
  label : String
  template : String
  successors : Array Nat := #[]
  sizeBound : Nat := 0
  deriving Inhabited

private def cfgEdgeToken (index : Nat) : String := s!"@@CFG_EDGE_{index}@@"

private def cfgNode? (nodes : Array CFGAsmNode) (id : Nat) : Option CFGAsmNode :=
  match nodes[id]? with
  | some node => if node.label.isEmpty then none else some node
  | none => none

private def renderCFGNode (nodes : Array CFGAsmNode) (node : CFGAsmNode) :
    Except String String := do
  let mut text := node.template
  for index in [0:node.successors.size] do
    let targetId := node.successors[index]!
    let some target := cfgNode? nodes targetId
      | throw s!"svm/cfg: node {node.id} targets missing node {targetId}"
    text := text.replace (cfgEdgeToken index) target.label
  return text

/-- Two instructions per source line is conservative for sBPF assembly (`lddw` is the only
two-word instruction emitted here). Labels and comments are deliberately over-counted. -/
private def cfgInstructionBound (text : String) : Nat :=
  2 * (text.splitOn "\n").length + 2

private structure CFGNodePosition where
  id : Nat
  start : Nat
  size : Nat
  deriving Inhabited

private def cfgPositions (nodes : Array CFGAsmNode) (layout : Array Nat) :
    Except String (Array CFGNodePosition) := do
  let mut result := Array.replicate nodes.size ({ id := 0, start := 0, size := 0 } : CFGNodePosition)
  let mut offset := 0
  for id in layout do
    let some node := cfgNode? nodes id
      | throw s!"svm/cfg: layout references missing node {id}"
    result := result.set! id { id, start := offset, size := node.sizeBound }
    offset := offset + node.sizeBound
  return result

/-- Split oversized CFG blocks at source-line boundaries before global relay placement. Each
non-final chunk jumps to the next one, so normal execution is unchanged while relay islands may be
laid out between chunks. `relayChunks` keeps every chunk below the conservative CFG jump span. -/
private def splitLargeCFGNodes (scope : String) (inputNodes : Array CFGAsmNode)
    (layout : Array Nat) (firstFreshId : Nat) :
    Except String (Array CFGAsmNode × Array Nat × Nat) := do
  let mut nodes := inputNodes
  let mut splitLayout : Array Nat := #[]
  let mut nextId := firstFreshId
  for id in layout do
    let some node := cfgNode? nodes id
      | throw s!"svm/cfg: split references missing node {id}"
    -- Keep chunks below half of the global 12,000-instruction relay span. This guarantees that
    -- every midpoint has a usable chunk boundary instead of repeatedly landing inside one chunk.
    let chunks := relayChunks node.template (maxLines := 2048)
    if chunks.size ≤ 1 then
      splitLayout := splitLayout.push id
    else
      let mut ids : Array Nat := #[id]
      for _ in [1:chunks.size] do
        ids := ids.push nextId
        nextId := nextId + 1
      for index in [0:chunks.size] do
        let chunkId := ids[index]!
        let isLast := index + 1 == chunks.size
        let template :=
          if isLast then chunks[index]!
          else chunks[index]! ++ s!"  ja {cfgEdgeToken 0}\n"
        let chunk : CFGAsmNode := {
          id := chunkId
          label := if index == 0 then node.label else s!"cfg_{scope}_chunk_{chunkId}"
          template
          successors := if isLast then node.successors else #[ids[index + 1]!]
          sizeBound := cfgInstructionBound template
        }
        if index == 0 then nodes := nodes.set! id chunk
        else nodes := nodes.push chunk
        splitLayout := splitLayout.push chunkId
  return (nodes, splitLayout, nextId)

private structure CFGFarEdge where
  source : Nat
  successorIndex : Nat
  target : Nat
  midpoint : Nat

private def firstFarCFGEdge (nodes : Array CFGAsmNode)
    (layout : Array Nat) (positions : Array CFGNodePosition) : Option CFGFarEdge := Id.run do
  -- Keep a wide safety margin below sBPF's signed 16-bit instruction displacement.
  let maxSpan := 12000
  for sourceId in layout do
    let source := positions[sourceId]!
    let some node := cfgNode? nodes source.id | continue
    for successorIndex in [0:node.successors.size] do
      let targetId := node.successors[successorIndex]!
      let some target := positions[targetId]? | continue
      -- CFG successor jumps are emitted in the terminator at the end of the source block. Measuring
      -- from `source.start` makes every edge out of a block larger than `maxSpan` permanently far:
      -- inserting a relay cannot shrink the source block itself, so relay insertion exhausts fuel.
      let sourceJump := source.start + source.size
      let low := min sourceJump target.start
      let high := max sourceJump target.start
      if high - low > maxSpan then
        return some {
          source := source.id
          successorIndex
          target := targetId
          midpoint := low + (high - low) / 2
        }
  return none

private partial def insertCFGRelays (scope : String) (nodes : Array CFGAsmNode)
    (layout : Array Nat) (nextId fuel : Nat) : Except String (Array CFGAsmNode × Array Nat) := do
  let positions ← cfgPositions nodes layout
  if fuel == 0 then
    match firstFarCFGEdge nodes layout positions with
    | some edge =>
        let source := positions[edge.source]!
        let target := positions[edge.target]!
        let largest := positions.foldl (init := 0) fun size position => max size position.size
        throw (s!"svm/cfg: long-jump relay layout did not converge: " ++
          s!"source={edge.source}@{source.start}+{source.size}, " ++
          s!"target={edge.target}@{target.start}, midpoint={edge.midpoint}, " ++
          s!"largestBlock={largest}, nodes={nodes.size}")
    | none => return (nodes, layout)
  match firstFarCFGEdge nodes layout positions with
  | none => pure (nodes, layout)
  | some edge =>
      let some source := cfgNode? nodes edge.source
        | throw s!"svm/cfg: missing relay source {edge.source}"
      unless edge.successorIndex < source.successors.size do
        throw s!"svm/cfg: invalid successor {edge.successorIndex} of node {edge.source}"
      let relayTemplate := s!"  ja {cfgEdgeToken 0}\n"
      let relay : CFGAsmNode := {
        id := nextId
        label := s!"cfg_{scope}_relay_{nextId}"
        template := relayTemplate
        successors := #[edge.target]
        sizeBound := cfgInstructionBound relayTemplate
      }
      let redirected := {
        source with successors := source.successors.set! edge.successorIndex nextId
      }
      let nodes := (nodes.set! edge.source redirected).push relay
      let insertion := Id.run do
        for index in [0:layout.size] do
          if positions[layout[index]!]!.start >= edge.midpoint then return index
        return layout.size
      let layout := layout.extract 0 insertion ++ #[nextId] ++ layout.extract insertion layout.size
      insertCFGRelays scope nodes layout (nextId + 1) (fuel - 1)

private def checkedCFGTemplate (p : IR.Program) (scope : String)
    (operation : Core.CFG.Checked Ops.ValKind) : Except String String := do
  match operation with
  | .addU64 lhs rhs | .subU64 lhs rhs | .mulU64 lhs rhs
  | .divU64 lhs rhs | .modU64 lhs rhs =>
      let loadL ← loadVal p lhs 8 0 s!"{scope}_checked_l"
      let loadR ← loadVal p rhs 16 1 s!"{scope}_checked_r"
      let arithmetic := match operation with
        | .addU64 .. =>
            s!"  lddw r3, 0xffffffffffffffff\n  sub64 r3, r2\n" ++
              s!"  jgt r1, r3, {cfgEdgeToken 1}\n  mov64 r4, r1\n  add64 r4, r2\n"
        | .subU64 .. =>
            s!"  jlt r1, r2, {cfgEdgeToken 1}\n  mov64 r4, r1\n  sub64 r4, r2\n"
        | .mulU64 .. =>
            s!"  lddw r3, 0xffffffffffffffff\n  jeq r2, 0, {scope}_mul_ok\n" ++
              s!"  div64 r3, r2\n  jgt r1, r3, {cfgEdgeToken 1}\n" ++
              s!"{scope}_mul_ok:\n  mov64 r4, r1\n  mul64 r4, r2\n"
        | .divU64 .. =>
            s!"  jeq r2, 0, {cfgEdgeToken 1}\n  mov64 r4, r1\n  div64 r4, r2\n"
        | .modU64 .. =>
            s!"  jeq r2, 0, {cfgEdgeToken 1}\n  mov64 r4, r1\n  mod64 r4, r2\n"
        | .forAccum .. => ""
      return loadL ++ loadR ++
        "  ldxdw r1, [r10 - 8]\n  ldxdw r2, [r10 - 16]\n" ++ arithmetic ++
        s!"  stxdw [r10 - 24], r4\n  ja {cfgEdgeToken 0}\n"
  | .forAccum bound addend resultLocal =>
      let some localOff := scalarLocalStackOff p resultLocal
        | throw "extract/unsupported: too many scalar locals"
      let loadAdd ← loadVal p addend 16 0 s!"{scope}_acc"
      return s!"\
  ; CFG forAccum {bound}
  lddw r1, 0
  stxdw [r10 - {localOff}], r1
  stxdw [r10 - {loopCounterScratch}], r1
{scope}_loop:
  ldxdw r1, [r10 - {loopCounterScratch}]
  lddw r2, {bound}
  jge r1, r2, {scope}_done
{loadAdd}  ldxdw r1, [r10 - {localOff}]
  ldxdw r2, [r10 - 16]
  lddw r3, 0xffffffffffffffff
  sub64 r3, r2
  jgt r1, r3, {cfgEdgeToken 1}
  add64 r1, r2
  stxdw [r10 - {localOff}], r1
  ldxdw r1, [r10 - {loopCounterScratch}]
  add64 r1, 1
  stxdw [r10 - {loopCounterScratch}], r1
  ja {scope}_loop
{scope}_done:
  ja {cfgEdgeToken 0}
"

private def emitCFGInitialize (p : IR.Program) (marker scope : String)
    (values : Array Ops.Val) (fresh : Nat) : Except String String := do
  if values.isEmpty then
    throw "extract/unsupported: init missing returnState"
  if !p.schema.isEmpty && values.size != p.slots.size then
    throw (s!"extract/unsupported: init initializes {values.size} state leaves, " ++
      s!"schema requires {p.slots.size}")
  let mut body := ""
  let mut n := fresh
  for i in [0:p.slots.size] do
    let slot := p.slots[i]!
    if h : i < values.size then
      let load ← loadVal p values[i] 8 n s!"{scope}_init_{i}"
      n := n + 1
      body := body ++ load ++ (← storeField p slot.name 8)
    else
      let some offset := IR.fieldOffset p slot.name
        | throw s!"extract/unsupported: unknown field {slot.name}"
      let store ← storeInsn slot.width
      body := body ++ s!"  lddw r1, 0\n  {store} [r6 + ACC0_DATA + {offset}], r1\n"
  return body ++ s!"\
  lddw r1, {marker}
  stxdw [r6 + ACC0_DATA + 0], r1
  lddw r0, 0
  exit
"

private def emitCFGReturnValues (p : IR.Program) (scope : String)
    (values : Array Ops.Val) (fresh : Nat) : Except String String := do
  if values.isEmpty then throw "svm/cfg: empty return tuple"
  let byteCount := values.size * 8
  if byteCount > loopCounterScratch then
    throw "extract/unsupported: return tuple exceeds scalar scratch"
  let mut body := ""
  let mut n := fresh
  for i in [0:values.size] do
    let stackOff := byteCount - i * 8
    body := body ++ (← loadVal p values[i]! stackOff n s!"{scope}_return_{i}")
    n := n + 1
  return body ++ s!"\
  mov64 r1, r10
  add64 r1, -{byteCount}
  lddw r2, {byteCount}
  call sol_set_return_data
  lddw r0, 0
  exit
"

private def makeCFGNode (p : IR.Program) (marker handler : String)
    (hints : Array (Core.CFG.BlockId × CFGResultHint))
    (block : Core.CFG.Block Ops.ValKind Ops.OpExt) : Except String CFGAsmNode := do
  unless block.params.isEmpty do
    throw s!"svm/cfg: block parameters are not lowered in block {block.id}"
  let scope := s!"{handler}_b{block.id}"
  let instructions ← IR.ofSourceOps block.instructions
  let (bodyPrefix, fresh) ← emitOps p scope handler instructions 0
  let incoming := (hints.find? (·.1 == block.id)).map (·.2) |>.getD .plain
  let afterInstructions := hintAfterInstructions block.instructions incoming
  let mut template := bodyPrefix
  let mut successors := #[]
  match block.terminator with
  | .jump next =>
      unless next.args.isEmpty do
        throw s!"svm/cfg: edge arguments remain at block {block.id}"
      template := template ++ s!"  ja {cfgEdgeToken 0}\n"
      successors := #[next.target]
  | .branch cmp lhs rhs thenEdge elseEdge =>
      unless thenEdge.args.isEmpty && elseEdge.args.isEmpty do
        throw s!"svm/cfg: branch arguments remain at block {block.id}"
      let loadL ← loadVal p lhs 8 fresh s!"{scope}_branch_l"
      let loadR ← loadVal p rhs 16 (fresh + 1) s!"{scope}_branch_r"
      let branchComment := match cmp, lhs, rhs with
        | .lt, .local _, .lit bound => s!"  ; CFG loop header bound={bound.toNat}\n"
        | _, _, _ => ""
      template := template ++ branchComment ++ loadL ++ loadR ++
        "  ldxdw r1, [r10 - 8]\n  ldxdw r2, [r10 - 16]\n" ++
        jmpIf cmp (cfgEdgeToken 0) ++ s!"  ja {cfgEdgeToken 1}\n"
      successors := #[thenEdge.target, elseEdge.target]
  | .checked operation success overflow =>
      unless success.args.isEmpty && overflow.args.isEmpty do
        throw s!"svm/cfg: checked arguments remain at block {block.id}"
      template := template ++ (← checkedCFGTemplate p scope operation)
      successors := #[success.target, overflow.target]
  | .exit result =>
      match result with
      | .initialize values =>
          template := template ++ (← emitCFGInitialize p marker scope values fresh)
      | .okState value =>
          let defaultDest := (p.slots[0]?.map (·.name)).getD "slot0"
          let (dest, hasStore, hasChecked) ← match afterInstructions with
            | .plain => pure (defaultDest, false, false)
            | .checked destination => pure (destination, false, true)
            | .stored => pure (defaultDest, true, false)
            | .conflict =>
                if (IR.optionLeafNames? p).isSome then pure (defaultDest, false, false)
                else match value with
                  | .field _ _ => pure (defaultDest, true, false)
                  | _ => throw s!"svm/cfg: ambiguous implicit result at block {block.id}"
          let (exitText, _) ← emitOkState p scope value fresh dest hasStore false hasChecked
          template := template ++ exitText
      | .errorOverflow => template := template ++ emitOverflowReturn
      | .errorNamed name =>
          let code := match name with
            | "unauthorized" => "0x1002"
            | "full" => "0x1003"
            | "selfTrade" => "0x1004"
            | _ => "0x1"
          template := template ++ s!"  ; named error {name}\n  lddw r0, {code}\n  exit\n"
      | .returnU64 value =>
          let (exitText, _) ← emitOps p scope handler #[.returnU64 value] fresh
          template := template ++ exitText
      | .returnU64s values =>
          template := template ++ (← emitCFGReturnValues p scope values fresh)
      | .returnState value =>
          let (exitText, _) ← emitOps p scope handler #[.returnState value] fresh
          template := template ++ exitText
  | .unreachable => throw s!"svm/cfg: reachable block {block.id} is incomplete"
  return {
    id := block.id
    label := s!"cfg_{handler}_block_{block.id}"
    template
    successors
    sizeBound := cfgInstructionBound template
  }

private def emitCFGBody (p : IR.Program) (marker handler : String) (method : IR.Method) :
    Except String String := do
  let graph ← method.toCFG
  let hints := cfgResultHints p graph
  let nextId := graph.blocks.foldl (init := 0) fun next block => max next (block.id + 1)
  let mut nodes := Array.replicate nextId (default : CFGAsmNode)
  for block in graph.blocks do
    nodes := nodes.set! block.id (← makeCFGNode p marker handler hints block)
  let layout := graph.reachable
  let (splitNodes, layout, nextId) ← splitLargeCFGNodes handler nodes layout nextId
  let (finalNodes, layout) ← insertCFGRelays handler splitNodes layout nextId 100000
  let mut body := ""
  for id in layout do
    let some node := cfgNode? finalNodes id
      | throw s!"svm/cfg: missing laid-out node {id}"
    body := body ++ s!"{node.label}:\n" ++ (← renderCFGNode finalNodes node)
  let ix :=
    if IR.usesWalk p then
      s!"  ldxdw r7, [r10 - {headerStack (IR.cpiAccountCount p)}]\n  add64 r7, 8\n"
    else ""
  return s!"body_{handler}:\n{ix}{body}"

private def emitMutBody (p : IR.Program) (label : String) (ops : Array IR.Op) : Except String String := do
  let (body, _) ← emitOps p label label ops 0
  let overflow :=
    if IR.hasCheckedArith ops || Ops.hasForAccum (IR.toSourceOps ops) then
      emitOverflowExit label
    else
      ""
  let ix :=
    if IR.usesWalk p then
      s!"  ldxdw r7, [r10 - {headerStack (IR.cpiAccountCount p)}]\n  add64 r7, 8\n"
    else ""
  return s!"body_{label}:\n{ix}{body}{overflow}"

private def emitGetBody (p : IR.Program) (label : String) (v : Ops.Val) : Except String String := do
  let load ← loadVal p v 8 0 s!"{label}_get"
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

private def initVal (ops : Array IR.Op) : Except String Ops.Val :=
  match ops.findSome? (fun | .returnState v => some v | _ => none) with
  | some v => .ok v
  | none => .error "extract/unsupported: init missing returnState"

private def getVal (ops : Array IR.Op) : Except String Ops.Val :=
  match ops.findSome? (fun | .returnU64 v => some v | _ => none) with
  | some v => .ok v
  | none => .error "extract/unsupported: get missing returnU64"

private def arithArgs (ops : Array IR.Op) : Except String (Ops.Val × Ops.Val × Bool) :=
  match ops.findSome? (fun
    | .checkedAddU64 l r => some (l, r, true)
    | .checkedSubU64 l r => some (l, r, false)
    | _ => none) with
  | some p => .ok p
  | none => .error "extract/unsupported: increment missing checked arith"

private def hasReturnState (ops : Array IR.Op) : Bool :=
  ops.any (fun | .returnState _ => true | _ => false)

private def hasErrorOverflow (ops : Array IR.Op) : Bool :=
  ops.any (fun | .errorOverflow => true | _ => false)

private def hasOkState (ops : Array IR.Op) : Bool :=
  ops.any (fun | .okState _ => true | _ => false)

private def hasReturnU64 (ops : Array IR.Op) : Bool :=
  ops.any (fun | .returnU64 _ => true | _ => false)

private def emitHandler (p : IR.Program) (marker : String) (m : IR.Method) : Except String String := do
  let label := handlerLabel m
  match m.kind with
  | .init =>
    if IR.usesCpi p then
      let body ← emitCFGBody p marker label m
      return s!"{label}:\n{preludeCpi p marker label (ixLenOf m) true m.ops}{body}"
    else if IR.usesWalk p then
      let body ← emitCFGBody p marker label m
      return s!"{label}:\n{preludeWalk p marker label (ixLenOf m) true m.ops}{body}"
    else
      let body ← emitCFGBody p marker label m
      return s!"{label}:\n{prelude p marker label (ixLenOf m) true true true}{body}"
  | .increment =>
    if IR.hasInvoke m.ops then
      let body ← emitCFGBody p marker label m
      return s!"{label}:\n{preludeCpi p marker label (ixLenOf m) false m.ops}{body}"
    else if !(IR.hasCheckedArith m.ops || IR.hasSelect m.ops ||
        m.ops.any (fun | .ite .. => true | .indexSet .. => true | .forAccum .. => true | .forBody .. => true | .storeField .. => true | _ => false)) then
      .error "extract/unsupported: increment missing checked arith"
    else do
      let body ← emitCFGBody p marker label m
      let head :=
        if IR.usesWalk p then preludeWalk p marker label (ixLenOf m) false m.ops
        else prelude p marker label (ixLenOf m) (usesSignerKey m.ops) true false
      return s!"{label}:\n{head}{body}"
  | .get =>
    let body ← emitCFGBody p marker label m
    let head :=
      if IR.usesWalk p then preludeWalk p marker label (ixLenOf m) false m.ops
      else prelude p marker label (ixLenOf m) (usesSignerKey m.ops) false false
    return s!"{label}:\n{head}{body}"

private def emitDispatch (program : IR.Program) : Except String String := do
  if program.methods.isEmpty then
    throw "extract/unsupported: no methods"
  let mut out := "dispatch_begin:\n  ldxdw r1, [r6 + INSTRUCTION_DATA]\n"
  for i in [0:program.methods.size] do
    let m := program.methods[i]!
    let label := handlerLabel m
    let disc ← IR.discHex m
    let next :=
      if i + 1 == program.methods.size then "err_unknown_disc"
      else s!"dispatch_next_{label}"
    -- Conditional and unconditional jumps have a signed 16-bit instruction offset. Large
    -- programs can place handlers beyond that range, while local calls use a 32-bit offset.
    -- Every handler rebuilds its own account-walk frame, so CPI handlers are safe to call too.
    let jump := s!"  call {label}\n  exit\n"
    if i == 0 then
      out := out ++ s!"  lddw r2, {disc}\n  jne r1, r2, {next}\n{jump}"
    else
      out := out ++ s!"dispatch_next_{handlerLabel program.methods[i - 1]!}:\n  lddw r2, {disc}\n  jne r1, r2, {next}\n{jump}"
  return out

private def emitRawSelfHandler (entry : Ops.RawSelfEntry) : String :=
  let (seedBytes, _) :=
    entry.authoritySeed.toList.foldl (init := ("", 0)) fun (out, offset) byte =>
      (out ++ s!"  lddw r1, {byte.toNat}\n  stxb [r8 + {offset}], r1\n", offset + 1)
  s!"\
raw_self_entry:
  ; signed raw self-entry tag={entry.tag.toNat} seed={entry.authoritySeed}
{emitWalkAccounts 1 "raw_self" "err_unknown_disc"}  ldxdw r7, [r10 - {headerStack 1}]
  ldxdw r1, [r7 + 0]
  jlt r1, 1, err_unknown_disc
  add64 r7, 8
  ldxb r1, [r7 + 0]
  jne r1, {entry.tag.toNat}, err_unknown_disc
  ldxdw r2, [r10 - {headerStack 0}]
  ldxb r1, [r2 + 1]
  jeq r1, 0, err_unknown_disc
  ldxb r1, [r2 + 2]
  jne r1, 0, err_unknown_disc
  mov64 r8, r10
  add64 r8, -2800
{seedBytes}  mov64 r1, r8
  stxdw [r8 + 64], r1
  lddw r1, {entry.authoritySeed.length}
  stxdw [r8 + 72], r1
  ldxdw r3, [r10 - {headerStack 1}]
  ldxdw r1, [r3 + 0]
  add64 r3, 8
  add64 r3, r1
  mov64 r1, r8
  add64 r1, 64
  lddw r2, 1
  mov64 r4, r8
  add64 r4, 96
  mov64 r5, r8
  add64 r5, 128
  call sol_try_find_program_address
  jne r0, 0, err_unknown_disc
  ldxdw r2, [r10 - {headerStack 0}]
  add64 r2, 8
  ldxdw r1, [r8 + 96]
  ldxdw r3, [r2 + 0]
  jne r1, r3, err_unknown_disc
  ldxdw r1, [r8 + 104]
  ldxdw r3, [r2 + 8]
  jne r1, r3, err_unknown_disc
  ldxdw r1, [r8 + 112]
  ldxdw r3, [r2 + 16]
  jne r1, r3, err_unknown_disc
  ldxdw r1, [r8 + 120]
  ldxdw r3, [r2 + 24]
  jne r1, r3, err_unknown_disc
  ; Publish the authenticated raw payload as one sol_log_data field.
  stxdw [r8 + 160], r7
  ldxdw r1, [r10 - {headerStack 1}]
  ldxdw r1, [r1 + 0]
  stxdw [r8 + 168], r1
  mov64 r1, r8
  add64 r1, 160
  lddw r2, 1
  call sol_log_data
  lddw r0, 0
  exit
"

/-- Emit assembly from the fully lowered, target-owned SVM IR. -/
def emitAsm (program : IR.Program) : Except String String := do
  unless IR.isProgramShape program do
    throw "extract/unsupported: not program shape"
  let rawSelfEntry ← IR.rawSelfEntry? program
  let marker ← IR.layoutMarkerHex program
  let layout := IR.inputLayout program
  let dispatch ← emitDispatch program
  let mut handlers := ""
  for m in program.methods do
    handlers := handlers ++ (← emitHandler program marker m) ++ "\n"
  let entryIx :=
    if IR.usesWalk program then
      let n := IR.cpiAccountCount program
      emitWalkAccounts n "entry" "err_unknown_disc" ++
        s!"  ldxdw r1, [r10 - {headerStack n}]\n  ldxdw r1, [r1 + 0]\n  jlt r1, 8, err_unknown_disc\n  ja dispatch_begin\n"
    else
      s!"\
  ldxb r1, [r6 + ACC0_HEADER + 0]
  jne r1, 0xff, err_unknown_disc
  ldxdw r1, [r6 + INSTRUCTION_DATA_LEN]
  jlt r1, 8, err_unknown_disc
  ja dispatch_begin
"
  let dispatchHead :=
    if IR.usesWalk program then
      s!"dispatch_begin:\n  ldxdw r1, [r10 - {headerStack (IR.cpiAccountCount program)}]\n  add64 r1, 8\n  ldxdw r1, [r1 + 0]\n"
    else
      "dispatch_begin:\n  ldxdw r1, [r6 + INSTRUCTION_DATA]\n"
  -- emitDispatch 自己写了 dispatch_begin 头；transfer 要换掉。
  let dispatchTxt :=
    if IR.usesWalk program then
      dispatch.replace "dispatch_begin:\n  ldxdw r1, [r6 + INSTRUCTION_DATA]\n" dispatchHead
    else dispatch
  let rawJump := if rawSelfEntry.isSome then "  jeq r1, 1, raw_self_entry\n" else ""
  let rawHandler := rawSelfEntry.map emitRawSelfHandler |>.getD ""
  return s!"\
; SOLANA-LEAN-SBPF-ASM v0 (CFG-driven handler bodies)
; digest={IR.digestHex program}
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
{rawJump}{entryIx}{rawHandler}err_unknown_disc:
  lddw r0, 1
  exit
{dispatchTxt}
{handlers}{natSubHelper}"

/-- Native SVM entry point from the combined extractor dialect. -/
def emitProgramAsm (program : Extract.IR.Program) : Except String String := do
  emitAsm (← IR.fromExtracted program)

end ProofForge.Svm.Emit
