import SolanaLean.IR
import SolanaLean.Ops

namespace SolanaLean.Emit

def overflowCode : String := "0x1001"

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

/-- 账户 i 的 header* 存在 `[r10 - (48 + 8*i)]`。ix 长度指针在最后一个 header 之后。 -/
private def headerStack (i : Nat) : Nat :=
  48 + 8 * i

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

private def walkInvokeMetas (fuel : Nat) (ops : Array Ops.Op) (acc : Array Ops.CpiMeta) :
    Array Ops.CpiMeta :=
  match fuel with
  | 0 => acc
  | fuel' + 1 =>
    ops.foldl (init := acc) fun a op =>
      match op with
      | .invoke _ metas _ => a ++ metas
      | .ite _ _ _ t f => walkInvokeMetas fuel' f (walkInvokeMetas fuel' t a)
      | _ => a

/-- acc0 必须 signer+writable；其余 meta 按编译期旗检查。 -/
private def emitCpiFlagChecks (p : IR.Program) (err : String) : String :=
  let metas := p.methods.foldl (init := #[]) fun a m => walkInvokeMetas 8 m.ops a
  let extra := Id.run do
    let mut seen : Array Nat := #[0]
    let mut out := ""
    for m in metas do
      unless seen.any (· == m.acc) do
        seen := seen.push m.acc
        if m.writable then
          out := out ++
            s!"  ldxdw r8, [r10 - {headerStack m.acc}]\n  ldxb r1, [r8 + 2]\n  jeq r1, 0, {err}\n"
        if m.signer then
          out := out ++
            s!"  ldxdw r8, [r10 - {headerStack m.acc}]\n  ldxb r1, [r8 + 1]\n  jeq r1, 0, {err}\n"
    return out
  s!"\
  ldxdw r8, [r10 - {headerStack 0}]
  ldxb r1, [r8 + 1]
  jeq r1, 0, {err}
  ldxb r1, [r8 + 2]
  jeq r1, 0, {err}
{extra}"

/-- CPI 预检：N 账户虚地址 walk；acc0 signer+writable；其余按 meta 旗。 -/
private def preludeCpi (p : IR.Program) (label : String) (ixLen : Nat) : String :=
  let err := s!"err_check_{label}"
  let n := IR.cpiAccountCount p
  s!"\
  ldxdw r1, [r6 + NUM_ACCOUNTS]
  jlt r1, {n}, {err}
{emitWalkAccounts n label err}  ldxdw r1, [r10 - {headerStack n}]
  ldxdw r1, [r1 + 0]
  jne r1, {ixLen}, {err}
{emitCpiFlagChecks p err}  ja body_{label}
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
    if IR.usesCpi p then
      .ok s!"[r7 + {8 + 8 * i}]"
    else
      .ok s!"[r6 + INSTRUCTION_DATA + {8 + 8 * i}]"
  | .lit _ | .clockSlot | .signerKey0 | .accLamports0 | .accOwner0 | .accDataLen0
  | .accN | .isSigner0 | .isWritable0 | .isExecutable0 | .findPda _ =>
    .error "extract/unsupported: runtime leaf has no mem"

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

/-- Clock 是 40 字节 `repr(C)`；`slot` 在偏移 0。缓冲放在 `r10-72`，避开算术临时槽。 -/
private def emitLoadClockSlot (stackOff : Nat) : String :=
  s!"\
  ; load clock.slot via sol_get_clock_sysvar
  mov64 r1, r10
  add64 r1, -72
  call sol_get_clock_sysvar
  jeq r0, 0, clock_ok_{stackOff}
  lddw r0, 0x1
  exit
clock_ok_{stackOff}:
  ldxdw r1, [r10 - 72]
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

/--
`sol_try_find_program_address`：一条 ASCII 种子 + 当前 program id。
scratch 用 `r8` 基址 `r10-2800`，避开 invoke 的 `r9=r10-2048` 和 clock 的 `r10-72`。
CPI 程序的 program id 在 walk 出的 ix 长度字之后。
-/
private def emitLoadFindPda (p : IR.Program) (seed : String) (stackOff : Nat) : String :=
  let (bytes, _) :=
    seed.toList.foldl (init := ("", 0)) fun (acc, i) c =>
      (acc ++ s!"  lddw r1, {c.toNat}\n  stxb [r8 + {i}], r1\n", i + 1)
  let progId :=
    if IR.usesCpi p then
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
  jeq r0, 0, pda_ok_{stackOff}
  lddw r0, 0x1
  exit
pda_ok_{stackOff}:
  ldxb r1, [r8 + 80]
  jeq r1, 0, pda_bad_{stackOff}
  stxdw [r10 - {stackOff}], r1
  ja pda_done_{stackOff}
pda_bad_{stackOff}:
  lddw r0, 0x1
  exit
pda_done_{stackOff}:
"

private def loadVal (p : IR.Program) (v : Ops.Val) (stackOff : Nat) : Except String String :=
  match v with
  | .lit n =>
    .ok s!"  ; load lit {n}\n  lddw r1, 0x{IR.u64Hex n}\n  stxdw [r10 - {stackOff}], r1\n"
  | .clockSlot =>
    .ok (emitLoadClockSlot stackOff)
  | .signerKey0 =>
    .ok (emitLoadSignerKey0 stackOff)
  | .accLamports0 =>
    .ok (emitLoadAccU64 "load account-0 lamports" "ACC0_LAMPORTS" stackOff)
  | .accOwner0 =>
    .ok (emitLoadAccU64 "load account-0 owner first u64" "ACC0_OWNER + 0" stackOff)
  | .accDataLen0 =>
    .ok (emitLoadAccU64 "load account-0 data_len" "ACC0_DATA_LEN" stackOff)
  | .accN =>
    .ok (emitLoadAccU64 "load NUM_ACCOUNTS" "NUM_ACCOUNTS" stackOff)
  | .isSigner0 =>
    .ok (emitLoadAccU8 "load account-0 is_signer" "ACC0_HEADER + 1" stackOff)
  | .isWritable0 =>
    .ok (emitLoadAccU8 "load account-0 is_writable" "ACC0_HEADER + 2" stackOff)
  | .isExecutable0 =>
    .ok (emitLoadAccU8 "load account-0 is_executable" "ACC0_HEADER + 3" stackOff)
  | .findPda seed =>
    .ok (emitLoadFindPda p seed stackOff)
  | _ => do
    let mem ← memOfVal p v
    let insn ← loadInsn (widthOfVal p v)
    return s!"  ; load {repr v}\n  {insn} r1, {mem}\n  stxdw [r10 - {stackOff}], r1\n"

private def storeField (p : IR.Program) (name : String) (fromStack : Nat) : Except String String :=
  match IR.fieldOffset p name, IR.fieldWidth p name with
  | none, _ => .error s!"extract/unsupported: unknown field {name}"
  | _, none => .error s!"extract/unsupported: unknown field {name}"
  | some off, some w => do
    let insn ← storeInsn w
    .ok s!"  ldxdw r1, [r10 - {fromStack}]\n  {insn} [r6 + ACC0_DATA + {off}], r1\n"

private def emitInitBody (p : IR.Program) (marker : String) (label : String) (ops : Array Ops.Op) :
    Except String String := do
  let vs := ops.filterMap (fun | .returnState v => some v | _ => none)
  if vs.isEmpty then
    .error "extract/unsupported: init missing returnState"
  else do
    let mut body := ""
    let mut i : Nat := 0
    for s in p.slots do
      if h : i < vs.size then
        let load ← loadVal p vs[i] 8
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

private def destField (p : IR.Program) (lhs : Ops.Val) : String :=
  match lhs with
  | .field _ n => n
  | _ => (p.slots[0]?.map (·.name)).getD "slot0"

private def valUsesSigner (v : Ops.Val) : Bool :=
  match v with
  | .signerKey0 => true
  | .field b _ => valUsesSigner b
  | _ => false

private def walkUsesSigner (fuel : Nat) (ops : Array Ops.Op) : Bool :=
  match fuel with
  | 0 => false
  | fuel' + 1 =>
    ops.any fun
      | .checkedAddU64 l r => valUsesSigner l || valUsesSigner r
      | .checkedSubU64 l r => valUsesSigner l || valUsesSigner r
      | .checkedMulU64 l r => valUsesSigner l || valUsesSigner r
      | .checkedDivU64 l r => valUsesSigner l || valUsesSigner r
      | .checkedModU64 l r => valUsesSigner l || valUsesSigner r
      | .ite _ l r t f =>
          valUsesSigner l || valUsesSigner r ||
            walkUsesSigner fuel' t || walkUsesSigner fuel' f
      | .invoke _ metas data _ bump =>
          metas.any (·.signer) ||
            data.any (fun | .u64le v => valUsesSigner v | _ => false) ||
              (match bump with | some v => valUsesSigner v | none => false)
      | .okState v => valUsesSigner v
      | .returnU64 v => valUsesSigner v
      | .returnState v => valUsesSigner v
      | .errorOverflow => false

private def usesSignerKey (ops : Array Ops.Op) : Bool :=
  walkUsesSigner 16 ops

private def emitOverflowExit (label : String) : String :=
  s!"err_{label}:\n  lddw r0, {overflowCode}\n  exit\n"

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

private def emitCpiData (p : IR.Program) (base : Nat) (data : Array Ops.CpiWord) :
    Except String (String × Nat) := do
  -- CreateAccount 是 52B：u32+u64 不对齐。先清 64B，避免残留污染 space。
  let mut body :=
    s!"  lddw r1, 0\n  stxdw [r9 + {base}], r1\n  stxdw [r9 + {base + 8}], r1\n" ++
    s!"  stxdw [r9 + {base + 16}], r1\n  stxdw [r9 + {base + 24}], r1\n" ++
    s!"  stxdw [r9 + {base + 32}], r1\n  stxdw [r9 + {base + 40}], r1\n" ++
    s!"  stxdw [r9 + {base + 48}], r1\n  stxdw [r9 + {base + 56}], r1\n"
  let mut off : Nat := 0
  for w in data do
    match w with
    | .u8le n =>
      body := body ++ s!"  lddw r1, {n.toNat}\n  stxb [r9 + {base + off}], r1\n"
      off := off + 1
    | .u32le n =>
      body := body ++ s!"  lddw r1, {n.toNat}\n  stxw [r9 + {base + off}], r1\n"
      off := off + 4
    | .u64le v =>
      let load ← loadVal p v 8
      body := body ++ load ++ s!"  ldxdw r1, [r10 - 8]\n  stxdw [r9 + {base + off}], r1\n"
      off := off + 8
    | .ascii s =>
      -- 逐字节；本切片字面量很短。
      let mut i : Nat := 0
      for c in s.toList do
        body := body ++ s!"  lddw r1, {c.toNat}\n  stxb [r9 + {base + off + i}], r1\n"
        i := i + 1
      off := off + s.length
    | .programId =>
      let copy :=
        if IR.usesCpi p then
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
  return (body, off)

/-- `r5` 已是 metas 基址（`r9 + metaOff`）；第 i 条相对偏移是 `16*i`，不要再加 16。 -/
private def emitOneMeta (i : Nat) (m : Ops.CpiMeta) : String :=
  let base := 16 * i
  let w := if m.writable then 1 else 0
  let s := if m.signer then 1 else 0
  s!"\
  ldxdw r8, [r10 - {headerStack m.acc}]
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

private def emitSignerSeeds (p : IR.Program) (seedOff : Nat)
    (seed : Option String) (bump : Option Ops.Val) : Except String (String × String) :=
  match seed, bump with
  | some s, some b => do
    let load ← loadVal p b 8
    let (bytes, _) :=
      s.toList.foldl (init := ("", (0 : Nat))) fun (acc, i) c =>
        (acc ++ s!"  lddw r1, {c.toNat}\n  stxb [r9 + {seedOff + i}], r1\n", i + 1)
    let seedPtr := seedOff
    let bumpByte := seedOff + ((s.length + 7) / 8) * 8 + 8
    let seedsArr := bumpByte + 8
    let groupOff := seedsArr + 32
    let txt :=
      load ++ bytes ++ s!"\
  ldxdw r1, [r10 - 8]
  stxb [r9 + {bumpByte}], r1
  mov64 r1, r9
  add64 r1, {seedPtr}
  stxdw [r9 + {seedsArr}], r1
  lddw r1, {s.length}
  stxdw [r9 + {seedsArr + 8}], r1
  mov64 r1, r9
  add64 r1, {bumpByte}
  stxdw [r9 + {seedsArr + 16}], r1
  lddw r1, 1
  stxdw [r9 + {seedsArr + 24}], r1
  mov64 r1, r9
  add64 r1, {seedsArr}
  stxdw [r9 + {groupOff}], r1
  lddw r1, 2
  stxdw [r9 + {groupOff + 8}], r1
"
    let regs :=
      s!"  mov64 r4, r9\n  add64 r4, {groupOff}\n  lddw r5, 1\n"
    return (txt, regs)
  | none, none =>
    return ("", "  lddw r4, 0\n  lddw r5, 0\n")
  | _, _ =>
    .error "extract/unsupported: invoke seeds must be seed+bump or empty"

private def emitInvoke (p : IR.Program) (label : String)
    (programIx : Nat) (metas : Array Ops.CpiMeta) (data : Array Ops.CpiWord)
    (seed : Option String) (bump : Option Ops.Val) :
    Except String String := do
  let n := IR.cpiAccountCount p
  let metaOff := 0
  let ixOff := metaOff + 16 * metas.size
  let dataOff := ixOff + 40
  let (dataTxt, dataLen) ← emitCpiData p dataOff data
  let infoOff := dataOff + ((dataLen + 7) / 8) * 8
  let seedOff := infoOff + 56 * n
  let (seedTxt, seedRegs) ← emitSignerSeeds p seedOff seed bump
  let mut metasTxt := ""
  for i in [0:metas.size] do
    metasTxt := metasTxt ++ emitOneMeta i metas[i]!
  let mut infos := ""
  for i in [0:n] do
    infos := infos ++ emitFillAccountInfoFromHeader label (headerStack i)
    if i + 1 < n then
      infos := infos ++ "  add64 r5, 56\n"
  return s!"\
  ; invoke programIx={programIx} metas={metas.size} dataLen={dataLen}
  mov64 r9, r10
  add64 r9, -2048
{dataTxt}  mov64 r5, r9
  add64 r5, {metaOff}
{metasTxt}  mov64 r8, r9
  add64 r8, {ixOff}
  ldxdw r1, [r10 - {headerStack programIx}]
  add64 r1, 8
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

private def emitArithOp (label : String) (kind : String) : String :=
  match kind with
  | "add" =>
      s!"  lddw r3, 0xffffffffffffffff\n  sub64 r3, r2\n  jgt r1, r3, err_{label}\n  mov64 r4, r1\n  add64 r4, r2\n"
  | "sub" =>
      s!"  jlt r1, r2, err_{label}\n  mov64 r4, r1\n  sub64 r4, r2\n"
  | "mul" =>
      s!"  lddw r3, 0xffffffffffffffff\n  jeq r2, 0, mul_ok_{label}\n  div64 r3, r2\n  jgt r1, r3, err_{label}\nmul_ok_{label}:\n  mov64 r4, r1\n  mul64 r4, r2\n"
  | "div" =>
      s!"  jeq r2, 0, err_{label}\n  mov64 r4, r1\n  div64 r4, r2\n"
  | "mod" =>
      s!"  jeq r2, 0, err_{label}\n  mov64 r4, r1\n  mod64 r4, r2\n"
  | _ => ""

private partial def emitOps (p : IR.Program) (label : String) (ops : Array Ops.Op) (fresh : Nat) :
    Except String (String × Nat) := do
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
    | none => (p.slots[0]?.map (·.name)).getD "slot0"
  for op in ops do
    match op with
    | .checkedAddU64 l r =>
      let loadL ← loadVal p l 8
      let loadR ← loadVal p r 16
      acc := acc ++ loadL ++ loadR ++
        "  ldxdw r1, [r10 - 8]\n  ldxdw r2, [r10 - 16]\n" ++
        emitArithOp label "add" ++
        "  stxdw [r10 - 24], r4\n"
    | .checkedSubU64 l r =>
      let loadL ← loadVal p l 8
      let loadR ← loadVal p r 16
      acc := acc ++ loadL ++ loadR ++
        "  ldxdw r1, [r10 - 8]\n  ldxdw r2, [r10 - 16]\n" ++
        emitArithOp label "sub" ++
        "  stxdw [r10 - 24], r4\n"
    | .checkedMulU64 l r =>
      let loadL ← loadVal p l 8
      let loadR ← loadVal p r 16
      acc := acc ++ loadL ++ loadR ++
        "  ldxdw r1, [r10 - 8]\n  ldxdw r2, [r10 - 16]\n" ++
        emitArithOp label "mul" ++
        "  stxdw [r10 - 24], r4\n"
    | .checkedDivU64 l r =>
      let loadL ← loadVal p l 8
      let loadR ← loadVal p r 16
      acc := acc ++ loadL ++ loadR ++
        "  ldxdw r1, [r10 - 8]\n  ldxdw r2, [r10 - 16]\n" ++
        emitArithOp label "div" ++
        "  stxdw [r10 - 24], r4\n"
    | .checkedModU64 l r =>
      let loadL ← loadVal p l 8
      let loadR ← loadVal p r 16
      acc := acc ++ loadL ++ loadR ++
        "  ldxdw r1, [r10 - 8]\n  ldxdw r2, [r10 - 16]\n" ++
        emitArithOp label "mod" ++
        "  stxdw [r10 - 24], r4\n"
    | .ite cmp l r thn els =>
      let loadL ← loadVal p l 8
      let loadR ← loadVal p r 16
      let thenLab := s!"then_{label}_{n}"
      let elseLab := s!"else_{label}_{n}"
      n := n + 1
      let (thenTxt, n1) ← emitOps p thenLab thn n
      let (elseTxt, n2) ← emitOps p elseLab els n1
      n := n2
      acc := acc ++ loadL ++ loadR ++
        "  ldxdw r1, [r10 - 8]\n  ldxdw r2, [r10 - 16]\n" ++
        jmpIf cmp thenLab ++
        s!"  ja {elseLab}\n{thenLab}:\n{thenTxt}{elseLab}:\n{elseTxt}"
    | .invoke prog metas data seed bump =>
      acc := acc ++ (← emitInvoke p label prog metas data seed bump)
    | .okState v =>
      let hasOpt := p.slots.any (fun s => s.name.endsWith "_tag")
      if hasOpt then
        let tagName :=
          match p.slots.find? (fun s => s.name.endsWith "_tag") with
          | some s => s.name
          | none => destHint
        let payName :=
          match p.slots.find? (fun s => s.name.endsWith "_p0") with
          | some s => s.name
          | none => destHint
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
          let load ← loadVal p v 24
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
          if Ops.hasCheckedArith ops then
            acc := acc ++ (← emitStoreAndReturn p destHint 24)
          else if fname.contains '_' && (IR.fieldOffset p fname).isSome then
            let load ← loadVal p (.arg 0) 24
            acc := acc ++ load
            acc := acc ++ (← emitStoreAndReturn p fname 24)
          else do
            -- 窄字段赋值：okState 抽出的是未改槽，写回指令参数到 dest。
            let load ← loadVal p (.arg 0) 24
            acc := acc ++ load
            acc := acc ++ (← emitStoreAndReturn p destHint 24)
        | .clockSlot | .signerKey0 | .accLamports0 | .accOwner0 | .accDataLen0
        | .accN | .isSigner0 | .isWritable0 | .isExecutable0 | .findPda _ => do
          let load ← loadVal p v 24
          acc := acc ++ load
          acc := acc ++ (← emitStoreAndReturn p destHint 24)
        | _ =>
          if Ops.hasCheckedArith ops then
            acc := acc ++ (← emitStoreAndReturn p destHint 24)
          else do
            let load ← loadVal p v 24
            acc := acc ++ load
            acc := acc ++ (← emitStoreAndReturn p destHint 24)
    | .errorOverflow =>
      acc := acc ++ emitOverflowExit label
    | .returnU64 v =>
      let load ← loadVal p v 8
      acc := acc ++ load ++ emitReturnU64 8
    | .returnState v =>
      let load ← loadVal p v 8
      let dest := (p.slots[0]?.map (·.name)).getD "slot0"
      acc := acc ++ load ++ (← emitStoreAndReturn p dest 8)
  return (acc, n)

private def emitMutBody (p : IR.Program) (label : String) (ops : Array Ops.Op) : Except String String := do
  let (body, _) ← emitOps p label ops 0
  let ix :=
    if IR.usesCpi p then
      s!"  ldxdw r7, [r10 - {headerStack (IR.cpiAccountCount p)}]\n  add64 r7, 8\n"
    else ""
  return s!"body_{label}:\n{ix}{body}"

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
    if IR.usesCpi p then
      return s!"{label}:\n{preludeCpi p label (ixLenOf m)}body_{label}:\n  lddw r0, 0\n  exit\n"
    else
      let body ← emitInitBody p marker label m.ops
      return s!"{label}:\n{prelude p marker label (ixLenOf m) true true true}{body}"
  | .increment =>
    if Ops.hasInvoke m.ops then
      let body ← emitMutBody p label m.ops
      return s!"{label}:\n{preludeCpi p label (ixLenOf m)}{body}"
    else if !(Ops.hasCheckedArith m.ops || m.ops.any (fun | .ite .. => true | _ => false)) then
      .error "extract/unsupported: increment missing checked arith"
    else do
      let body ← emitMutBody p label m.ops
      return s!"{label}:\n{prelude p marker label (ixLenOf m) (usesSignerKey m.ops) true false}{body}"
  | .get =>
    if m.ops.any (fun | .ite .. => true | _ => false) then
      let body ← emitMutBody p label m.ops
      return s!"{label}:\n{prelude p marker label (ixLenOf m) (usesSignerKey m.ops) false false}{body}"
    else
      let v ← getVal m.ops
      let body ← emitGetBody p label v
      return s!"{label}:\n{prelude p marker label (ixLenOf m) (usesSignerKey m.ops) false false}{body}"

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
    let jump := if IR.usesCpi program then s!"  ja {label}\n" else s!"  call {label}\n  exit\n"
    if i == 0 then
      out := out ++ s!"  lddw r2, {disc}\n  jne r1, r2, {next}\n{jump}"
    else
      out := out ++ s!"dispatch_next_{handlerLabel program.methods[i - 1]!}:\n  lddw r2, {disc}\n  jne r1, r2, {next}\n{jump}"
  return out

def emitCounterAsm (program : IR.Program) : Except String String := do
  unless IR.isProgramShape program do
    throw "extract/unsupported: not program shape"
  let marker ← IR.layoutMarkerHex program
  let layout := IR.inputLayout program
  let dispatch ← emitDispatch program
  let mut handlers := ""
  for m in program.methods do
    handlers := handlers ++ (← emitHandler program marker m) ++ "\n"
  let entryIx :=
    if IR.usesCpi program then
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
    if IR.usesCpi program then
      s!"dispatch_begin:\n  ldxdw r1, [r10 - {headerStack (IR.cpiAccountCount program)}]\n  add64 r1, 8\n  ldxdw r1, [r1 + 0]\n"
    else
      "dispatch_begin:\n  ldxdw r1, [r6 + INSTRUCTION_DATA]\n"
  -- emitDispatch 自己写了 dispatch_begin 头；transfer 要换掉。
  let dispatchTxt :=
    if IR.usesCpi program then
      dispatch.replace "dispatch_begin:\n  ldxdw r1, [r6 + INSTRUCTION_DATA]\n" dispatchHead
    else dispatch
  return s!"\
; SOLANA-LEAN-SBPF-ASM v0 (ops-driven handler bodies)
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
{entryIx}err_unknown_disc:
  lddw r0, 1
  exit
{dispatchTxt}
{handlers}"

end SolanaLean.Emit
