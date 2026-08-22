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

private def emitWalkThreeAccounts (tag err : String) : String :=
  s!"\
  mov64 r8, r6
  add64 r8, 8
  ldxb r1, [r8 + 0]
  jne r1, 0xff, {err}
  stxdw [r10 - 48], r8
  ldxdw r4, [r8 + 80]
{emitSkipAccount s!"0_{tag}"}  ldxb r1, [r8 + 0]
  jne r1, 0xff, {err}
  stxdw [r10 - 56], r8
  ldxdw r4, [r8 + 80]
{emitSkipAccount s!"1_{tag}"}  ldxb r1, [r8 + 0]
  jne r1, 0xff, {err}
  stxdw [r10 - 64], r8
  ldxdw r4, [r8 + 80]
{emitSkipAccount s!"2_{tag}"}  stxdw [r10 - 72], r8
"

/-- 封闭 transfer：三账户、零数据。payer 必须 signer+writable。 -/
private def preludeTransfer (label : String) (ixLen : Nat) : String :=
  let err := s!"err_check_{label}"
  s!"\
  ldxdw r1, [r6 + NUM_ACCOUNTS]
  jlt r1, 3, {err}
{emitWalkThreeAccounts label err}  ldxdw r1, [r10 - 72]
  ldxdw r1, [r1 + 0]
  jne r1, {ixLen}, {err}
  ldxdw r8, [r10 - 48]
  ldxb r1, [r8 + 1]
  jeq r1, 0, {err}
  ldxb r1, [r8 + 2]
  jeq r1, 0, {err}
  ldxdw r8, [r10 - 56]
  ldxb r1, [r8 + 2]
  jeq r1, 0, {err}
  ja body_{label}
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
    if IR.usesSystemTransfer p then
      .ok s!"[r7 + {8 + 8 * i}]"
    else
      .ok s!"[r6 + INSTRUCTION_DATA + {8 + 8 * i}]"
  | .lit _ | .clockSlot | .signerKey0 | .evmCaller | .evmBlockNumber =>
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

private def loadVal (p : IR.Program) (v : Ops.Val) (stackOff : Nat) : Except String String :=
  match v with
  | .lit n =>
    .ok s!"  ; load lit {n}\n  lddw r1, 0x{IR.u64Hex n}\n  stxdw [r10 - {stackOff}], r1\n"
  | .clockSlot =>
    .ok (emitLoadClockSlot stackOff)
  | .signerKey0 =>
    .ok (emitLoadSignerKey0 stackOff)
  | .evmCaller | .evmBlockNumber =>
    .error "extract/unsupported: svm rejects evm leaf"
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
      | .systemTransfer v => valUsesSigner v
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
private def emitFillAccountInfoFromHeader (srcStack : Nat) : String :=
  s!"\
  ldxdw r8, [r10 - {srcStack}]
  mov64 r1, r8
  add64 r1, 8
  stxdw [r5 + 0], r1
  mov64 r1, r8
  add64 r1, 72
  stxdw [r5 + 8], r1
  ldxdw r1, [r8 + 80]
  stxdw [r5 + 16], r1
  mov64 r1, r8
  add64 r1, 88
  stxdw [r5 + 24], r1
  mov64 r1, r8
  add64 r1, 40
  stxdw [r5 + 32], r1
  mov64 r1, r8
  add64 r1, 88
  ldxdw r4, [r8 + 80]
  add64 r1, r4
  add64 r1, MAX_PERMITTED_DATA_INCREASE
  mov64 r2, r4
  and64 r2, 7
  jeq r2, 0, fill_rent_{srcStack}
  lddw r3, 8
  sub64 r3, r2
  add64 r1, r3
fill_rent_{srcStack}:
  ldxdw r1, [r1 + 0]
  stxdw [r5 + 40], r1
  ldxb r1, [r8 + 1]
  stxb [r5 + 48], r1
  ldxb r1, [r8 + 2]
  stxb [r5 + 49], r1
  ldxb r1, [r8 + 3]
  stxb [r5 + 50], r1
  lddw r1, 0
  stxb [r5 + 51], r1
  stxb [r5 + 52], r1
  stxb [r5 + 53], r1
  stxb [r5 + 54], r1
  stxb [r5 + 55], r1
"

private def emitSystemTransfer (p : IR.Program) (label : String) (amount : Ops.Val) :
    Except String String := do
  let load ← loadVal p amount 8
  return load ++ s!"\
  ; closed system.transfer via sol_invoke_signed_c
  mov64 r9, r10
  add64 r9, -400
  lddw r1, 0
  stxdw [r9 + 0], r1
  stxdw [r9 + 8], r1
  lddw r1, 2
  stxw [r9 + 0], r1
  ldxdw r1, [r10 - 8]
  stxdw [r9 + 4], r1
  mov64 r5, r9
  add64 r5, 16
  ldxdw r8, [r10 - 48]
  mov64 r1, r8
  add64 r1, 8
  stxdw [r5 + 0], r1
  lddw r1, 1
  stxb [r5 + 8], r1
  stxb [r5 + 9], r1
  lddw r1, 0
  stxb [r5 + 10], r1
  stxb [r5 + 11], r1
  stxb [r5 + 12], r1
  stxb [r5 + 13], r1
  stxb [r5 + 14], r1
  stxb [r5 + 15], r1
  ldxdw r8, [r10 - 56]
  mov64 r1, r8
  add64 r1, 8
  stxdw [r5 + 16], r1
  lddw r1, 1
  stxb [r5 + 24], r1
  lddw r1, 0
  stxb [r5 + 25], r1
  stxb [r5 + 26], r1
  stxb [r5 + 27], r1
  stxb [r5 + 28], r1
  stxb [r5 + 29], r1
  stxb [r5 + 30], r1
  stxb [r5 + 31], r1
  mov64 r8, r9
  add64 r8, 48
  ldxdw r1, [r10 - 64]
  add64 r1, 8
  stxdw [r8 + 0], r1
  mov64 r1, r9
  add64 r1, 16
  stxdw [r8 + 8], r1
  lddw r1, 2
  stxdw [r8 + 16], r1
  stxdw [r8 + 24], r9
  lddw r1, 12
  stxdw [r8 + 32], r1
  stxdw [r10 - 80], r8
  mov64 r5, r9
  add64 r5, 88
{emitFillAccountInfoFromHeader 48}  add64 r5, 56
{emitFillAccountInfoFromHeader 56}  add64 r5, 56
{emitFillAccountInfoFromHeader 64}  ldxdw r1, [r10 - 80]
  mov64 r2, r9
  add64 r2, 88
  lddw r3, 3
  lddw r4, 0
  lddw r5, 0
  call sol_invoke_signed_c
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
    | .systemTransfer amount =>
      acc := acc ++ (← emitSystemTransfer p label amount)
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
        | .clockSlot | .signerKey0 => do
          let load ← loadVal p v 24
          acc := acc ++ load
          acc := acc ++ (← emitStoreAndReturn p destHint 24)
        | .evmCaller | .evmBlockNumber =>
          throw "extract/unsupported: svm rejects evm leaf"
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
    if IR.usesSystemTransfer p then
      "  ldxdw r7, [r10 - 72]\n  add64 r7, 8\n"
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
    if IR.usesSystemTransfer p then
      -- transfer 程序无状态账户；init 只做三账户形状检查。
      return s!"{label}:\n{preludeTransfer label (ixLenOf m)}body_{label}:\n  lddw r0, 0\n  exit\n"
    else
      let body ← emitInitBody p marker label m.ops
      return s!"{label}:\n{prelude p marker label (ixLenOf m) true true true}{body}"
  | .increment =>
    if Ops.hasSystemTransfer m.ops then
      let body ← emitMutBody p label m.ops
      return s!"{label}:\n{preludeTransfer label (ixLenOf m)}{body}"
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
    let jump := if IR.usesSystemTransfer program then s!"  ja {label}\n" else s!"  call {label}\n  exit\n"
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
    if IR.usesSystemTransfer program then
      emitWalkThreeAccounts "entry" "err_unknown_disc" ++
        "  ldxdw r1, [r10 - 72]\n  ldxdw r1, [r1 + 0]\n  jlt r1, 8, err_unknown_disc\n  ja dispatch_begin\n"
    else
      s!"\
  ldxb r1, [r6 + ACC0_HEADER + 0]
  jne r1, 0xff, err_unknown_disc
  ldxdw r1, [r6 + INSTRUCTION_DATA_LEN]
  jlt r1, 8, err_unknown_disc
  ja dispatch_begin
"
  let dispatchHead :=
    if IR.usesSystemTransfer program then
      "dispatch_begin:\n  ldxdw r1, [r10 - 72]\n  add64 r1, 8\n  ldxdw r1, [r1 + 0]\n"
    else
      "dispatch_begin:\n  ldxdw r1, [r6 + INSTRUCTION_DATA]\n"
  -- emitDispatch 自己写了 dispatch_begin 头；transfer 要换掉。
  let dispatchTxt :=
    if IR.usesSystemTransfer program then
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
