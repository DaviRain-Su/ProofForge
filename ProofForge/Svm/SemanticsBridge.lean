import SbpfSemantics.Api
import SbpfSemantics.Run
import Std.Data.HashMap

/-!
# ProofForge/Svm/SemanticsBridge

**通用语义桥**（适用于全部合约，不只是 Counter）：

  合约 def → extractProgramIR → Emit.emitAsm（`.s` 文本）
    → `assembleSf`（本模块，纯函数解析器，fail-closed）
    → `SbpfSemantics.Program`（L2 已解析指令）
    → `runSf`（SbpfSemantics 小步执行机 + Loader-v3 入口 ABI）

`.s` 方言覆盖面（未覆盖即报错）：
- 指令：`mov64 sub64 add64 mul64 div64 mod64 and64 or64 xor64 lsh64 rsh64
  arsh64`（寄存器/立即数）、`lddw`、`ldxb/ldxh/ldxw/ldxdw`、
  `stxb/stxh/stxw/stxdw`、`be16/be32/be64`、`ja`、`jeq/jne/jgt/jge/jlt/
  jle/jset`（寄存器/立即数）、`call`（标签 = 内部调用，`sol_*` =
  host syscall）、`exit`
- 行：`;` 注释、`.globl`、`.equ N, V`、`label:`
- 符号表达式：`.equ` 常量算术（`ACC0_OWNER + 8`、`-8`、`0x10`）
- 跳转/调用目标是标签，第二遍解析为 `pc+1+off` PC 相对偏移（Int16 有界）
- 未知助记符 / 未知符号 / 重复定义 → 报错（fail-closed）

`sfInput` 按程序自己的 `.equ` 表构造 Loader-v3 入口 ABI（r1 指向
NUM_ACCOUNTS / ACC0_* / INSTRUCTION_DATA 布局，附带的 program id 追加在
instruction data 之后）；`runSf` 在 SbpfSemantics 小步执行机上跑解析出的
程序并返回最终 `Machine` × `Observation`。
-/

namespace ProofForge.Svm.SemanticsBridge

open SbpfSemantics

/-! ### 词法 -/

private def hexDigit? (c : Char) : Option Nat :=
  if '0' ≤ c && c ≤ '9' then some (c.toNat - '0'.toNat)
  else if 'a' ≤ c && c ≤ 'f' then some (c.toNat - 'a'.toNat + 10)
  else if 'A' ≤ c && c ≤ 'F' then some (c.toNat - 'A'.toNat + 10)
  else none

/-- 十六进制 digit run（≥1 位），返回 (值, 剩余)。 -/
private def hexRun (cs : List Char) (acc : Nat) : Option (Nat × List Char) :=
  match cs with
  | c :: rest =>
      match hexDigit? c with
      | some d => hexRun rest (acc * 16 + d)
      | none => some (acc, c :: rest)
  | [] => some (acc, [])

/-- 十进制 digit run，同理。 -/
private partial def decRun (cs : List Char) (acc : Nat) : Option (Nat × List Char) :=
  match cs with
  | c :: rest =>
      if '0' ≤ c && c ≤ '9' then decRun rest (acc * 10 + (c.toNat - '0'.toNat))
      else some (acc, c :: rest)
  | [] => some (acc, [])

/-- 无符号字面量：十进制或 `0x` 十六进制。 -/
def numNat? (cs : List Char) : Option Nat :=
  match cs with
  | '0' :: 'x' :: rest => (hexRun rest 0).map (·.1)
  | c :: _ => if '0' ≤ c && c ≤ '9' then (decRun cs 0).map (·.1) else none
  | [] => none

/-- 带符号数字字面量（可选前导 `-`）。 -/
def numInt? (cs : List Char) : Option Int :=
  match cs with
  | [] => none
  | '-' :: rest => (numNat? rest).map (fun n => -Int.ofNat n)
  | _ => (numNat? cs).map Int.ofNat

abbrev SymEnv : Type := Std.HashMap String Int

private def symChar (c : Char) : Bool :=
  ('0' ≤ c && c ≤ '9') || ('a' ≤ c && c ≤ 'z') ||
    ('A' ≤ c && c ≤ 'Z') || c == '_'

/-- 一个项的值：数字或 `.equ` 符号。 -/
private def termValue? (equs : SymEnv) (buf : List Char) : Option Int :=
  match buf with
  | [] => none
  | c :: _ =>
      if '0' ≤ c && c ≤ '9' then (numNat? buf).map Int.ofNat
      else equs.get? (String.ofList buf)

/-- 符号表达式求值：去空格后 `term (("+"|"-") term)*`，项为数字或符号。
要求消耗整个输入，悬空运算符 / 未知符号 / 空输入 → `none`。 -/
def evalExpr? (equs : SymEnv) (raw : String) : Option Int := Id.run do
  let cs0 := raw.toList.filter (· != ' ')
  let mut total : Int := 0
  let mut sign : Int := 1
  let mut haveTerm : Bool := false
  let mut buf : List Char := []
  let mut failed : Bool := false
  for c in cs0 do
    if failed then
      pure ()
    else if c == '+' then
      if !haveTerm || buf.isEmpty then failed := true
      else
        match termValue? equs buf.reverse with
        | some v => total := total + sign * v; buf := []; haveTerm := false; sign := 1
        | none => failed := true
    else if c == '-' then
      if haveTerm then
        if buf.isEmpty then failed := true
        else
          match termValue? equs buf.reverse with
          | some v => total := total + sign * v; buf := []; haveTerm := false; sign := -1
          | none => failed := true
      else
        sign := -sign
    else
      buf := c :: buf
      haveTerm := true
  if failed then none
  else if haveTerm && !buf.isEmpty then
    (termValue? equs buf.reverse).map (fun v => total + sign * v)
  else if haveTerm then some total
  else none

/-! ### 行分类 -/

inductive AsmLine where
  | blank
  | equ (name : String) (value : Int)
  | label (name : String)
  | insn (text : String)

private def trimL (cs : List Char) : List Char := cs.dropWhile (· == ' ')
private def trimR (cs : List Char) : List Char :=
  (cs.reverse.dropWhile (· == ' ')).reverse
private def trimC (cs : List Char) : List Char := trimR (trimL cs)

private def trimStr (s : String) : String := String.ofList (trimC s.toList)

private def stripComment (line : String) : String :=
  match line.toList.findIdx? (· == ';') with
  | none => line
  | some i => String.ofList (line.toList.take i)

/-- 一行 `.s` 的分类（`.globl` / 空行 / `.equ N, V` / `label:` / 指令）。 -/
def classifyLine (raw : String) : Except String AsmLine := do
  let t := trimStr (stripComment raw)
  if t.isEmpty then .ok .blank
  else if t.startsWith ".globl" then .ok .blank
  else if t.startsWith ".equ " then
    match ((t.toList.drop 5).asString).splitOn "," with
    | [name, val] =>
        match numInt? (trimC val.toList) with
        | some v => .ok (.equ (trimStr name) v)
        | none => .error s!"semanticsBridge: bad .equ value `{val}`"
    | _ => .error s!"semanticsBridge: bad .equ line `{t}`"
  else if t.endsWith ":" then
    let name := trimStr (String.ofList t.toList.dropLast)
    if name.isEmpty then .error "semanticsBridge: empty label"
    else .ok (.label name)
  else .ok (.insn t)

/-! ### 寄存器与操作数 -/

/-- `r0`…`r10`。 -/
def reg? (tok : String) : Option Reg :=
  match trimC tok.toList with
  | 'r' :: ds =>
      if ds.isEmpty then none
      else
        match decRun ds 0 with
        | some (n, []) => if h : n < 11 then some ⟨n, h⟩ else none
        | _ => none
  | _ => none

/-- `[rN + expr]` / `[rN-expr]` / `[rN]` → (基址寄存器, 偏移)。 -/
def memOperand? (equs : SymEnv) (tok : String) : Except String (Reg × Int) := do
  let cs := trimC tok.toList
  if cs.isEmpty || cs.head! != '[' || cs.getLast! != ']' then
    .error s!"semanticsBridge: bad memory operand `{tok}`"
  else
    let inner := cs.drop 1 |>.dropLast
    let base := trimStr (String.ofList (inner.takeWhile (fun c => c != '+' && c != '-')))
    let after := inner.dropWhile (fun c => c != '+' && c != '-')
    match reg? base with
    | none => .error s!"semanticsBridge: bad memory operand `{tok}`"
    | some r =>
        match after with
        | [] => .ok (r, 0)
        | sign :: rest =>
            let s : Int := if sign == '-' then -1 else 1
            match evalExpr? equs (String.ofList rest) with
            | some v => .ok (r, s * v)
            | none => .error s!"semanticsBridge: unknown symbol in `{tok}`"

def opInt? (equs : SymEnv) (tok : String) : Except String Int :=
  match evalExpr? equs tok with
  | some v => .ok v
  | none => .error s!"semanticsBridge: bad operand `{tok}`"

def wordOfInt (v : Int) : Word := BitVec.ofInt 64 v
def off16OfInt (v : Int) : Off16 := BitVec.ofInt 16 v

/-! ### 两遍扫描 -/

structure Scan where
  equs : SymEnv
  labels : Std.HashMap String Nat
  texts : Array String

private def collectGo (lines : List String) (sc : Scan) : Except String Scan :=
  match lines with
  | [] => .ok sc
  | line :: rest => do
      match ← classifyLine line with
      | .blank => collectGo rest sc
      | .equ n v =>
          if sc.equs.contains n then
            .error s!"semanticsBridge: duplicate .equ {n}"
          else
            collectGo rest { sc with equs := sc.equs.insert n v }
      | .label name =>
          if sc.labels.contains name then
            .error s!"semanticsBridge: duplicate label {name}"
          else
            collectGo rest { sc with labels := sc.labels.insert name sc.texts.size }
      | .insn text => collectGo rest { sc with texts := sc.texts.push text }

def scanSf (asm : String) : Except String Scan :=
  collectGo (asm.splitOn "\n") ⟨{}, {}, #[]⟩

/-! ### 指令面 -/

private def aluOpc? (stem : String) (imm : Bool) : Option Opcode :=
  match stem, imm with
  | "mov", true => some .Mov64Imm
  | "mov", false => some .Mov64Reg
  | "add", true => some .Add64Imm
  | "add", false => some .Add64Reg
  | "sub", true => some .Sub64Imm
  | "sub", false => some .Sub64Reg
  | "mul", true => some .Mul64Imm
  | "mul", false => some .Mul64Reg
  | "div", true => some .Div64Imm
  | "div", false => some .Div64Reg
  | "mod", true => some .Mod64Imm
  | "mod", false => some .Mod64Reg
  | "and", true => some .And64Imm
  | "and", false => some .And64Reg
  | "or", true => some .Or64Imm
  | "or", false => some .Or64Reg
  | "xor", true => some .Xor64Imm
  | "xor", false => some .Xor64Reg
  | "lsh", true => some .Lsh64Imm
  | "lsh", false => some .Lsh64Reg
  | "rsh", true => some .Rsh64Imm
  | "rsh", false => some .Rsh64Reg
  | "arsh", true => some .Arsh64Imm
  | "arsh", false => some .Arsh64Reg
  | _, _ => none

private def jmpOpc? (stem : String) (imm : Bool) : Option Opcode :=
  match stem, imm with
  | "jeq", true => some .JeqImm
  | "jeq", false => some .JeqReg
  | "jne", true => some .JneImm
  | "jne", false => some .JneReg
  | "jgt", true => some .JgtImm
  | "jgt", false => some .JgtReg
  | "jge", true => some .JgeImm
  | "jge", false => some .JgeReg
  | "jlt", true => some .JltImm
  | "jlt", false => some .JltReg
  | "jle", true => some .JleImm
  | "jle", false => some .JleReg
  | "jset", true => some .JsetImm
  | "jset", false => some .JsetReg
  | _, _ => none

private def loadOpc? (op : String) : Option Opcode :=
  match op with
  | "ldxb" => some .Ldxb
  | "ldxh" => some .Ldxh
  | "ldxw" => some .Ldxw
  | "ldxdw" => some .Ldxdw
  | _ => none

private def storeOpc? (op : String) : Option Opcode :=
  match op with
  | "stxb" => some .Stxb
  | "stxh" => some .Stxh
  | "stxw" => some .Stxw
  | "stxdw" => some .Stxdw
  | _ => none

private def findLabelΔ (labels : Std.HashMap String Nat) (name : String) (pc : Nat)
    : Except String Int :=
  match labels.get? name with
  | none => .error s!"semanticsBridge: unknown label `{name}`"
  | some t =>
      let d : Int := (t : Int) - ((pc + 1 : Int))
      if d < -32768 || d > 32767 then
        .error s!"semanticsBridge: jump distance out of Int16 range to {name}"
      else .ok d

private def rel16Of (labels : Std.HashMap String Nat) (name : String) (pc : Nat)
    : Except String Off16 :=
  (findLabelΔ labels name pc).map off16OfInt

private def relCallOf (labels : Std.HashMap String Nat) (name : String) (pc : Nat)
    : Except String Word :=
  (findLabelΔ labels name pc).map wordOfInt

private def regArg (line : String) (a : String) : Except String Reg :=
  match reg? a with
  | some r => .ok r
  | none => .error s!"semanticsBridge: bad register `{a}` in `{line}`"

/-- 第二遍：指令文本 → `SbpfSemantics.Instr`。 -/
def decodeInsn (sc : Scan) (pc : Nat) (line : String) : Except String Instr := do
  let toks := (line.splitOn " ").filter (· != "")
  match toks with
  | [] => .error "semanticsBridge: empty instruction line"
  | op :: _ =>
    let argStr := trimStr (String.intercalate " " (toks.drop 1))
    let args : Array String :=
      if argStr.isEmpty then #[] else ((argStr.splitOn ",").map trimStr).toArray
    let argN (i : Nat) : Except String String :=
      match args[i]? with
      | some a => .ok a
      | none => .error s!"semanticsBridge: missing operand {i} in `{line}`"
    match op with
    | "exit" =>
        if args.size != 0 then .error s!"semanticsBridge: `exit` takes no operands: {line}"
        else .ok Instr.exit
    | "lddw" => do
        if args.size != 2 then .error s!"semanticsBridge: bad `lddw`: {line}" else
        let d ← regArg line (← argN 0)
        let v ← opInt? sc.equs (← argN 1)
        .ok (Instr.lddw d (wordOfInt v))
    | "be16" | "be32" | "be64" => do
        if args.size != 1 then .error s!"semanticsBridge: bad `{op}`: {line}" else
        let d ← regArg line (← argN 0)
        let bits : Nat := match op with
          | "be16" => 16 | "be32" => 32 | _ => 64
        .ok { opcode := .Be, dst := some d, imm := some (BitVec.ofNat 64 bits) }
    | o => do
        if let some opc := loadOpc? o then
          unless args.size == 2 do
            .error s!"semanticsBridge: bad load: {line}"
          let d ← regArg line (← argN 0)
          let (b, off) ← memOperand? sc.equs (← argN 1)
          .ok (Instr.loadMem opc d b (off16OfInt off))
        else if let some opc := storeOpc? o then
          unless args.size == 2 do
            .error s!"semanticsBridge: bad store: {line}"
          let (b, off) ← memOperand? sc.equs (← argN 0)
          let s ← regArg line (← argN 1)
          .ok (Instr.storeReg opc b s (off16OfInt off))
        else if o == "ja" then
          unless args.size == 1 do
            .error s!"semanticsBridge: bad `ja`: {line}"
          .ok (Instr.ja (← rel16Of sc.labels (← argN 0) pc))
        else if o == "call" then
          unless args.size == 1 do
            .error s!"semanticsBridge: bad `call`: {line}"
          let tgt ← argN 0
          match sc.labels.get? tgt with
          | some _ => .ok (Instr.callRel (← relCallOf sc.labels tgt pc))
          | none => .ok (Instr.callSyscall tgt)
        else if (jmpOpc? o true).isSome || (jmpOpc? o false).isSome then
            -- 条件跳转（如 `jne r1, 1, err`；无 64 后缀）
            unless args.size == 3 do
              .error s!"semanticsBridge: bad jump: {line}"
            let d ← regArg line (← argN 0)
            let off ← rel16Of sc.labels (← argN 2) pc
            match reg? (← argN 1) with
            | some s =>
                match jmpOpc? o false with
                | some opc => .ok (Instr.jumpReg opc d s off)
                | none => .error s!"semanticsBridge: unknown instruction {o}"
            | none =>
                let v ← opInt? sc.equs (← argN 1)
                match jmpOpc? o true with
                | some opc => .ok (Instr.jumpImm opc d (wordOfInt v) off)
                | none => .error s!"semanticsBridge: unknown instruction {o}"
        else if o.endsWith "64" then
          let stem := String.ofList (o.toList.dropLast |> .dropLast)
          -- ALU64
          unless args.size == 2 do
            .error s!"semanticsBridge: bad ALU: {line}"
          let d ← regArg line (← argN 0)
          match reg? (← argN 1) with
          | some s =>
              match aluOpc? stem false with
              | some opc => .ok (Instr.binReg opc d s)
              | none => .error s!"semanticsBridge: unknown instruction {o}"
          | none =>
              let v ← opInt? sc.equs (← argN 1)
              match aluOpc? stem true with
              | some opc => .ok (Instr.binImm opc d (wordOfInt v))
              | none => .error s!"semanticsBridge: unknown instruction {o}"
        else
          .error s!"semanticsBridge: unknown instruction `{op}` in `{line}`"

/-- 主入口：`.s` 文本 → L2 程序。任何不认识的行 / 符号 / 标签都报错。 -/
def assembleSf (asm : String) : Except String Program := do
  let sc ← scanSf asm
  let ins ← (List.range sc.texts.size).mapM (fun i => decodeInsn sc i sc.texts[i]!)
  .ok ins.toArray

/-! ### 入口 ABI 与执行 -/

/-- Loader-v3 入口的一次调用载荷。 -/
structure SfIx where
  /-- 账户 header 原始字节：布局标记 / signer / writable（合约自行校验）。 -/
  header : Array UInt8 := #[0xff, 1, 1]
  /-- 账户 32 字节 key（同时充当 program id：owner 检查比较两者）。 -/
  key : Array UInt8 := Array.replicate 32 7
  lamports : Word := 0
  /-- 账户 data 区内容（合约状态）。 -/
  data : Array UInt8 := #[]
  /-- instruction data（discriminator + LE 参数）。 -/
  ix : Array UInt8 := #[]

def le64Bytes (v : Word) : Array UInt8 :=
  (List.range 8).toArray.map
    (fun i => UInt8.ofNat ((v.toNat >>> (8 * i)) &&& 0xff))

/-- `.s` 头部的 `.equ` 常量（无符号）。 -/
def symNat? (equs : SymEnv) (name : String) : Except String Nat :=
  match equs.get? name with
  | some v =>
      match v.toNat? with
      | some n => .ok n
      | none => .error s!"semanticsBridge: .equ {name} = {v} must be nonnegative"
  | none => .error s!"semanticsBridge: missing .equ {name}"

/-- 把入口 ABI 写进 input 区：地址由程序自己的 `.equ` 表决定。
`SbpfSemantics.Machine.entry` 的 r1 = `inputStart`，与发射器 ABI 一致。 -/
def sfInput? (asm : String) (t : SfIx) : Except String (Array UInt8) := do
  let sc ← scanSf asm
  let e := sc.equs
  let numAccounts ← symNat? e "NUM_ACCOUNTS"
  let hdr ← symNat? e "ACC0_HEADER"
  let keyOff ← symNat? e "ACC0_KEY"
  let ownerOff ← symNat? e "ACC0_OWNER"
  let lamportsOff ← symNat? e "ACC0_LAMPORTS"
  let dataLenOff ← symNat? e "ACC0_DATA_LEN"
  let dataOff ← symNat? e "ACC0_DATA"
  let ixLenOff ← symNat? e "INSTRUCTION_DATA_LEN"
  let ixdOff ← symNat? e "INSTRUCTION_DATA"
  if !(dataOff + t.data.size ≤ ixLenOff) then
    .error "semanticsBridge: account data overflows into instruction data region"
  else
    -- (offset, byte) 写入表，渲染时统一落位
    let idxd {α : Type} [Inhabited α] (a : Array α) : Array (Nat × α) :=
      (List.range a.size).toArray.map (fun i => (i, a[i]!))
    let writes : Array (Nat × UInt8) :=
      ((idxd (le64Bytes 1#64)).map (fun (j, b) => (numAccounts + j, b)))
      ++ (idxd t.header).map (fun (j, b) => (hdr + j, b))
      ++ (idxd t.key).map (fun (j, b) => (keyOff + j, b))
      ++ (idxd t.key).map (fun (j, b) => (ownerOff + j, b))
      ++ (idxd (le64Bytes t.lamports)).map (fun (j, b) => (lamportsOff + j, b))
      ++ (idxd (le64Bytes (BitVec.ofNat 64 t.data.size))).map
            (fun (j, b) => (dataLenOff + j, b))
      ++ (idxd t.data).map (fun (j, b) => (dataOff + j, b))
      ++ (idxd (le64Bytes (BitVec.ofNat 64 t.ix.size))).map
            (fun (j, b) => (ixLenOff + j, b))
      ++ (idxd t.ix).map (fun (j, b) => (ixdOff + j, b))
      ++ (idxd t.key).map (fun (j, b) => (ixdOff + t.ix.size + j, b))
    let valMap : Std.HashMap Nat UInt8 :=
      writes.foldl (fun m p => m.insert p.1 p.2) ({} : Std.HashMap Nat UInt8)
    .ok ((Array.range (ixdOff + t.ix.size + 32)).map (fun i => valMap.getD i 0))

open SbpfSemantics in
/-- 在已有机器记忆上改写 instruction data 区（连续调用间共享账户状态）。 -/
def pokeIx? (asm : String) (m : Machine) (t : SfIx) : Except String Machine := do
  let sc ← scanSf asm
  let ixdOff ← symNat? sc.equs "INSTRUCTION_DATA"
  let ixLenOff ← symNat? sc.equs "INSTRUCTION_DATA_LEN"
  if !(ixdOff + t.ix.size + 32 ≤ m.mem.input.size) then
    .error "semanticsBridge: instruction data does not fit memory"
  else
    let ws : Array (Nat × UInt8) :=
      (t.ix.mapIdx (fun i b => (ixdOff + i, b)))
      ++ (le64Bytes (BitVec.ofNat 64 t.ix.size)).zipIdx.toList.map
            (fun p => (ixLenOff + p.2, p.1))
      ++ (t.key.mapIdx (fun i b => (ixdOff + t.ix.size + i, b)))
    let arr := ws.foldl (fun a p => a.set! p.1 p.2) m.mem.input
    .ok { m with mem := { m.mem with input := arr } }

open SbpfSemantics in
/-- 调试工具：小步执行并记录 PC 轨迹（`999` 表示卡住）。 -/
def traceRun (asm : String) (t : SfIx) (steps : Nat := 32) (fuel : Nat := 8192)
    : Except String (List Nat) := do
  let P ← assembleSf asm
  let input ← sfInput? asm t
  let m0 := Machine.entry input #[]
  .ok (stepLoop pfDefaultHost P m0 steps)
where
  /-- 步进循环：PC 轨迹（顺序）；`asmStep` 卡住即提前结束。 -/
  stepLoop (D : ExecDialect) (P : Program) : Machine → Nat → List Nat
    | _, 0 => []
    | m, k+1 =>
        match asmStep D P m with
        | none => []
        | some m' => m.pc :: stepLoop D P m' k

open SbpfSemantics in
/-- 初次调用：全新机器。 -/
def runSfInitial? (asm : String) (t : SfIx) (fuel : Nat := 8192)
    : Except String (Machine × Observation) := do
  let P ← assembleSf asm
  let input ← sfInput? asm t
  let m0 := Machine.entry input #[]
  let (m, o) := runFuel pfDefaultHost P fuel m0
  .ok (m, observe m o)

open SbpfSemantics in
/-- 后续调用：同一记忆（账户数据保持），重写 ix 后 `readyForNext` 再入。 -/
def runSfNext? (asm : String) (P : Program) (m : Machine) (t : SfIx) (fuel : Nat)
    : Except String (Machine × Observation) := do
  let m ← pokeIx? asm m t
  let (m, o) := runFuel pfDefaultHost P fuel m.readyForNext
  .ok (m, observe m o)

end ProofForge.Svm.SemanticsBridge
