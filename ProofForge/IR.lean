import ProofForge.Ops
import ProofForge.Core.Schema
import ProofForge.Core.Eval
import ProofForge.Crypto.Sha256

namespace ProofForge.IR

open ProofForge.Crypto

/--
Agave `MAX_TX_ACCOUNT_LOCKS` 在 feature 关着时是 64，开了是 128。
官方文档当前强制值仍是 64：
https://solana.com/docs/core/transactions
https://solana.com/docs/core/constants-reference
-/
def maxTxAccountLocks : Nat := 64

/--
Agave `MAX_ACCOUNTS_PER_INSTRUCTION` = 255
（`MAX_ACCOUNTS_PER_TRANSACTION` 256 里留一个 `NON_DUP_MARKER`）。
本仓账户下标按这个封顶，不是随便写的 7。
-/
def maxAccountsPerInstruction : Nat := 255

/-- 账户下标合法：`0 ≤ acc < maxTxAccountLocks`。 -/
def accInRange (acc : Nat) : Bool :=
  acc < maxTxAccountLocks

inductive MethodKind where
  | init
  | increment
  | get
  deriving BEq, Repr, Inhabited, DecidableEq

structure Method where
  kind : MethodKind
  name : String
  /-- 链上 instruction 名。Lean `init` 映射为 `initialize`。 -/
  ixName : String := ""
  /-- instruction data 里参数个数（不含 8 字节 disc）。 -/
  paramCount : Nat := 0
  /-- 每个参数的物理宽：1/2/4/8。默认全 8。 -/
  paramWidths : Array Nat := #[]
  /-- view 返回叶数。1 = 单 `uint*`；2 = `(uint64,uint64)`。 -/
  retCount : Nat := 1
  sketch : Array String := #[]
  ops : Array Ops.Op := #[]
  /-- Target-neutral state semantics. Empty/default only for legacy hand-authored fixtures. -/
  evaluation : Core.Evaluation := {}
  deriving BEq, Repr, Inhabited

/-- 账户槽。偏移从 header 后累加。 -/
structure Slot where
  name : String
  width : Nat := 8
  abi : String := "u64-le"
  deriving BEq, Repr, Inhabited

/-- 单账户程序。`slots` 声明顺序 = 账户槽顺序。`fields` 是槽名，兼容旧调用。 -/
structure Program where
  name : String
  slots : Array Slot := #[{ name := "value" }]
  /-- Source-level typed identity for each flattened slot. Empty only for legacy hand-written fixtures. -/
  schema : Core.Schema := {}
  methods : Array Method
  deriving BEq, Repr, Inhabited

def Program.fields (p : Program) : Array String :=
  p.slots.map (·.name)

def slotsOfSchema (schema : Core.Schema) : Array Slot :=
  schema.leaves.map fun leaf =>
    { name := leaf.name, width := leaf.width, abi := leaf.abi }

/-- Extracted programs must keep the compatibility slots as a lossless physical view of the typed schema. -/
def schemaMatchesSlots (p : Program) : Bool :=
  p.schema.isEmpty || slotsOfSchema p.schema == p.slots

def hasKind (p : Program) (k : MethodKind) : Bool :=
  p.methods.any (fun m => m.kind == k)

/-- 至少一个 init、一个 mutate、一个 view。 -/
def isProgramShape (p : Program) : Bool :=
  hasKind p .init && hasKind p .increment && hasKind p .get

def isCounterShape (p : Program) : Bool :=
  isProgramShape p

/-- Lean 声明末段 → 链上名。`init` 是 Lean 命令关键字，链上仍叫 `initialize`。 -/
def ixNameOfLean (lean : String) : String :=
  if lean == "init" then "initialize" else lean

def lastName (n : String) : String :=
  match n.splitOn "." with
  | [] => n
  | parts => parts.getLast!

def ixParamSig (paramCount : Nat) : String :=
  String.intercalate "," (List.replicate paramCount "u64")

private def hexDigit (n : Nat) : Char :=
  if n < 10 then Char.ofNat (n + 48) else Char.ofNat (n + 87)

def u64Hex (n : UInt64) : String :=
  let rec go (fuel : Nat) (v : Nat) (acc : String) : String :=
    match fuel with
    | 0 => acc
    | fuel' + 1 =>
      if v = 0 && acc ≠ "" then acc
      else go fuel' (v / 16) (String.singleton (hexDigit (v % 16)) ++ acc)
  let s := go 17 n.toNat ""
  if s = "" then "0" else s

/-- `sha256("proof-forge-solana-v1:" ++ name ++ "(" ++ sig ++ ")")` 前 8 字节，小端。 -/
def discPreimage (ixName : String) (paramCount : Nat) : String :=
  s!"proof-forge-solana-v1:{ixName}({ixParamSig paramCount})"

def discHexOf (ixName : String) (paramCount : Nat) : Except String String :=
  .ok s!"0x{u64Hex (Sha256.first8Le (discPreimage ixName paramCount))}"

def discHex (m : Method) : Except String String :=
  discHexOf m.ixName m.paramCount

def defaultParamCount (kind : MethodKind) : Nat :=
  match kind with
  | .get => 0
  | _ => 1

def fieldOffset (p : Program) (name : String) : Option Nat :=
  Id.run do
    let mut off : Nat := 8
    for s in p.slots do
      if s.name == name then return some off
      off := off + s.width
    return none

def fieldWidth (p : Program) (name : String) : Option Nat :=
  (p.slots.find? (·.name == name)).map (·.width)

structure VectorStorage where
  baseSlot : Nat
  length : Nat
  strideBytes : Nat
  strideSlots : Nat
  deriving BEq, Repr, Inhabited

private def legacyVectorStorage (p : Program) (name : String) : Option VectorStorage :=
  let pre0 := name ++ "_0"
  let group :=
    p.slots.filter fun s => s.name == pre0 || s.name.startsWith (pre0 ++ "_")
  if group.isEmpty then none
  else
    let width := group.foldl (init := 0) fun acc s => acc + s.width
    let digitPref (s : String) : String :=
      Id.run do
        let mut out := ""
        for c in s.toList do
          if c.isDigit then out := out.push c else return out
        return out
    let n :=
      p.slots.foldl (init := 0) fun acc s =>
        let rest :=
          if s.name.startsWith (name ++ "_") then
            digitPref (s.name.drop (name.length + 1) |>.copy)
          else ""
        match rest.toNat? with
        | some i => Nat.max acc (i + 1)
        | none => acc
    let baseSlot := p.slots.findIdx fun s => s.name == pre0 || s.name.startsWith (pre0 ++ "_")
    if n = 0 || width = 0 then none
    else some { baseSlot, length := n, strideBytes := width, strideSlots := group.size }

/-- Typed vector layout for extracted programs; the string parser is isolated here for old Golden fixtures. -/
def vectorStorage (p : Program) (name : String) : Option VectorStorage :=
  match p.schema.vector? name with
  | some vector => do
      let baseSlot ← p.schema.vectorBaseLeafIndex? vector
      return {
        baseSlot
        length := vector.length
        strideBytes := vector.elementBytes
        strideSlots := vector.elementLeaves
      }
  | none => legacyVectorStorage p name

/-- `cells` / `nodes` 这类定长向量的元素个数和每元素字节数。 -/
def vectorElem (p : Program) (name : String) : Option (Nat × Nat) :=
  (vectorStorage p name).map fun layout => (layout.length, layout.strideBytes)

def vectorLenOf (p : Program) (name : String) (given : Nat) : Nat :=
  if given ≠ 0 then given
  else match vectorElem p name with | some (n, _) => n | none => 0

def vectorStride (p : Program) (name : String) : Nat :=
  match vectorElem p name with
  | some (_, w) => w
  | none => 8

private def slotOffsetAt (p : Program) (index : Nat) : Option Nat :=
  if index ≥ p.slots.size then none
  else
    let before := p.slots.extract 0 index
    some (8 + before.foldl (init := 0) fun acc slot => acc + slot.width)

def vectorBaseOffset (p : Program) (name : String) : Option Nat := do
  let layout ← vectorStorage p name
  slotOffsetAt p layout.baseSlot

def vectorBaseSlot (p : Program) (name : String) : Option Nat :=
  (vectorStorage p name).map (·.baseSlot)

private def legacyVectorLeafOff (p : Program) (name leaf : String) : Nat :=
  let pre0 := name ++ "_0"
  Id.run do
    let mut off : Nat := 0
    for s in p.slots do
      if s.name == pre0 || s.name.startsWith (pre0 ++ "_") then
        if s.name == pre0 ++ "_" ++ leaf || (leaf.isEmpty && s.name == pre0) then
          return off
        off := off + s.width
    return off

/-- `nodes[i].value` 相对 `nodes_0_left` 的叶内偏移。 -/
def vectorLeafOff (p : Program) (name leaf : String) : Nat :=
  match p.schema.vector? name with
  | some vector => Id.run do
      let mut off : Nat := 0
      for item in p.schema.vectorElementLeaves vector do
        if vector.relativeLeafName item == leaf then return off
        off := off + item.width
      return off
  | none => legacyVectorLeafOff p name leaf

private def legacyVectorLeafName (p : Program) (name : String) (off : Nat) : String :=
  let pre0 := name ++ "_0"
  Id.run do
    let mut acc : Nat := 0
    for s in p.slots do
      if s.name == pre0 || s.name.startsWith (pre0 ++ "_") then
        if acc == off then
          let suf := pre0 ++ "_"
          if s.name.startsWith suf then return (s.name.drop suf.length |>.copy)
          else return ""
        acc := acc + s.width
    return "value"

/-- 叶内偏移 → 字段名。`0` 对叶子向量仍是整元素。 -/
def vectorLeafName (p : Program) (name : String) (off : Nat) : String :=
  match p.schema.vector? name with
  | some vector => Id.run do
      let mut acc : Nat := 0
      for item in p.schema.vectorElementLeaves vector do
        if acc == off then return vector.relativeLeafName item
        acc := acc + item.width
      return "value"
  | none => legacyVectorLeafName p name off

/-- First Option tag/payload names. Typed paths are authoritative for extracted programs. -/
def optionLeafNames? (p : Program) : Option (String × String) :=
  match p.schema.firstOption? with
  | some (tag, payload) => some (tag.name, payload.name)
  | none => do
      let tag ← p.slots.find? (fun slot => slot.name.endsWith "_tag")
      let payload ← p.slots.find? (fun slot => slot.name.endsWith "_p0")
      return (tag.name, payload.name)

def hasOptionLeaves (p : Program) : Bool :=
  (optionLeafNames? p).isSome

def dataLen (p : Program) : Nat :=
  let raw := 8 + p.slots.foldl (init := 0) fun acc s => acc + s.width
  let pad := (8 - raw % 8) % 8
  raw + pad

/-- Loader V3 单账户：`ACC0_DATA=0x60`，后接 `10240` 再对齐到 8。 -/
def acc0Data : Nat := 0x60
def maxPermittedDataIncrease : Nat := 10240

structure InputLayout where
  rentEpoch : Nat
  instructionDataLen : Nat
  instructionData : Nat
  deriving BEq, Repr, Inhabited

/-- 账户前缀到 data：header 8 + key 32 + owner 32 + lamports 8 + data_len 8 = 88。 -/
def accountPrefix : Nat := 0x58

def accountSpan (accountDataLen : Nat) : Nat :=
  let dataEnd := accountPrefix + accountDataLen + maxPermittedDataIncrease
  let align := (8 - dataEnd % 8) % 8
  dataEnd + align + 8

/-- 程序是否含 CPI。 -/
def usesCpi (p : Program) : Bool :=
  p.methods.any (fun m => Ops.hasInvoke m.ops)

/-- 要走多账户虚地址 walk：有 CPI，或读账户 ≥1 叶子。 -/
def usesWalk (p : Program) : Bool :=
  usesCpi p || p.methods.any (fun m => Ops.hasAcc1 m.ops)

def usesSystemTransfer (p : Program) : Bool :=
  usesCpi p

/-- 外层账户数：invoke 下标最大值 + 1；叶子下标最大值 + 1。 -/
def cpiAccountCount (p : Program) : Nat :=
  let rec maxIx (fuel : Nat) (ops : Array Ops.Op) (acc : Nat) : Nat :=
    match fuel with
    | 0 => acc
    | fuel' + 1 =>
      ops.foldl (init := acc) fun a op =>
        match op with
        | .invoke prog metas .. =>
          let m := metas.foldl (init := prog) fun b mt => Nat.max b mt.acc
          Nat.max a m
        | .ite _ _ _ t f => Nat.max (maxIx fuel' t a) (maxIx fuel' f a)
        | .forBody _ body => maxIx fuel' body a
        | _ => a
  let n := p.methods.foldl (init := 0) fun a m => Nat.max a (maxIx 8 m.ops 0)
  let fromInvoke := if usesCpi p then Nat.max 2 (n + 1) else 0
  let fromLeaves := p.methods.foldl (init := 0) fun a m => Nat.max a (Ops.opsMinAccounts m.ops)
  Nat.max fromInvoke fromLeaves

def inputLayout (p : Program) : InputLayout :=
  if usesWalk p then
    -- N 个 data_len=0 的账户：每个 span = 0x2860，instruction 紧跟最后账户 rent。
    let n := cpiAccountCount p
    let rec lastRent (i : Nat) (off : Nat) : Nat :=
      match i with
      | 0 => off - 8
      | i' + 1 => lastRent i' (off + accountSpan 0)
    let rent := lastRent n 8
    { rentEpoch := rent
      instructionDataLen := rent + 8
      instructionData := rent + 16 }
  else
    let dataEnd := acc0Data + dataLen p + maxPermittedDataIncrease
    let align := (8 - dataEnd % 8) % 8
    let rent := dataEnd + align
    { rentEpoch := rent
      instructionDataLen := rent + 8
      instructionData := rent + 16 }

/-- StateCell 单字段历史名是 `count`，Lean 侧叫 `value`。 -/
def layoutSlotName (name : String) : String :=
  if name == "value" then "count" else name

/-- `n|i:name:0:off:8:u64-le|…`，与 PF `proof-forge-solana-layout-v1:` 一致。 -/
def layoutSig (p : Program) : String :=
  let parts := Id.run do
    let mut acc : Array String := #[]
    let mut i : Nat := 0
    let mut off : Nat := 8
    for s in p.slots do
      acc := acc.push s!"{i}:{layoutSlotName s.name}:0:{off}:{s.width}:{s.abi}"
      off := off + s.width
      i := i + 1
    return acc
  s!"{p.slots.size}|{String.intercalate "|" parts.toList}"

/-- `sha256("proof-forge-solana-layout-v1:" ++ layoutSig)` 前 8 字节，大端。 -/
def layoutPreimage (p : Program) : String :=
  s!"proof-forge-solana-layout-v1:{layoutSig p}"

def layoutMarkerHex (p : Program) : Except String String :=
  .ok s!"0x{u64Hex (Sha256.first8Be (layoutPreimage p))}"

def counterProgram (name : String := "Counter") : Program :=
  { name
    slots := #[{ name := "value" }]
    methods := #[
      { kind := .init, name := "init", ixName := "initialize", paramCount := 1 },
      { kind := .increment, name := "increment", ixName := "increment", paramCount := 1 },
      { kind := .get, name := "get", ixName := "get", paramCount := 0 }
    ] }

private def kindTag : MethodKind → String
  | .init => "init"
  | .increment => "mut"
  | .get => "view"

private def cmpTag : Ops.Cmp → String
  | .eq => "eq" | .ne => "ne" | .lt => "lt"
  | .le => "le" | .gt => "gt" | .ge => "ge"

private def valCanon : Ops.Val → String
  | .arg i => s!"a{i}"
  | .local i => s!"v{i}"
  | .lit n => s!"l{n.toNat}"
  | .field b n => s!"f.{n}({valCanon b})"
  | .clockSlot => "clk"
  | .clockEpoch => "epo"
  | .unixTime => "unix"
  | .slotsPerEpoch => "spe"
  | .signerKey0 => "k0"
  | .evmCaller => "ecall"
  | .evmBlockNumber => "eblk"
  | .evmTimestamp => "ets"
  | .evmChainId => "echain"
  | .evmSelf => "eself"
  | .evmCallValue => "eval"
  | .evmSelfBalance => "ebal"
  | .evmCallerW0 => "ecw0"
  | .evmCallerW1 => "ecw1"
  | .evmCallerW2 => "ecw2"
  | .evmSelfW0 => "esw0"
  | .evmSelfW1 => "esw1"
  | .evmSelfW2 => "esw2"
  | .bitAnd l r => s!"and({valCanon l},{valCanon r})"
  | .bitOr l r => s!"or({valCanon l},{valCanon r})"
  | .bitXor l r => s!"xor({valCanon l},{valCanon r})"
  | .bitNot v => s!"not({valCanon v})"
  | .shiftL l r => s!"shl({valCanon l},{valCanon r})"
  | .shiftR l r => s!"shr({valCanon l},{valCanon r})"
  | .indexGet b n i k off =>
      if off == 0 then s!"idx.{n}[{valCanon i}/{k}]({valCanon b})"
      else s!"idx.{n}+{off}[{valCanon i}/{k}]({valCanon b})"
  | .loopIx => "ix"
  | .select c l r t f =>
      s!"sel.{repr c}({valCanon l},{valCanon r},{valCanon t},{valCanon f})"
  | .addU64 l r => s!"uadd({valCanon l},{valCanon r})"
  | .subU64 l r => s!"usub({valCanon l},{valCanon r})"
  | .mulU64 l r => s!"umul({valCanon l},{valCanon r})"
  | .divU64 l r => s!"udiv({valCanon l},{valCanon r})"
  | .modU64 l r => s!"umod({valCanon l},{valCanon r})"
  | .mapGetU64 b k => s!"vg({valCanon b},{valCanon k})"
  | .mapGetAddr b a0 a1 a2 =>
      s!"vga({valCanon b},{valCanon a0},{valCanon a1},{valCanon a2})"
  | .mapGetPair b a0 a1 a2 c0 c1 c2 =>
      s!"vgp({valCanon b},{valCanon a0},{valCanon a1},{valCanon a2},{valCanon c0},{valCanon c1},{valCanon c2})"
  | .accLamports0 => "lp0"
  | .accOwner0 => "ow0"
  | .accDataLen0 => "dl0"
  | .accN => "nacc"
  | .isSigner0 => "sg0"
  | .isWritable0 => "wr0"
  | .isExecutable0 => "ex0"
  | .accLamports1 => "lp1"
  | .accOwner1 => "ow1"
  | .accDataLen1 => "dl1"
  | .isSigner1 => "sg1"
  | .isWritable1 => "wr1"
  | .isExecutable1 => "ex1"
  | .findPda s => s!"pda.{s}"
  | .checkPda s b => s!"chk.{s}:{valCanon b}"
  | .rentExemption n => s!"rent.{n.toNat}"
  | .cpiReturn => "cret"
  | .sha256Lit s => s!"sha.{s}"
  | .keccak256Lit s => s!"kec.{s}"
  | .accKeyWord a w => s!"kw.{a}.{w}"
  | .accOwnerWord a w => s!"ow.{a}.{w}"
  | .accLamportsN a => s!"lpN.{a}"
  | .accDataLenN a => s!"dlN.{a}"
  | .isSignerN a => s!"sgN.{a}"
  | .isWritableN a => s!"wrN.{a}"
  | .isExecutableN a => s!"exN.{a}"
  | .signerKeyN a => s!"sk.{a}"
  | .ownerIsSelf a => s!"ois.{a}"


private partial def opsCanon (ops : Array Ops.Op) : String :=
  let rec one (op : Ops.Op) : String :=
    match op with
    | .letLocal i v => s!"let.{i}({valCanon v})"
    | .checkedAddU64 l r => s!"add({valCanon l},{valCanon r})"
    | .checkedSubU64 l r => s!"sub({valCanon l},{valCanon r})"
    | .checkedMulU64 l r => s!"mul({valCanon l},{valCanon r})"
    | .checkedDivU64 l r => s!"div({valCanon l},{valCanon r})"
    | .checkedModU64 l r => s!"mod({valCanon l},{valCanon r})"
    | .ite c l r t f => s!"ite.{cmpTag c}({valCanon l},{valCanon r},[{opsCanon t}],[{opsCanon f}])"
    | .evmDeposit v => s!"edep({valCanon v})"
    | .evmSendEth a b c d =>
        s!"esend({valCanon a},{valCanon b},{valCanon c},{valCanon d})"
    | .evmLog n v => s!"elog.{n}({valCanon v})"
    | .forAccum n v => s!"for({n},{valCanon v})"
    | .forBody n body => s!"forb({n},[{opsCanon body}])"
    | .indexSet n i v k off =>
        if off == 0 then s!"iset.{n}[{valCanon i}/{k}]({valCanon v})"
        else s!"iset.{n}+{off}[{valCanon i}/{k}]({valCanon v})"
    | .mapGetU64 b k => s!"mget({valCanon b},{valCanon k})"
    | .mapSetU64 b k v => s!"mset({valCanon b},{valCanon k},{valCanon v})"
    | .mapGetAddr b a0 a1 a2 =>
        s!"mgeta({valCanon b},{valCanon a0},{valCanon a1},{valCanon a2})"
    | .mapSetAddr b a0 a1 a2 v =>
        s!"mseta({valCanon b},{valCanon a0},{valCanon a1},{valCanon a2},{valCanon v})"
    | .mapGetPair b a0 a1 a2 c0 c1 c2 =>
        s!"mgetp({valCanon b},{valCanon a0},{valCanon a1},{valCanon a2},{valCanon c0},{valCanon c1},{valCanon c2})"
    | .mapSetPair b a0 a1 a2 c0 c1 c2 v =>
        s!"msetp({valCanon b},{valCanon a0},{valCanon a1},{valCanon a2},{valCanon c0},{valCanon c1},{valCanon c2},{valCanon v})"
    | .evmTokenTransfer a b c d e f g =>
        s!"ttxfer({valCanon a},{valCanon b},{valCanon c},{valCanon d},{valCanon e},{valCanon f},{valCanon g})"
    | .evmTokenBalanceOfSelf a b c =>
        s!"tbal({valCanon a},{valCanon b},{valCanon c})"
    | .invoke prog metas data seed bump =>
      let ms :=
        String.intercalate ","
          (metas.toList.map fun m =>
            s!"{m.acc}{if m.signer then "s" else ""}{if m.writable then "w" else ""}")
      let rec word (w : Ops.CpiWord) : String :=
        match w with
        | .u8le n => s!"u8.{n.toNat}"
        | .u32le n => s!"u32.{n.toNat}"
        | .u64le v => s!"u64.{valCanon v}"
        | .ascii s => s!"s.{s}"
        | .programId => "pid"
        | .accKey i => s!"k.{i}"
      let ds := String.intercalate "," (data.toList.map word)
      let seeds :=
        match seed, bump with
        | some s, some b => s!",s.{s}:{valCanon b}"
        | _, _ => ""
      s!"inv({prog},[{ms}],[{ds}]{seeds})"

    | .storeField n v => s!"st.{n}({valCanon v})"
    | .okState v => s!"ok({valCanon v})"
    | .errorOverflow => "ovf"
    | .errorNamed n => s!"err.{n}"
    | .returnU64 v => s!"retu({valCanon v})"
    | .returnState v => s!"rets({valCanon v})"
  String.intercalate ";" (ops.toList.map one)

private def methodCanon (m : Method) : String :=
  let base := s!"{kindTag m.kind}:{m.ixName}:{m.paramCount}:[{opsCanon m.ops}]"
  if (m.paramWidths.isEmpty || m.paramWidths.all (· == 8)) && m.retCount == 1 then
    base
  else
    let widths := String.intercalate "," (m.paramWidths.map toString).toList
    s!"{kindTag m.kind}:{m.ixName}:{m.paramCount}:{widths}:r{m.retCount}:[{opsCanon m.ops}]"

/-- 规范化身份：按 `ixName` 排序。不含 Lean 全名、不含 sketch。 -/
def canonical (p : Program) : String :=
  let fields := String.intercalate "," p.fields.toList
  let methods :=
    (p.methods.qsort (fun a b => a.ixName < b.ixName)).toList.map methodCanon
  s!"{p.name}|{fields}|{String.intercalate "/" methods}"

private def fnvOffset : UInt64 := 14695981039346656037
private def fnvPrime : UInt64 := 1099511628211

def fnv1a64 (s : String) : UInt64 :=
  s.toUTF8.data.foldl (init := fnvOffset) fun h b =>
    (h ^^^ b.toUInt64) * fnvPrime

/-- FNV-1a 64，十六进制，无 `0x` 前缀。 -/
def digestHex (p : Program) : String :=
  u64Hex (fnv1a64 (canonical p))

end ProofForge.IR
