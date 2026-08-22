import SolanaLean.Ops
import SolanaLean.Sha256

namespace SolanaLean.IR

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
  methods : Array Method
  deriving BEq, Repr, Inhabited

def Program.fields (p : Program) : Array String :=
  p.slots.map (·.name)

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

/-- 程序是否含封闭 `system.transfer`（三账户：payer / recipient / System）。 -/
def usesSystemTransfer (p : Program) : Bool :=
  p.methods.any (fun m => Ops.hasSystemTransfer m.ops)

def inputLayout (p : Program) : InputLayout :=
  if usesSystemTransfer p then
    -- 三个 data_len=0 的账户：每个 span = 0x2860，instruction 紧跟第三账户 rent。
    let acc0 := 8
    let acc1 := acc0 + accountSpan 0
    let acc2 := acc1 + accountSpan 0
    let rent2 := acc2 + accountSpan 0 - 8
    { rentEpoch := rent2
      instructionDataLen := rent2 + 8
      instructionData := rent2 + 16 }
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
  | .lit n => s!"l{n.toNat}"
  | .field b n => s!"f.{n}({valCanon b})"
  | .clockSlot => "clk"
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
  | .indexGet b n i k => s!"idx.{n}[{valCanon i}/{k}]({valCanon b})"
  | .loopIx => "ix"

private partial def opsCanon (ops : Array Ops.Op) : String :=
  let rec one (op : Ops.Op) : String :=
    match op with
    | .checkedAddU64 l r => s!"add({valCanon l},{valCanon r})"
    | .checkedSubU64 l r => s!"sub({valCanon l},{valCanon r})"
    | .checkedMulU64 l r => s!"mul({valCanon l},{valCanon r})"
    | .checkedDivU64 l r => s!"div({valCanon l},{valCanon r})"
    | .checkedModU64 l r => s!"mod({valCanon l},{valCanon r})"
    | .ite c l r t f => s!"ite.{cmpTag c}({valCanon l},{valCanon r},[{opsCanon t}],[{opsCanon f}])"
    | .systemTransfer v => s!"xfer({valCanon v})"
    | .evmDeposit v => s!"edep({valCanon v})"
    | .evmSendEth a b c d =>
        s!"esend({valCanon a},{valCanon b},{valCanon c},{valCanon d})"
    | .evmLog n v => s!"elog.{n}({valCanon v})"
    | .forAccum n v => s!"for({n},{valCanon v})"
    | .indexSet n i v k => s!"iset.{n}[{valCanon i}/{k}]({valCanon v})"
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

end SolanaLean.IR
