import SolanaLean.Ops

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
  sketch : Array String := #[]
  ops : Array Ops.Op := #[]
  deriving BEq, Repr, Inhabited

/-- 单账户程序。`fields` 声明顺序 = 账户里 header 之后的 UInt64 槽顺序。 -/
structure Program where
  name : String
  fields : Array String := #["value"]
  methods : Array Method
  deriving BEq, Repr, Inhabited

def hasKind (p : Program) (k : MethodKind) : Bool :=
  p.methods.any (fun m => m.kind == k)

def isCounterShape (p : Program) : Bool :=
  hasKind p .init && hasKind p .increment && hasKind p .get

/-- Lean 声明末段 → 链上名。`init` 是 Lean 命令关键字，链上仍叫 `initialize`。 -/
def ixNameOfLean (lean : String) : String :=
  if lean == "init" then "initialize" else lean

def lastName (n : String) : String :=
  match n.splitOn "." with
  | [] => n
  | parts => parts.getLast!

def ixParamSig (kind : MethodKind) : String :=
  match kind with
  | .get => ""
  | _ => "u64"

/-- 已登记的 PF disc 立即数（SHA-256 前 8 字节按 LE 读）。 -/
def discHex (ixName : String) (kind : MethodKind) : Except String String :=
  match ixName, ixParamSig kind with
  | "initialize", "u64" => .ok "0x642858a76747495e"
  | "increment", "u64" => .ok "0x223edbd10397c79d"
  | "decrement", "u64" => .ok "0x1b92f24dfb29d300"
  | "get", "" => .ok "0x37dd90d6b076a2a4"
  | "getLeft", "" => .ok "0xe391a39d1496f393"
  | "creditLeft", "u64" => .ok "0xca5ea3052ea3b57e"
  | name, sig => .error s!"extract/unsupported: unregistered disc {name}({sig})"

def fieldOffset (p : Program) (name : String) : Option Nat :=
  match p.fields.findIdx? (· == name) with
  | some i => some (8 + i * 8)
  | none => none

def dataLen (p : Program) : Nat :=
  8 + p.fields.size * 8

/-- Loader V3 单账户：`ACC0_DATA=0x60`，后接 `10240` 再对齐到 8。 -/
def acc0Data : Nat := 0x60
def maxPermittedDataIncrease : Nat := 10240

structure InputLayout where
  rentEpoch : Nat
  instructionDataLen : Nat
  instructionData : Nat
  deriving BEq, Repr, Inhabited

def inputLayout (p : Program) : InputLayout :=
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
    for name in p.fields do
      let off := 8 + i * 8
      acc := acc.push s!"{i}:{layoutSlotName name}:0:{off}:8:u64-le"
      i := i + 1
    return acc
  s!"{p.fields.size}|{String.intercalate "|" parts.toList}"

/-- 只登记已对齐 PF 的字段表。新布局先算 SHA-256 再挂进来。 -/
def layoutMarkerHex (p : Program) : Except String String :=
  match layoutSig p with
  | "1|0:count:0:8:8:u64-le" =>
    .ok "0xbbe897f0336e6fc"
  | "2|0:left:0:8:8:u64-le|1:right:0:16:8:u64-le" =>
    .ok "0x20d45b635e2b016f"
  | sig => .error s!"extract/unsupported: unregistered layout {sig}"

def extractedCounter : Program :=
  { name := "Counter"
    fields := #["value"]
    methods := #[
      { kind := .init, name := "Examples.Counter.init", ixName := "initialize"
        ops := #[.returnState (.arg 0)] },
      { kind := .increment, name := "Examples.Counter.increment", ixName := "increment"
        ops := #[
          .checkedAddU64 (.field (.arg 1) "value") (.arg 0),
          .okState (.arg 0),
          .errorOverflow
        ] },
      { kind := .increment, name := "Examples.Counter.decrement", ixName := "decrement"
        ops := #[
          .checkedSubU64 (.field (.arg 1) "value") (.arg 0),
          .okState (.arg 0),
          .errorOverflow
        ] },
      { kind := .get, name := "Examples.Counter.get", ixName := "get"
        ops := #[.returnU64 (.field (.arg 0) "value")] }
    ] }

def extractedPair : Program :=
  { name := "Pair"
    fields := #["left", "right"]
    methods := #[
      { kind := .init, name := "Examples.Pair.init", ixName := "initialize"
        ops := #[.returnState (.arg 0)] },
      { kind := .increment, name := "Examples.Pair.creditLeft", ixName := "creditLeft"
        ops := #[
          .checkedAddU64 (.field (.arg 1) "left") (.arg 0),
          .okState (.arg 0),
          .errorOverflow
        ] },
      { kind := .get, name := "Examples.Pair.getLeft", ixName := "getLeft"
        ops := #[.returnU64 (.field (.arg 0) "left")] }
    ] }

def counterProgram (name : String := "Counter") : Program :=
  { name
    fields := #["value"]
    methods := #[
      { kind := .init, name := "init", ixName := "initialize" },
      { kind := .increment, name := "increment", ixName := "increment" },
      { kind := .get, name := "get", ixName := "get" }
    ] }

end SolanaLean.IR
