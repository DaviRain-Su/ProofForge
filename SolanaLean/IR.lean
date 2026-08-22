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

def fieldOffset (p : Program) (name : String) : Option Nat :=
  match p.fields.findIdx? (· == name) with
  | some i => some (8 + i * 8)
  | none => none

def dataLen (p : Program) : Nat :=
  8 + p.fields.size * 8

def extractedCounter : Program :=
  { name := "Counter"
    fields := #["value"]
    methods := #[
      { kind := .init, name := "Examples.Counter.init"
        ops := #[.returnState (.arg 0)] },
      { kind := .increment, name := "Examples.Counter.increment"
        ops := #[
          .checkedAddU64 (.field (.arg 1) "value") (.arg 0),
          .okState (.arg 0),
          .errorOverflow
        ] },
      { kind := .get, name := "Examples.Counter.get"
        ops := #[.returnU64 (.field (.arg 0) "value")] }
    ] }

def counterProgram (name : String := "Counter") : Program :=
  { name
    fields := #["value"]
    methods := #[
      { kind := .init, name := "init" },
      { kind := .increment, name := "increment" },
      { kind := .get, name := "get" }
    ] }

end SolanaLean.IR
