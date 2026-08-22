import SolanaLean.Ops

namespace SolanaLean.IR

/-- v0 可编译方法。语义由对应的普通 Lean 函数定义，不由本结构解释。 -/
inductive MethodKind where
  | init
  | increment
  | get
  deriving BEq, Repr, Inhabited, DecidableEq

structure Method where
  kind : MethodKind
  name : String
  /-- 定义体用到的常量名，已排序。空数组表示「只声明形状、尚未抽出」。 -/
  sketch : Array String := #[]
  /-- 从 `Expr` 抽出的操作。空数组表示尚未抽出或仅形状。 -/
  ops : Array Ops.Op := #[]
  deriving BEq, Repr, Inhabited

/-- 惰性程序形状。禁止在构造过程中跑 IO 或任意元程序。 -/
structure Program where
  name : String
  methods : Array Method
  deriving BEq, Repr, Inhabited

def hasKind (p : Program) (k : MethodKind) : Bool :=
  p.methods.any (fun m => m.kind == k)

def isCounterShape (p : Program) : Bool :=
  hasKind p .init && hasKind p .increment && hasKind p .get

def hasSketches (p : Program) : Bool :=
  p.methods.all (fun m => !m.sketch.isEmpty)

/-- 与 `Extract.extractCounter` 对 `Counter.init/increment/get` 的抽出结果对齐。 -/
def extractedCounter : Program :=
  { name := "Counter"
    methods := #[
      { kind := .init, name := "SolanaLean.Counter.init"
        ops := #[.returnState (.arg 0)] },
      { kind := .increment, name := "SolanaLean.Counter.increment"
        ops := #[
          .checkedAddU64 (.field (.arg 1) "value") (.arg 0),
          .okState (.arg 0),
          .errorOverflow
        ] },
      { kind := .get, name := "SolanaLean.Counter.get"
        ops := #[.returnU64 (.field (.arg 0) "value")] }
    ] }

def counterProgram (name : String := "Counter") : Program :=
  { name
    methods := #[
      { kind := .init, name := "init" },
      { kind := .increment, name := "increment" },
      { kind := .get, name := "get" }
    ] }

end SolanaLean.IR
