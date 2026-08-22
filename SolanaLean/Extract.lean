import Lean
import SolanaLean.IR
import SolanaLean.Profile

open Lean

namespace SolanaLean.Extract

/-- 定义体里出现的常量名，排序后作为 body sketch。改函数体就会变。 -/
def sketchOfExpr (e : Expr) : Array String :=
  let names := e.getUsedConstantsAsSet.toList.toArray.qsort (·.toString < ·.toString)
  names.map (·.toString)

def sketchOfDecl (env : Environment) (n : Name) : Except String (Array String) :=
  match env.find? n with
  | none => .error s!"extract/unsupported: unknown {n}"
  | some info =>
    match info.value? with
    | none => .error s!"extract/unsupported: no value {n}"
    | some e => .ok (sketchOfExpr e)

/-- 抽出 Counter 形状 + 三方法 body sketch。先过 Profile。 -/
def extractCounter (env : Environment)
    (initName incrementName getName : Name)
    (programName : String := "Counter") :
    Except String IR.Program := do
  match Profile.checkAll env #[initName, incrementName, getName] with
  | .reject reason => throw reason
  | .accept => pure ()
  let initS ← sketchOfDecl env initName
  let incS ← sketchOfDecl env incrementName
  let getS ← sketchOfDecl env getName
  let methods : Array IR.Method := #[
    { kind := .init, name := initName.toString, sketch := initS },
    { kind := .increment, name := incrementName.toString, sketch := incS },
    { kind := .get, name := getName.toString, sketch := getS }
  ]
  let program : IR.Program := { name := programName, methods }
  unless IR.isCounterShape program do
    throw "extract/unsupported: not counter shape"
  return program

end SolanaLean.Extract
