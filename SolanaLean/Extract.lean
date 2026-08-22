import Lean
import SolanaLean.IR
import SolanaLean.Ops
import SolanaLean.Profile

open Lean

namespace SolanaLean.Extract

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

private def isConstNamed (e : Expr) (n : Name) : Bool :=
  e.getAppFn.constName? == some n

private def strip (e : Expr) : Expr :=
  e.consumeMData

/-- `s.value` / `State.value s` -/
private def asFieldValue (e : Expr) : Option Ops.Val :=
  let e := strip e
  let fn := e.getAppFn
  let args := e.getAppArgs
  match fn.constName? with
  | some n =>
    if n.toString.endsWith ".value" && args.size ≥ 1 then
      match args[args.size - 1]! with
      | .bvar i => some (.field (.arg i) "value")
      | _ => none
    else none
  | none => none

private def asArg (e : Expr) : Option Ops.Val :=
  match strip e with
  | .bvar i => some (.arg i)
  | _ => asFieldValue e

/-- `x + y` via `HAdd.hAdd`. -/
private def asAdd (e : Expr) : Option (Ops.Val × Ops.Val) :=
  let e := strip e
  if isConstNamed e ``HAdd.hAdd then
    let args := e.getAppArgs
    if args.size ≥ 2 then
      match asArg args[args.size - 2]!, asArg args[args.size - 1]! with
      | some x, some y => some (x, y)
      | _, _ => none
    else none
  else none

/-- `u64Max - x` -/
private def asSubFromMax (e : Expr) : Option Ops.Val :=
  let e := strip e
  if isConstNamed e ``HSub.hSub then
    let args := e.getAppArgs
    if args.size ≥ 2 then
      let left := strip args[args.size - 2]!
      let right := args[args.size - 1]!
      if (left.getAppFn.constName?.map (·.toString.endsWith ".u64Max")).getD false then
        asArg right
      else none
    else none
  else none

/-- `s.value ≤ u64Max - delta` -/
private def asLeChecked (e : Expr) : Option (Ops.Val × Ops.Val) :=
  let e := strip e
  if isConstNamed e ``LE.le then
    let args := e.getAppArgs
    if args.size ≥ 2 then
      match asFieldValue args[args.size - 2]!, asSubFromMax args[args.size - 1]! with
      | some lhs, some rhs => some (lhs, rhs)
      | _, _ => none
    else none
  else none

private def asStateMk (e : Expr) : Option Ops.Val :=
  let e := strip e
  let n? := e.getAppFn.constName?
  if (n?.map (fun n => n.toString.endsWith ".State.mk" || n.toString.endsWith ".mk")).getD false then
    let args := e.getAppArgs
    if args.size ≥ 1 then asArg args[args.size - 1]! else none
  else none

private def asOkState (e : Expr) : Option Ops.Val :=
  let e := strip e
  if isConstNamed e ``Except.ok then
    let args := e.getAppArgs
    if args.size ≥ 1 then
      let pair := strip args[args.size - 1]!
      if isConstNamed pair ``Prod.mk then
        let pargs := pair.getAppArgs
        if pargs.size ≥ 2 then asStateMk pargs[pargs.size - 2]! else none
      else asStateMk pair
    else none
  else none

private def isErrorOverflow (e : Expr) : Bool :=
  let e := strip e
  if isConstNamed e ``Except.error then
    let args := e.getAppArgs
    if h : args.size > 0 then
      let last := strip args[args.size - 1]
      (last.getAppFn.constName?.map (·.toString.endsWith ".overflow")).getD false
    else false
  else false

/-- `fun a b => body`，返回 binder 数和体。 -/
private partial def peelLams (e : Expr) : Nat × Expr :=
  let rec go (n : Nat) (e : Expr) : Nat × Expr :=
    match strip e with
    | .lam _ _ body _ => go (n + 1) body
    | .letE _ _ _ body _ => go n body
    | e => (n, e)
  go 0 e

private def decodeInit (e : Expr) : Except String (Array Ops.Op) :=
  let (_, body) := peelLams e
  match asStateMk body with
  | some v => .ok #[.returnState v]
  | none => .error "extract/unsupported: init body"

private def decodeGet (e : Expr) : Except String (Array Ops.Op) :=
  let (_, body) := peelLams e
  match asFieldValue body with
  | some v => .ok #[.returnU64 v]
  | none => .error "extract/unsupported: get body"

private def peelLets (e : Expr) : Expr :=
  let rec go (fuel : Nat) (e : Expr) : Expr :=
    match fuel with
    | 0 => e
    | fuel' + 1 =>
      match strip e with
      | .letE _ _ _ body _ => go fuel' body
      | e => e
  go 16 e

private def decodeIncrement (e : Expr) : Except String (Array Ops.Op) :=
  let (_, body) := peelLams e
  let body := strip body
  if isConstNamed body ``ite && body.getAppArgs.size ≥ 5 then
    let args := body.getAppArgs
    let cond? := args.find? (fun a => isConstNamed a ``LE.le)
    let t := peelLets args[args.size - 2]!
    let f := args[args.size - 1]!
    match cond?.bind asLeChecked, asOkState t with
    | some (lhs, rhs), some v =>
      if isErrorOverflow f then
        .ok #[.checkedAddU64 lhs rhs, .okState v, .errorOverflow]
      else
        .error "extract/unsupported: increment false branch"
    | none, _ => .error "extract/unsupported: increment cond"
    | _, none => .error "extract/unsupported: increment then"
  else
    .error "extract/unsupported: increment not ite"

def decodeMethod (kind : IR.MethodKind) (e : Expr) : Except String (Array Ops.Op) :=
  match kind with
  | .init => decodeInit e
  | .get => decodeGet e
  | .increment => decodeIncrement e

def extractMethod (env : Environment) (kind : IR.MethodKind) (n : Name) :
    Except String IR.Method := do
  let some info := env.find? n
    | throw s!"extract/unsupported: unknown {n}"
  let some e := info.value?
    | throw s!"extract/unsupported: no value {n}"
  let sketch := sketchOfExpr e
  let ops ← decodeMethod kind e
  return { kind, name := n.toString, sketch, ops }

def extractCounter (env : Environment)
    (initName incrementName getName : Name)
    (programName : String := "Counter") :
    Except String IR.Program := do
  match Profile.checkAll env #[initName, incrementName, getName] with
  | .reject reason => throw reason
  | .accept => pure ()
  let initM ← extractMethod env .init initName
  let incM ← extractMethod env .increment incrementName
  let getM ← extractMethod env .get getName
  unless Ops.hasCheckedAdd incM.ops do
    throw "extract/unsupported: increment missing checkedAddU64"
  let program : IR.Program := { name := programName, methods := #[initM, incM, getM] }
  unless IR.isCounterShape program do
    throw "extract/unsupported: not counter shape"
  return program

end SolanaLean.Extract
