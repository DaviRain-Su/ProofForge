import Lean
import SolanaLean.IR
import SolanaLean.Ops
import SolanaLean.Profile

open Lean

namespace SolanaLean.Extract

def sketchOfExpr (e : Expr) : Array String :=
  let names := e.getUsedConstantsAsSet.toList.toArray.qsort (·.toString < ·.toString)
  names.map (·.toString)

private def isConstNamed (e : Expr) (n : Name) : Bool :=
  e.consumeMData.getAppFn.constName? == some n

private def strip (e : Expr) : Expr :=
  e.consumeMData

private def endsWith (e : Expr) (suf : String) : Bool :=
  (e.getAppFn.constName?.map (·.toString.endsWith suf)).getD false

private def peelLams (e : Expr) : Nat × Expr :=
  let rec go (fuel : Nat) (n : Nat) (e : Expr) : Nat × Expr :=
    match fuel with
    | 0 => (n, e)
    | fuel' + 1 =>
      match strip e with
      | .lam _ _ body _ => go fuel' (n + 1) body
      | .letE _ _ _ body _ => go fuel' n body
      | e => (n, e)
  go 32 0 e

private def peelLets (e : Expr) : Expr :=
  let rec go (fuel : Nat) (e : Expr) : Expr :=
    match fuel with
    | 0 => e
    | fuel' + 1 =>
      match strip e with
      | .letE _ _ _ body _ => go fuel' body
      | e => e
  go 16 e

private def asLit (fuel : Nat) (e : Expr) : Option Ops.Val :=
  match fuel with
  | 0 => none
  | fuel' + 1 =>
    match strip e with
    | .lit (.natVal n) =>
      if n < UInt64.size then some (.lit (UInt64.ofNat n)) else none
    | e =>
      if isConstNamed e ``OfNat.ofNat then
        let args := e.getAppArgs
        if args.size ≥ 1 then asLit fuel' args[args.size - 1]! else none
      else none

private def asVal (fuel : Nat) (e : Expr) : Option Ops.Val :=
  match fuel with
  | 0 => none
  | fuel' + 1 =>
    let e := strip e
    match e with
    | .bvar i => some (.arg i)
    | _ =>
      if let some v := asLit fuel' e then some v
      else if let some n := e.getAppFn.constName? then
        let field := n.toString
        let user :=
          field.startsWith "Examples." || field.startsWith "SolanaLean." ||
            field.startsWith "Tests."
        if user && field.contains "." && e.getAppArgs.size ≥ 1 then
          let proj :=
            match field.splitOn "." with
            | [] => field
            | parts => parts.getLast!
          if proj == "mk" || proj == "ok" || proj == "error" then none
          else
            match asVal fuel' e.getAppArgs[e.getAppArgs.size - 1]! with
            | some b => some (.field b proj)
            | none => none
        else none
      else none

private def val (e : Expr) : Option Ops.Val :=
  asVal 16 e

private def asSubFromMax (e : Expr) : Option Ops.Val :=
  let e := strip e
  if isConstNamed e ``HSub.hSub then
    let args := e.getAppArgs
    if args.size ≥ 2 && endsWith (strip args[args.size - 2]!) ".u64Max" then
      val args[args.size - 1]!
    else none
  else none

/-- `x ≤ u64Max - y`  →  checked add x y -/
private def asCheckedAddGuard (e : Expr) : Option (Ops.Val × Ops.Val) :=
  let e := strip e
  if isConstNamed e ``LE.le then
    let args := e.getAppArgs
    if args.size ≥ 2 then
      match val args[args.size - 2]!, asSubFromMax args[args.size - 1]! with
      | some lhs, some rhs => some (lhs, rhs)
      | _, _ => none
    else none
  else none

/-- `x ≥ y` / `y ≤ x`  →  checked sub x y -/
private def asCheckedSubGuard (e : Expr) : Option (Ops.Val × Ops.Val) :=
  let e := strip e
  if isConstNamed e ``LE.le then
    let args := e.getAppArgs
    if args.size ≥ 2 then
      match val args[args.size - 2]!, val args[args.size - 1]! with
      | some rhs, some lhs =>
        some (lhs, rhs)
      | _, _ => none
    else none
  else if isConstNamed e ``GE.ge then
    let args := e.getAppArgs
    if args.size ≥ 2 then
      match val args[args.size - 2]!, val args[args.size - 1]! with
      | some lhs, some rhs => some (lhs, rhs)
      | _, _ => none
    else none
  else none

/-- 多字段 `State.mk a b …`：init 用第一个显式参数；checked 更新用最后一个。 -/
private def asStateMk (e : Expr) (preferLast := false) : Option Ops.Val :=
  let e := strip e
  if endsWith e ".State.mk" || endsWith e ".mk" then
    let args := e.getAppArgs
    if args.size = 0 then none
    else if preferLast then val args[args.size - 1]!
    else
      match args.findSome? val with
      | some v => some v
      | none => val args[args.size - 1]!
  else none

private def asOkState (e : Expr) : Option Ops.Val :=
  let e := peelLets (strip e)
  if isConstNamed e ``Except.ok then
    let args := e.getAppArgs
    if args.size ≥ 1 then
      let pair := strip args[args.size - 1]!
      if isConstNamed pair ``Prod.mk then
        let pargs := pair.getAppArgs
        if pargs.size ≥ 2 then asStateMk pargs[pargs.size - 2]! true else none
      else asStateMk pair true
    else none
  else none

private def isErrorOverflow (e : Expr) : Bool :=
  let e := strip e
  if isConstNamed e ``Except.error then
    let args := e.getAppArgs
    if h : args.size > 0 then
      endsWith (strip args[args.size - 1]) ".overflow"
    else false
  else false

private def decodePlain (e : Expr) : Except String (Array Ops.Op) :=
  let e := peelLets (strip e)
  if let some v := asOkState e then
    .ok #[.okState v]
  else if let some v := asStateMk e then
    .ok #[.returnState v]
  else if let some v := val e then
    match v with
    | .field _ _ => .ok #[.returnU64 v]
    | .arg _ => .ok #[.returnState v]
    | .lit _ => .ok #[.returnU64 v]
  else
    .error "extract/unsupported: body"

private def decodeIte (e : Expr) : Except String (Array Ops.Op) :=
  let e := strip e
  if !(isConstNamed e ``ite) || e.getAppArgs.size < 5 then
    decodePlain e
  else
    let args := e.getAppArgs
    let cond? := args.find? (fun a => isConstNamed a ``LE.le || isConstNamed a ``GE.ge)
    let t := peelLets args[args.size - 2]!
    let f := args[args.size - 1]!
    if !isErrorOverflow f then
      .error "extract/unsupported: false branch not overflow"
    else
      match cond?.bind asCheckedAddGuard, asOkState t with
      | some (lhs, rhs), some v =>
        .ok #[.checkedAddU64 lhs rhs, .okState v, .errorOverflow]
      | none, some v =>
        match cond?.bind asCheckedSubGuard with
        | some (lhs, rhs) =>
          .ok #[.checkedSubU64 lhs rhs, .okState v, .errorOverflow]
        | none => .error "extract/unsupported: ite cond"
      | _, none => .error "extract/unsupported: ite then"

def decodeBody (e : Expr) : Except String (Array Ops.Op) :=
  let (_, body) := peelLams e
  decodeIte body

/-- 可变入口必须是带 overflow 假支的 checked ite。 -/
def decodeMutating (e : Expr) : Except String (Array Ops.Op) := do
  let ops ← decodeBody e
  if Ops.hasCheckedArith ops then
    return ops
  else
    throw "extract/unsupported: mutating method missing checked arith"

def extractMethod (env : Environment) (kind : IR.MethodKind) (n : Name) :
    Except String IR.Method := do
  let some info := env.find? n
    | throw s!"extract/unsupported: unknown {n}"
  let some e := info.value?
    | throw s!"extract/unsupported: no value {n}"
  let sketch := sketchOfExpr e
  let ops ←
    match kind with
    | .increment => decodeMutating e
    | _ => decodeBody e
  return { kind, name := n.toString, sketch, ops }

private def peelForalls (e : Expr) : Expr :=
  let rec go (fuel : Nat) (e : Expr) : Expr :=
    match fuel with
    | 0 => e
    | fuel' + 1 =>
      match strip e with
      | .forallE _ _ body _ => go fuel' body
      | e => e
  go 32 e

private def isUInt64Type (e : Expr) : Bool :=
  e.consumeMData.getAppFn.constName? == some ``UInt64

private def fieldIsUInt64 (env : Environment) (structName fieldName : Name) : Bool :=
  match getProjFnForField? env structName fieldName with
  | none => false
  | some proj =>
    match env.find? proj with
    | none => false
    | some info => isUInt64Type (peelForalls info.type)

/-- `Examples.Counter.init` → `Counter`。 -/
def programNameOfInit (n : Name) : String :=
  match n with
  | .str (.str _ mod) "init" => mod
  | .str _ "init" => "Program"
  | _ => "Program"

/-- 从 `init` 返回类型收字段。必须是无 `extends`、全 `UInt64` 的 structure。 -/
def inferFields (env : Environment) (initName : Name) : Except String (Array String) := do
  let some info := env.find? initName
    | throw s!"extract/unsupported: unknown {initName}"
  let some structName := (peelForalls info.type).getAppFn.constName?
    | throw "extract/unsupported: init return is not a structure"
  unless isStructure env structName do
    throw s!"extract/unsupported: init return is not a structure {structName}"
  unless (getStructureParentInfo env structName).isEmpty do
    throw "extract/unsupported: structure extends"
  let names := getStructureFields env structName
  if names.isEmpty then
    throw "extract/unsupported: structure has no fields"
  let mut fields : Array String := #[]
  for n in names do
    if (isSubobjectField? env structName n).isSome then
      throw "extract/unsupported: structure extends"
    unless fieldIsUInt64 env structName n do
      throw s!"extract/unsupported: field {n} is not UInt64"
    fields := fields.push n.toString
  return fields

private def valFields : Ops.Val → Array String
  | .field b n => valFields b |>.push n
  | .arg _ => #[]
  | .lit _ => #[]

private def opFields : Ops.Op → Array String
  | .checkedAddU64 l r => valFields l ++ valFields r
  | .checkedSubU64 l r => valFields l ++ valFields r
  | .okState v => valFields v
  | .errorOverflow => #[]
  | .returnU64 v => valFields v
  | .returnState v => valFields v

private def checkUsedFields (p : IR.Program) : Except String Unit := do
  for m in p.methods do
    for op in m.ops do
      for name in opFields op do
        if (IR.fieldOffset p name).isNone then
          throw s!"extract/unsupported: unknown field {name}"

def extractProgram (env : Environment)
    (initName incrementName getName : Name)
    (programName : Option String := none)
    (fields? : Option (Array String) := none) :
    Except String IR.Program := do
  match Profile.checkAll env #[initName, incrementName, getName] with
  | .reject reason => throw reason
  | .accept => pure ()
  let inferred ← inferFields env initName
  let fields ←
    match fields? with
    | none => pure inferred
    | some fs =>
      if fs == inferred then pure fs
      else throw s!"extract/unsupported: fields {fs} != inferred {inferred}"
  let initM ← extractMethod env .init initName
  let incM ← extractMethod env .increment incrementName
  let getM ← extractMethod env .get getName
  let program : IR.Program := {
    name := programName.getD (programNameOfInit initName)
    fields
    methods := #[initM, incM, getM]
  }
  unless IR.isCounterShape program do
    throw "extract/unsupported: not three-method shape"
  checkUsedFields program
  match IR.layoutMarkerHex program with
  | .error reason => throw reason
  | .ok _ => pure ()
  return program

def extractCounter := extractProgram

end SolanaLean.Extract
