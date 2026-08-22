import Lean
import SolanaLean.IR
import SolanaLean.Ops
import SolanaLean.Profile
import SolanaLean.Attr

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
        match args.findSome? (asLit fuel') with
        | some v => some v
        | none =>
          if args.size ≥ 2 then asLit fuel' args[1]! else none
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

private def asDivFromMax (e : Expr) : Option Ops.Val :=
  let e := strip e
  if isConstNamed e ``HDiv.hDiv then
    let args := e.getAppArgs
    if args.size ≥ 2 && endsWith (strip args[args.size - 2]!) ".u64Max" then
      val args[args.size - 1]!
    else none
  else none

/-- `x ≤ u64Max / y`  →  checked mul x y -/
private def asCheckedMulGuard (e : Expr) : Option (Ops.Val × Ops.Val) :=
  let e := strip e
  if isConstNamed e ``LE.le then
    let args := e.getAppArgs
    if args.size ≥ 2 then
      match val args[args.size - 2]!, asDivFromMax args[args.size - 1]! with
      | some lhs, some rhs => some (lhs, rhs)
      | _, _ => none
    else none
  else none

private def binArgs (e : Expr) : Option (Expr × Expr) :=
  let args := e.getAppArgs
  if args.size ≥ 2 then some (args[args.size - 2]!, args[args.size - 1]!) else none

private def asCmpCore (e : Expr) : Option (Ops.Cmp × Ops.Val × Ops.Val) :=
  let e := strip e
  if isConstNamed e ``Eq || isConstNamed e ``BEq.beq then
    match binArgs e with
    | some (l, r) =>
      match val l, val r with
      | some lv, some rv => some (.eq, lv, rv)
      | _, _ => none
    | none => none
  else if isConstNamed e ``Ne then
    match binArgs e with
    | some (l, r) =>
      match val l, val r with
      | some lv, some rv => some (.ne, lv, rv)
      | _, _ => none
    | none => none
  else if isConstNamed e ``LT.lt then
    match binArgs e with
    | some (l, r) =>
      match val l, val r with
      | some lv, some rv => some (.lt, lv, rv)
      | _, _ => none
    | none => none
  else if isConstNamed e ``LE.le then
    match binArgs e with
    | some (l, r) =>
      match val l, val r with
      | some lv, some rv => some (.le, lv, rv)
      | _, _ => none
    | none => none
  else if isConstNamed e ``GT.gt then
    match binArgs e with
    | some (l, r) =>
      match val l, val r with
      | some lv, some rv => some (.gt, lv, rv)
      | _, _ => none
    | none => none
  else if isConstNamed e ``GE.ge then
    match binArgs e with
    | some (l, r) =>
      match val l, val r with
      | some lv, some rv => some (.ge, lv, rv)
      | _, _ => none
    | none => none
  else none

private def asCmp (e : Expr) : Option (Ops.Cmp × Ops.Val × Ops.Val) :=
  let e := strip e
  if isConstNamed e ``Not then
    let args := e.getAppArgs
    if args.size ≥ 1 then
      match asCmpCore args[args.size - 1]! with
      | some (.eq, l, r) => some (.ne, l, r)
      | some (.ne, l, r) => some (.eq, l, r)
      | _ => none
    else none
  else asCmpCore e

/-- `x ≥ y` / `y ≤ x`  →  checked sub x y -/
private def asCheckedSubGuard (e : Expr) : Option (Ops.Val × Ops.Val) :=
  match asCmp e with
  | some (.le, rhs, lhs) => some (lhs, rhs)
  | some (.ge, lhs, rhs) => some (lhs, rhs)
  | _ => none

private def asNeZero (e : Expr) : Option Ops.Val :=
  match asCmp e with
  | some (.ne, v, .lit 0) => some v
  | some (.ne, .lit 0, v) => some v
  | _ => none

private def asEqZero (e : Expr) : Option Ops.Val :=
  match asCmp e with
  | some (.eq, v, .lit 0) => some v
  | some (.eq, .lit 0, v) => some v
  | _ => none

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

private def findBy (args : Array Expr) (p : Expr → Bool) : Option Expr :=
  args.find? p

private def lastNamedBin (want : Name) (e : Expr) : Option (Ops.Val × Ops.Val) :=
  let rec go (fuel : Nat) (e : Expr) : Option (Ops.Val × Ops.Val) :=
    match fuel with
    | 0 => none
    | fuel' + 1 =>
      let e := strip e
      if isConstNamed e want then
        match binArgs e with
        | some (l, r) =>
          match val l, val r with
          | some lv, some rv => some (lv, rv)
          | _, _ => none
        | none => none
      else
        e.getAppArgs.findSome? (go fuel')
  go 8 e

private def decodeExpr (fuel : Nat) (e : Expr) : Except String (Array Ops.Op) :=
  match fuel with
  | 0 => .error "extract/unsupported: ite depth"
  | fuel' + 1 => Id.run do
    let e := strip e
    if isConstNamed e ``ite && e.getAppArgs.size ≥ 5 then
      let args := e.getAppArgs
      let t := peelLets args[args.size - 2]!
      let f := peelLets args[args.size - 1]!
      if isErrorOverflow f then
        if let some condE := findBy args (fun a => (asCheckedAddGuard a).isSome) then
          match asCheckedAddGuard condE, asOkState t with
          | some (lhs, rhs), some v =>
            return .ok #[.checkedAddU64 lhs rhs, .okState v, .errorOverflow]
          | _, _ => return .error "extract/unsupported: ite then"
        else if let some condE := findBy args (fun a => (asCheckedMulGuard a).isSome) then
          match asCheckedMulGuard condE, asOkState t with
          | some (lhs, rhs), some v =>
            return .ok #[.checkedMulU64 lhs rhs, .okState v, .errorOverflow]
          | _, _ => return .error "extract/unsupported: ite then"
        else if let some condE := findBy args (fun a => (asCheckedSubGuard a).isSome) then
          match asCheckedSubGuard condE, asOkState t with
          | some (lhs, rhs), some v =>
            return .ok #[.checkedSubU64 lhs rhs, .okState v, .errorOverflow]
          | _, _ => return .error "extract/unsupported: ite then"
        else if let some condE := findBy args (fun a => (asNeZero a).isSome) then
          match asNeZero condE with
          | none => return .error "extract/unsupported: ite then"
          | some den =>
            let v := (asOkState t).getD (.arg 0)
            if (lastNamedBin ``HMod.hMod t).isSome then
              let (lhs, rhs) := (lastNamedBin ``HMod.hMod t).getD ((.field (.arg 1) "value"), den)
              return .ok #[.checkedModU64 lhs (if rhs == den then rhs else den), .okState v, .errorOverflow]
            else if (lastNamedBin ``UInt64.mod t).isSome then
              let (lhs, rhs) := (lastNamedBin ``UInt64.mod t).getD ((.field (.arg 1) "value"), den)
              return .ok #[.checkedModU64 lhs (if rhs == den then rhs else den), .okState v, .errorOverflow]
            else
              let (lhs, rhs) := (lastNamedBin ``HDiv.hDiv t).getD ((.field (.arg 1) "value"), den)
              return .ok #[.checkedDivU64 lhs (if rhs == den then rhs else den), .okState v, .errorOverflow]
        else
          return .error "extract/unsupported: ite cond"
      else
        let some condE := findBy args (fun a => (asCmp a).isSome)
          | return .error "extract/unsupported: ite cond"
        let some (cmp, lv, rv) := asCmp condE
          | return .error "extract/unsupported: ite cond"
        match decodeExpr fuel' t, decodeExpr fuel' f with
        | .ok thn, .ok els => return .ok #[.ite cmp lv rv thn els]
        | .error r, _ => return .error r
        | _, .error r => return .error r
    else
      return decodePlain e

def decodeBody (e : Expr) : Except String (Array Ops.Op) :=
  let (_, body) := peelLams e
  decodeExpr 16 body

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
  let ops0 ←
    match kind with
    | .increment => decodeMutating e
    | _ => decodeBody e
  let lean := IR.lastName n.toString
  let ops :=
    if lean == "modulo" then
      ops0.map fun
        | .checkedDivU64 l r => .checkedModU64 l r
        | op => op
    else ops0
  let (nLams, _) := peelLams e
  let paramCount :=
    match kind with
    | .init | .increment => 1
    | .get => if nLams ≤ 1 then 0 else nLams - 1
  return {
    kind, name := n.toString, ixName := IR.ixNameOfLean lean
    paramCount, sketch, ops
  }

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
  | .checkedMulU64 l r => valFields l ++ valFields r
  | .checkedDivU64 l r => valFields l ++ valFields r
  | .checkedModU64 l r => valFields l ++ valFields r
  | .ite _ l r t f =>
      valFields l ++ valFields r ++ t.flatMap opFields ++ f.flatMap opFields
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

private def isExceptType (e : Expr) : Bool :=
  e.consumeMData.getAppFn.constName? == some ``Except

/-- `Except` → mutate；`UInt64` → view；其它用户 structure → init。
`UInt64` 本身也是 structure，必须先判。 -/
def inferKind (env : Environment) (n : Name) : Except String IR.MethodKind := do
  let some info := env.find? n
    | throw s!"extract/unsupported: unknown {n}"
  let ret := peelForalls info.type
  if isExceptType ret then
    return .increment
  if isUInt64Type ret then
    return .get
  if let some structName := ret.getAppFn.constName? then
    if isStructure env structName && structName != ``UInt64 then
      return .init
  throw s!"extract/unsupported: cannot classify {n}"

private def sortNames (ns : Array Name) : Array Name :=
  ns.qsort (·.toString < ·.toString)

/-- 收同一名字空间下 `@[solana_entry]` 的根。须恰好一个 init、至少一个 mutate、至少一个 view。 -/
def extractModule (env : Environment) (ns : Name)
    (fields? : Option (Array String) := none) :
    Except String IR.Program := do
  let tagged := sortNames (Attr.entriesIn env ns)
  if tagged.isEmpty then
    throw "extract/unsupported: no solana_entry"
  let mut inits : Array Name := #[]
  let mut muts : Array Name := #[]
  let mut views : Array Name := #[]
  for n in tagged do
    match Profile.check env n with
    | .reject reason => throw reason
    | .accept => pure ()
    match ← inferKind env n with
    | .init => inits := inits.push n
    | .increment => muts := muts.push n
    | .get => views := views.push n
  if inits.size != 1 then
    throw s!"extract/unsupported: need exactly one init, got {inits.size}"
  if muts.isEmpty then
    throw "extract/unsupported: missing mutating method"
  if views.isEmpty then
    throw "extract/unsupported: missing view method"
  let initName := inits[0]!
  let inferred ← inferFields env initName
  let fields ←
    match fields? with
    | none => pure inferred
    | some fs =>
      if fs == inferred then pure fs
      else throw s!"extract/unsupported: fields {fs} != inferred {inferred}"
  let initM ← extractMethod env .init initName
  let mut methods : Array IR.Method := #[initM]
  let mut seen : Array String := #[initM.ixName]
  for n in muts do
    let m ← extractMethod env .increment n
    if seen.contains m.ixName then
      throw s!"extract/unsupported: duplicate ixName {m.ixName}"
    seen := seen.push m.ixName
    methods := methods.push m
  for n in views do
    let m ← extractMethod env .get n
    if seen.contains m.ixName then
      throw s!"extract/unsupported: duplicate ixName {m.ixName}"
    seen := seen.push m.ixName
    methods := methods.push m
  let program : IR.Program := {
    name := programNameOfInit initName
    fields
    methods
  }
  unless IR.isCounterShape program do
    throw "extract/unsupported: not counter shape"
  checkUsedFields program
  match IR.layoutMarkerHex program with
  | .error reason => throw reason
  | .ok _ => pure ()
  for m in program.methods do
    match IR.discHex m with
    | .error reason => throw reason
    | .ok _ => pure ()
  return program

end SolanaLean.Extract
