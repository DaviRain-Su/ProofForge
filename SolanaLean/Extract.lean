import Lean
import SolanaLean.IR
import SolanaLean.Ops
import SolanaLean.Profile
import SolanaLean.Attr
import SolanaLean.Runtime

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

/-- 无参数构造子的 inductive。构造子按声明顺序编号。 -/
private def enumCtorIndex (env : Environment) (tyName ctor : Name) : Option Nat :=
  match env.find? tyName with
  | some (.inductInfo info) =>
    if info.numParams != 0 || info.numIndices != 0 || info.ctors.isEmpty || info.isRec then
      none
    else
      info.ctors.findIdx? (· == ctor)
  | _ => none

private def isEnumLeaf (env : Environment) (tyName : Name) : Bool :=
  match env.find? tyName with
  | some (.inductInfo info) =>
    info.numParams == 0 && info.numIndices == 0 && !info.ctors.isEmpty && !info.isRec &&
      info.ctors.all fun ctor =>
        match env.find? ctor with
        | some (.ctorInfo c) => c.numFields == 0
        | _ => false
  | _ => false

/-- 两构造子：一个 0 字段、一个 1 个 UInt64。按 Option 双叶展开。 -/
private def isOptionLikeInductive (env : Environment) (tyName : Name) : Bool :=
  match env.find? tyName with
  | some (.inductInfo info) =>
    info.numParams == 0 && info.numIndices == 0 && info.ctors.length == 2 && !info.isRec &&
      Id.run do
        let mut zeros := 0
        let mut ones := 0
        for ctor in info.ctors do
          match env.find? ctor with
          | some (.ctorInfo c) =>
            if c.numFields == 0 then zeros := zeros + 1
            else if c.numFields == 1 then
              match strip c.type with
              | .forallE _ ty _ _ =>
                if ty.consumeMData.getAppFn.constName? == some ``UInt64 then
                  ones := ones + 1
              | _ => pure ()
          | _ => pure ()
        return zeros == 1 && ones == 1
  | _ => false

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

private def looksLikeOptionProj (env : Environment) (n : Name) : Bool :=
  match env.find? n with
  | some info => info.type.getUsedConstantsAsSet.toList.any (· == ``Option)
  | none => false

private def asVal (env : Environment) (fuel : Nat) (e : Expr) : Option Ops.Val :=
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
        if (endsWith e ".findPda" || isConstNamed e ``SolanaLean.Runtime.findPda) &&
            e.getAppArgs.size ≥ 1 then
          match strip e.getAppArgs[e.getAppArgs.size - 1]! with
          | .lit (.strVal s) => if s.isEmpty then none else some (.findPda s)
          | _ => none
        else if (endsWith e ".rentExemption" ||
            isConstNamed e ``SolanaLean.Runtime.rentExemption) &&
            e.getAppArgs.size ≥ 1 then
          match asLit fuel' e.getAppArgs[e.getAppArgs.size - 1]! with
          | some (.lit n) => some (.rentExemption n)
          | _ => none
        else if user && field.contains "." && e.getAppArgs.size ≥ 1 then
          let proj :=
            match field.splitOn "." with
            | [] => field
            | parts => parts.getLast!
          if proj == "mk" || proj == "ok" || proj == "error" ||
              proj.startsWith "_proof" || proj == "rfl" then none
          else if match env.find? n with | some (.ctorInfo _) => true | _ => false then none
          else
            -- 整个 Vector 投影本身不是叶；下标再展开成 `name_i`。
            let skipVector :=
              match env.find? n with
              | some info =>
                info.type.getUsedConstantsAsSet.toList.any (· == ``Vector)
              | none => false
            if skipVector then none
            else
              match asVal env fuel' e.getAppArgs[e.getAppArgs.size - 1]! with
              | some b =>
                if looksLikeOptionProj env n then some (.field b s!"{proj}_tag")
                else some (.field b proj)
              | none =>
                match e.getAppArgs[e.getAppArgs.size - 1]! with
                | .bvar i =>
                  if looksLikeOptionProj env n then some (.field (.arg i) s!"{proj}_tag")
                  else some (.field (.arg i) proj)
                | _ => none
        else if (isConstNamed e ``UInt8.toUInt64 || isConstNamed e ``UInt64.toUInt8) &&
            e.getAppArgs.size ≥ 1 then
          asVal env fuel' e.getAppArgs[e.getAppArgs.size - 1]!
        else if (isConstNamed e ``Option.isSome || endsWith e ".isSome") && e.getAppArgs.size ≥ 1 then
          match asVal env fuel' e.getAppArgs[e.getAppArgs.size - 1]! with
          | some (.field b n) =>
            if n.endsWith "_tag" then some (.field b n)
            else some (.field b s!"{n}_tag")
          | some b => some (.field b s!"slot_tag")
          | none => none
        else if endsWith e ".u64Max" then
          some (.lit (~~~(0 : UInt64)))
        else if endsWith e ".clockSlot" || isConstNamed e ``SolanaLean.Runtime.clockSlot then
          some .clockSlot
        else if endsWith e ".signerKey0" || isConstNamed e ``SolanaLean.Runtime.signerKey0 then
          some .signerKey0
        else if endsWith e ".accLamports0" || isConstNamed e ``SolanaLean.Runtime.accLamports0 then
          some .accLamports0
        else if endsWith e ".accOwner0" || isConstNamed e ``SolanaLean.Runtime.accOwner0 then
          some .accOwner0
        else if endsWith e ".accDataLen0" || isConstNamed e ``SolanaLean.Runtime.accDataLen0 then
          some .accDataLen0
        else if endsWith e ".accN" || isConstNamed e ``SolanaLean.Runtime.accN then
          some .accN
        else if endsWith e ".isSigner0" || isConstNamed e ``SolanaLean.Runtime.isSigner0 then
          some .isSigner0
        else if endsWith e ".isWritable0" || isConstNamed e ``SolanaLean.Runtime.isWritable0 then
          some .isWritable0
        else if endsWith e ".isExecutable0" || isConstNamed e ``SolanaLean.Runtime.isExecutable0 then
          some .isExecutable0
        else if (endsWith e ".systemTransfer" ||
            isConstNamed e ``SolanaLean.Runtime.systemTransfer) && e.getAppArgs.size ≥ 1 then
          asVal env fuel' e.getAppArgs[e.getAppArgs.size - 1]!
        else if endsWith e ".invokeAcc1" || isConstNamed e ``SolanaLean.Runtime.invokeAcc1 ||
            endsWith e ".invoke" || isConstNamed e ``SolanaLean.Runtime.invoke ||
            endsWith e ".invokeSigned" || isConstNamed e ``SolanaLean.Runtime.invokeSigned then
          some (.lit 0)
        else if isConstNamed e ``Bool.true || endsWith e ".true" then
          some (.lit 1)
        else if isConstNamed e ``Bool.false || endsWith e ".false" then
          some (.lit 0)
        else if user && e.getAppArgs.isEmpty then
          match e.getAppFn.constName? with
          | some ctor =>
            match env.find? ctor with
            | some (.ctorInfo c) =>
              match enumCtorIndex env c.induct ctor with
              | some i => some (.lit (UInt64.ofNat i))
              | none => none
            | _ => none
          | none => none
        else if isConstNamed e ``Option.none || endsWith e ".none" then
          some (.lit 0)
        else if (isConstNamed e ``Option.some || endsWith e ".some") && e.getAppArgs.size ≥ 1 then
          asVal env fuel' e.getAppArgs[e.getAppArgs.size - 1]!
        else if (isConstNamed e ``GetElem.getElem || isConstNamed e ``Vector.get ||
            endsWith e ".getElem" || endsWith e ".get") && e.getAppArgs.size ≥ 2 then
          let args := e.getAppArgs
          -- 最后一个字面量才是下标；前面的 `OfNat n` 是 Vector 长度。
          let idx? :=
            match (args.filterMap (asLit fuel')).back? with
            | some (.lit n) => some n.toNat
            | _ => none
          match idx? with
          | none => none
          | some i =>
            let rec findState (fuel : Nat) (e : Expr) : Option Nat :=
              match fuel with
              | 0 => none
              | fuel' + 1 =>
                match strip e with
                | .bvar j => some j
                | e => e.getAppArgs.findSome? (findState fuel')
            match findState fuel' e, args.findSome? (asVal env fuel') with
            | some j, some (.field _ n) =>
              let suf := s!"_{i}"
              let base := if n.endsWith suf then n.dropEnd suf.length |>.copy else n
              some (.field (.arg j) s!"{base}_{i}")
            | some j, _ =>
              -- 投影被跳过时，从 GetElem 第一个用户结构参数收字段名。
              let rec fieldNameOf (fuel : Nat) (e : Expr) : Option String :=
                match fuel with
                | 0 => none
                | fuel' + 1 =>
                  match e.getAppFn.constName? with
                  | some n =>
                    let s := n.toString
                    let last := IR.lastName s
                    let user := s.startsWith "Examples." || s.startsWith "Tests."
                    if !user || last == "mk" || last == "getElem" || last.startsWith "_proof" then
                      e.getAppArgs.findSome? (fieldNameOf fuel')
                    else some last
                  | none => e.getAppArgs.findSome? (fieldNameOf fuel')
              match fieldNameOf 8 e with
              | some n => some (.field (.arg j) s!"{n}_{i}")
              | none => none
            | _, _ => none
        else none
      else none

private def val (env : Environment) (e : Expr) : Option Ops.Val :=
  asVal env 16 e

private def asSubFromMax (env : Environment) (e : Expr) : Option Ops.Val :=
  let e := strip e
  if isConstNamed e ``HSub.hSub then
    let args := e.getAppArgs
    if args.size ≥ 2 && endsWith (strip args[args.size - 2]!) ".u64Max" then
      val env args[args.size - 1]!
    else none
  else none

/-- `x ≤ u64Max - y`  →  checked add x y。单独的 `x ≤ u64Max` 不是 add。 -/
private def asCheckedAddGuard (env : Environment) (e : Expr) : Option (Ops.Val × Ops.Val) :=
  let e := strip e
  if isConstNamed e ``LE.le then
    let args := e.getAppArgs
    if args.size ≥ 2 then
      match val env args[args.size - 2]!, asSubFromMax env args[args.size - 1]! with
      | some lhs, some rhs => some (lhs, rhs)
      | _, _ => none
    else none
  else none

private def asDivFromMax (env : Environment) (e : Expr) : Option Ops.Val :=
  let e := strip e
  if isConstNamed e ``HDiv.hDiv then
    let args := e.getAppArgs
    if args.size ≥ 2 && endsWith (strip args[args.size - 2]!) ".u64Max" then
      val env args[args.size - 1]!
    else none
  else none

/-- `x ≤ u64Max / y`  →  checked mul x y -/
private def asCheckedMulGuard (env : Environment) (e : Expr) : Option (Ops.Val × Ops.Val) :=
  let e := strip e
  if isConstNamed e ``LE.le then
    let args := e.getAppArgs
    if args.size ≥ 2 then
      match val env args[args.size - 2]!, asDivFromMax env args[args.size - 1]! with
      | some lhs, some rhs => some (lhs, rhs)
      | _, _ => none
    else none
  else none

private def binArgs (e : Expr) : Option (Expr × Expr) :=
  let args := e.getAppArgs
  if args.size ≥ 2 then some (args[args.size - 2]!, args[args.size - 1]!) else none

private def asCmpCore (env : Environment) (e : Expr) : Option (Ops.Cmp × Ops.Val × Ops.Val) :=
  let e := strip e
  if isConstNamed e ``Eq || isConstNamed e ``BEq.beq then
    match binArgs e with
    | some (l, r) =>
      match val env l, val env r with
      | some lv, some rv => some (.eq, lv, rv)
      | _, _ => none
    | none => none
  else if isConstNamed e ``Ne then
    match binArgs e with
    | some (l, r) =>
      match val env l, val env r with
      | some lv, some rv => some (.ne, lv, rv)
      | _, _ => none
    | none => none
  else if isConstNamed e ``LT.lt then
    match binArgs e with
    | some (l, r) =>
      match val env l, val env r with
      | some lv, some rv => some (.lt, lv, rv)
      | _, _ => none
    | none => none
  else if isConstNamed e ``LE.le then
    match binArgs e with
    | some (l, r) =>
      match val env l, val env r with
      | some lv, some rv => some (.le, lv, rv)
      | _, _ => none
    | none => none
  else if isConstNamed e ``GT.gt then
    match binArgs e with
    | some (l, r) =>
      match val env l, val env r with
      | some lv, some rv => some (.gt, lv, rv)
      | _, _ => none
    | none => none
  else if isConstNamed e ``GE.ge then
    match binArgs e with
    | some (l, r) =>
      match val env l, val env r with
      | some lv, some rv => some (.ge, lv, rv)
      | _, _ => none
    | none => none
  else none

private def asCmp (env : Environment) (e : Expr) : Option (Ops.Cmp × Ops.Val × Ops.Val) :=
  let e := strip e
  if isConstNamed e ``Not then
    let args := e.getAppArgs
    if args.size ≥ 1 then
      match asCmpCore env args[args.size - 1]! with
      | some (.eq, l, r) => some (.ne, l, r)
      | some (.ne, l, r) => some (.eq, l, r)
      | _ => none
    else none
  else
    match asCmpCore env e with
    | some t => some t
    | none =>
      if isConstNamed e ``Eq then
        match binArgs e with
        | some (l, r) =>
          let l := strip l
          let r := strip r
          let trueR := isConstNamed r ``Bool.true || endsWith r ".true"
          let noneR := isConstNamed r ``Option.none || endsWith r ".none"
          let noneL := isConstNamed l ``Option.none || endsWith l ".none"
          if trueR && (isConstNamed l ``Option.isSome || endsWith l ".isSome") then
            match val env l with
            | some (.field b n) =>
              let tag := if n.endsWith "_tag" then n else s!"{n}_tag"
              some (.ne, .field b tag, .lit 0)
            | some b => some (.ne, .field b "slot_tag", .lit 0)
            | none => some (.ne, .field (.arg 0) "slot_tag", .lit 0)
          else if noneR then
            match val env l with
            | some lv => some (.eq, lv, .lit 0)
            | none => none
          else if noneL then
            match val env r with
            | some rv => some (.eq, rv, .lit 0)
            | none => none
          else none
        | none => none
      else if isConstNamed e ``Option.isSome || endsWith e ".isSome" then
        let args := e.getAppArgs
        if args.size ≥ 1 then
          match val env args[args.size - 1]! with
          | some (.field b n) =>
            let tag := if n.endsWith "_tag" then n else s!"{n}_tag"
            some (.ne, .field b tag, .lit 0)
          | some b => some (.ne, .field b "slot_tag", .lit 0)
          | none => none
        else none
      else none

/-- `x ≥ y` / `y ≤ x`  →  checked sub x y。`x ≤ lit` 是上界（255 / u64Max），不是 sub。 -/
private def asCheckedSubGuard (env : Environment) (e : Expr) : Option (Ops.Val × Ops.Val) :=
  match asCmp env e with
  | some (.le, _, .lit _) => none
  | some (.le, rhs, lhs) => some (lhs, rhs)
  | some (.ge, lhs, rhs) => some (lhs, rhs)
  | _ => none

/-- `den ≠ 0` 才是除法守卫。两边都是字面量的 `0 ≠ 1` 不算。 -/
private def asNeZero (env : Environment) (e : Expr) : Option Ops.Val :=
  match asCmp env e with
  | some (.ne, .lit _, .lit _) => none
  | some (.ne, v, .lit 0) => some v
  | some (.ne, .lit 0, v) => some v
  | _ => none

private def asEqZero (env : Environment) (e : Expr) : Option Ops.Val :=
  match asCmp env e with
  | some (.eq, v, .lit 0) => some v
  | some (.eq, .lit 0, v) => some v
  | _ => none

/-- 多字段 `State.mk a b …`：init 用第一个显式参数；checked 更新用最后一个。 -/
private def asStateMk (env : Environment) (e : Expr) (preferLast := false) : Option Ops.Val :=
  let e := strip e
  if endsWith e ".State.mk" || endsWith e ".mk" then
    let args := e.getAppArgs
    if args.size = 0 then none
    else if preferLast then val env args[args.size - 1]!
    else
      match args.findSome? (val env) with
      | some v => some v
      | none => val env args[args.size - 1]!
  else none

private def asOptionPayload (env : Environment) (e : Expr) : Option Ops.Val :=
  let e := strip e
  if isConstNamed e ``Option.none || endsWith e ".none" then
    some (.lit 0)
  else if isConstNamed e ``Option.some || endsWith e ".some" then
    let args := e.getAppArgs
    if args.size ≥ 1 then val env args[args.size - 1]! else none
  else
    match e.getAppFn.constName? with
    | some ctor =>
      match env.find? ctor with
      | some (.ctorInfo c) =>
        if isOptionLikeInductive env c.induct || isEnumLeaf env c.induct then
          match enumCtorIndex env c.induct ctor with
          | some 0 => some (.lit 0)
          | some _ =>
            if c.numFields == 0 then some (.lit 1)
            else if e.getAppArgs.size ≥ 1 then val env e.getAppArgs[e.getAppArgs.size - 1]!
            else none
          | none => none
        else none
      | _ => none
    | none => none

/-- `#v[a, b, …]` = `Vector.mk (List.toArray (a :: b :: []))`。 -/
private def collectListVals (env : Environment) (fuel : Nat) (e : Expr) : Array Ops.Val :=
  match fuel with
  | 0 => #[]
  | fuel' + 1 =>
    let e := strip e
    if isConstNamed e ``List.nil || endsWith e ".nil" then
      #[]
    else if isConstNamed e ``List.cons || endsWith e ".cons" then
      let args := e.getAppArgs
      if args.size ≥ 2 then
        let head := args[args.size - 2]!
        let tail := args[args.size - 1]!
        match val env head with
        | some v => #[v] ++ collectListVals env fuel' tail
        | none => collectListVals env fuel' tail
      else #[]
    else if isConstNamed e ``List.toArray || endsWith e ".toArray" then
      let args := e.getAppArgs
      if args.size ≥ 1 then collectListVals env fuel' args[args.size - 1]! else #[]
    else
      match val env e with
      | some v => #[v]
      | none => #[]

private def findListVals (env : Environment) (fuel : Nat) (e : Expr) : Option (Array Ops.Val) :=
  match fuel with
  | 0 => none
  | fuel' + 1 =>
    let e := strip e
    if isConstNamed e ``List.cons || endsWith e ".cons" then
      some (collectListVals env 16 e)
    else
      e.getAppArgs.findSome? (findListVals env fuel')

private def asVectorLits (env : Environment) (e : Expr) : Option (Array Ops.Val) :=
  let e := strip e
  if isConstNamed e ``Vector.mk || endsWith e "Vector.mk" then
    match findListVals env 16 e with
    | some vs => if vs.isEmpty then none else some vs
    | none => none
  else none

/-- `xs.set i v`：只抽出被改的那一叶。 -/
private def asVectorSet (env : Environment) (e : Expr) : Option Ops.Val :=
  let e := strip e
  if isConstNamed e ``Vector.set || endsWith e ".set" then
    let args := e.getAppArgs
    let idx? :=
      match (args.filterMap (asLit 8)).back? with
      | some (.lit n) => some n.toNat
      | _ => none
    -- `Vector.set xs i v h`：值在字面量下标之后。
    let payload :=
      Id.run do
        let mut seenIdx := false
        for a in args do
          match asLit 8 a, val env a with
          | some (.lit _), _ =>
            seenIdx := true
          | none, some v =>
            if seenIdx then return some v
          | _, _ => pure ()
        return none
    let rec baseName (fuel : Nat) (e : Expr) : Option String :=
      match fuel with
      | 0 => none
      | fuel' + 1 =>
        match e.getAppFn.constName? with
        | some n =>
          let s := n.toString
          let last := IR.lastName s
          let user := s.startsWith "Examples." || s.startsWith "Tests."
          if !user || last == "set" || last == "mk" || last.startsWith "_proof" then
            e.getAppArgs.findSome? (baseName fuel')
          else some last
        | none => e.getAppArgs.findSome? (baseName fuel')
    match idx?, payload, baseName 8 e with
    | some i, some v, some n => some (.field v s!"{n}_{i}")
    | some i, some v, none => some (.field v s!"cells_{i}")
    | _, _, _ => none
  else none

/-- `State.mk` 每个字段一个值。`Option` 展开成 tag + payload；`Vector` 展开成各叶。 -/
private def asStateFields (env : Environment) (e : Expr) : Option (Array Ops.Val) :=
  let e := strip e
  if endsWith e ".State.mk" || endsWith e ".mk" then
    Id.run do
      let mut acc : Array Ops.Val := #[]
      for a in e.getAppArgs do
        match asOptionPayload env a with
        | some (.lit 0) =>
          acc := acc.push (.lit 0) |>.push (.lit 0)
        | some v =>
          acc := acc.push (.lit 1) |>.push v
        | none =>
          if endsWith a "._proof_1" || endsWith a "._proof_2" || endsWith a ".rfl" then
            pure ()
          else
            match asVectorLits env a with
            | some vs => acc := acc ++ vs
            | none =>
              match asVectorSet env a with
              | some v => acc := acc.push v
              | none =>
                match val env a with
                | some v => acc := acc.push v
                | none => pure ()
      if acc.isEmpty then none else some acc
  else none

private def asOkState (env : Environment) (e : Expr) : Option Ops.Val :=
  let e := peelLets (strip e)
  if isConstNamed e ``Except.ok then
    let args := e.getAppArgs
    if args.size ≥ 1 then
      let pair := strip args[args.size - 1]!
      if isConstNamed pair ``Prod.mk then
        let pargs := pair.getAppArgs
        if pargs.size ≥ 2 then
          let st := pargs[pargs.size - 2]!
          match asOptionPayload env st with
          | some v => some v
          | none =>
            match val env st with
            | some (.clockSlot) => some .clockSlot
            | some (.signerKey0) => some .signerKey0
            | some (.accLamports0) => some .accLamports0
            | some (.accOwner0) => some .accOwner0
            | some (.accDataLen0) => some .accDataLen0
            | some (.accN) => some .accN
            | some (.isSigner0) => some .isSigner0
            | some (.isWritable0) => some .isWritable0
            | some (.isExecutable0) => some .isExecutable0
            | some (.findPda s) => some (.findPda s)
            | some (.rentExemption n) => some (.rentExemption n)
            | _ =>
              match asVectorSet env (strip st) <|>
                  (strip st).getAppArgs.findSome? (asVectorSet env) with
              | some v => some v
              | none =>
                match asStateMk env st true with
                | some v => some v
                | none =>
                  let args := (strip st).getAppArgs
                  args.findSome? (asOptionPayload env) <|>
                    args.findSome? (val env) <|>
                    asStateMk env st true
        else none
      else asStateMk env pair true
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

/-- 每个槽一条 `returnState`。第二槽起全是 `lit 0` 时仍压成一条（旧 init）。 -/
private def returnStatesOf (vs : Array Ops.Val) : Array Ops.Op :=
  if vs.size ≤ 1 then
    vs.map Ops.Op.returnState
  else if vs[1:].all (fun | .lit 0 => true | _ => false) then
    #[.returnState vs[0]!]
  else
    vs.map Ops.Op.returnState

private def isRuntimeName (n : Name) (suf : String) : Bool :=
  n == (`SolanaLean.Runtime).append suf.toName || n.toString.endsWith s!".{suf}"

private def mentionsRuntime (e : Expr) (suf : String) : Bool :=
  e.getUsedConstantsAsSet.toList.any (isRuntimeName · suf)

private def natOfVal : Ops.Val → Option Nat
  | .lit n => some n.toNat
  | _ => none

private def asBoolLit (e : Expr) : Option Bool :=
  if isConstNamed e ``Bool.true || endsWith e ".true" then some true
  else if isConstNamed e ``Bool.false || endsWith e ".false" then some false
  else none

/-- `CpiMeta.mk acc signer writable` 或具名字段。 -/
private def asCpiMeta (env : Environment) (e : Expr) : Option Ops.CpiMeta :=
  let e := strip e
  if isConstNamed e ``SolanaLean.Runtime.CpiMeta.mk || endsWith e ".mk" then
    let args := e.getAppArgs
    if args.size ≥ 3 then
      match val env args[args.size - 3]!, asBoolLit args[args.size - 2]!,
          asBoolLit args[args.size - 1]! with
      | some accV, some signer, some writable =>
        match natOfVal accV with
        | some acc => some { acc, signer, writable }
        | none => none
      | _, _, _ => none
    else none
  else none

private def asCpiWord (env : Environment) (e : Expr) : Option Ops.CpiWord :=
  let e := strip e
  if isConstNamed e ``SolanaLean.Runtime.CpiWord.u8le || endsWith e ".u8le" then
    if e.getAppArgs.size ≥ 1 then
      match val env e.getAppArgs[e.getAppArgs.size - 1]! >>= natOfVal with
      | some n => some (.u8le (UInt64.ofNat n))
      | none => none
    else none
  else if isConstNamed e ``SolanaLean.Runtime.CpiWord.u32le || endsWith e ".u32le" then
    if e.getAppArgs.size ≥ 1 then
      match val env e.getAppArgs[e.getAppArgs.size - 1]! >>= natOfVal with
      | some n => some (.u32le (UInt64.ofNat n))
      | none => none
    else none
  else if isConstNamed e ``SolanaLean.Runtime.CpiWord.u64le || endsWith e ".u64le" then
    if e.getAppArgs.size ≥ 1 then
      match val env e.getAppArgs[e.getAppArgs.size - 1]! with
      | some v => some (.u64le v)
      | none => none
    else none
  else if isConstNamed e ``SolanaLean.Runtime.CpiWord.ascii || endsWith e ".ascii" then
    if e.getAppArgs.size ≥ 1 then
      match e.getAppArgs[e.getAppArgs.size - 1]! with
      | .lit (.strVal s) => some (.ascii s)
      | _ => none
    else none
  else if isConstNamed e ``SolanaLean.Runtime.CpiWord.programId || endsWith e ".programId" then
    some .programId
  else none

/-- `#[a, b, …]` 展开成 `Array.mk [a, b, …]` / `List.cons`。 -/
private def asArrayElems (e : Expr) : Option (Array Expr) :=
  let rec fromList (fuel : Nat) (e : Expr) (acc : Array Expr) : Option (Array Expr) :=
    match fuel with
    | 0 => none
    | fuel' + 1 =>
      let e := strip e
      if isConstNamed e ``List.nil then some acc
      else if isConstNamed e ``List.cons && e.getAppArgs.size ≥ 2 then
        let args := e.getAppArgs
        fromList fuel' args[args.size - 1]! (acc.push args[args.size - 2]!)
      else none
  let e := strip e
  if isConstNamed e ``Array.mk && e.getAppArgs.size ≥ 1 then
    fromList 16 e.getAppArgs[e.getAppArgs.size - 1]! #[]
  else if isConstNamed e ``List.toArray && e.getAppArgs.size ≥ 1 then
    fromList 16 e.getAppArgs[e.getAppArgs.size - 1]! #[]
  else if isConstNamed e ``Array.empty || endsWith e ".empty" then
    some #[]
  else none

private def decodeMetasData (env : Environment) (metaE dataE : Expr) :
    Option (Array Ops.CpiMeta × Array Ops.CpiWord) :=
  match asArrayElems metaE, asArrayElems dataE with
  | some metaEs, some dataEs =>
    Id.run do
      let mut metas : Array Ops.CpiMeta := #[]
      for me in metaEs do
        match asCpiMeta env me with
        | none => return none
        | some m => metas := metas.push m
      let mut data : Array Ops.CpiWord := #[]
      for de in dataEs do
        match asCpiWord env de with
        | none => return none
        | some w => data := data.push w
      some (metas, data)
  | _, _ => none

private def asAsciiLit (e : Expr) : Option String :=
  match strip e with
  | .lit (.strVal s) => if s.isEmpty then none else some s
  | _ => none

/-- 抽出结果：program / metas / data / 可选 (seed, bump)。 -/
private def decodeInvokeArgs (env : Environment) (e : Expr) :
    Option (Nat × Array Ops.CpiMeta × Array Ops.CpiWord × Option String × Option Ops.Val) :=
  let e := strip e
  if isConstNamed e ``SolanaLean.Runtime.invokeSigned || endsWith e ".invokeSigned" then
    let args := e.getAppArgs
    if args.size < 5 then none
    else
      match val env args[args.size - 5]!,
          decodeMetasData env args[args.size - 4]! args[args.size - 3]!,
          asAsciiLit args[args.size - 2]!,
          val env args[args.size - 1]! with
      | some progV, some (metas, data), some seed, some bump =>
        match natOfVal progV with
        | some prog => some (prog, metas, data, some seed, some bump)
        | none => none
      | _, _, _, _ => none
  else if isConstNamed e ``SolanaLean.Runtime.invoke || endsWith e ".invoke" then
    let args := e.getAppArgs
    if args.size < 3 then none
    else
      match val env args[args.size - 3]!,
          decodeMetasData env args[args.size - 2]! args[args.size - 1]! with
      | some progV, some (metas, data) =>
        match natOfVal progV with
        | some prog => some (prog, metas, data, none, none)
        | none => none
      | _, _ => none
  else none

/-- 体里任意深度的编译期 `invoke`。包装会 unfold 成这条。 -/
private def findInvoke (env : Environment) (fuel : Nat) (e : Expr) :
    Option (Nat × Array Ops.CpiMeta × Array Ops.CpiWord × Option String × Option Ops.Val) :=
  let rec go (fuel : Nat) (e : Expr) :
      Option (Nat × Array Ops.CpiMeta × Array Ops.CpiWord × Option String × Option Ops.Val) :=
    match fuel with
    | 0 => none
    | fuel' + 1 =>
      let e := e.consumeMData
      match decodeInvokeArgs env e with
      | some inv => some inv
      | none =>
        -- 非 irreducible 的 Runtime 包装展开成 invoke。
        let unfolded :=
          match e.getAppFn.constName? with
          | none => none
          | some n =>
            if n.getRoot != `SolanaLean then none
            else
              match env.find? n with
              | some (.defnInfo info) =>
                -- 空参包装（invokeAcc1）直接取体；有参包装 β 展开。
                if e.getAppArgs.isEmpty then some info.value
                else some (info.value.beta e.getAppArgs)
              | _ => none
        match unfolded with
        | some u => go fuel' u
        | none =>
          match e with
          | .letE _ _ value body _ => go fuel' value <|> go fuel' body
          | .lam _ _ body _ => go fuel' body
          | .app f a => go fuel' f <|> go fuel' a
          | _ => none
  if mentionsRuntime e "invoke" || mentionsRuntime e "invokeSigned" ||
      mentionsRuntime e "systemTransfer" || mentionsRuntime e "invokeAcc1" ||
      mentionsRuntime e "systemCreate" ||
      mentionsRuntime e "tokenTransferChecked" ||
      mentionsRuntime e "ataCreateIdempotent" then
    go fuel e
  else none

private def invokeOps
    (inv : Nat × Array Ops.CpiMeta × Array Ops.CpiWord × Option String × Option Ops.Val)
    (ret : Ops.Val) : Array Ops.Op :=
  let (prog, metas, data, seed, bump) := inv
  #[.invoke prog metas data seed bump, .returnU64 ret]

/-- `.ok (state, ret)` 的第二元。找不到就 none。 -/
private def findOkRet (env : Environment) (e : Expr) : Option Ops.Val :=
  let rec go (fuel : Nat) (e : Expr) : Option Ops.Val :=
    match fuel with
    | 0 => none
    | fuel' + 1 =>
      let e := strip e
      if isConstNamed e ``Except.ok && e.getAppArgs.size ≥ 1 then
        let pair := strip e.getAppArgs[e.getAppArgs.size - 1]!
        if isConstNamed pair ``Prod.mk && pair.getAppArgs.size ≥ 2 then
          val env pair.getAppArgs[pair.getAppArgs.size - 1]!
        else none
      else
        match e with
        | .letE _ _ _ body _ => go fuel' body
        | .lam _ _ body _ => go fuel' body
        | .app f a => go fuel' f <|> go fuel' a
        | _ => none
  go 16 e

private def invokeRet
    (_env : Environment) (_e : Expr)
    (inv : Nat × Array Ops.CpiMeta × Array Ops.CpiWord × Option String × Option Ops.Val) :
    Ops.Val :=
  match inv with
  | (2, _, #[.u32le 2, .u64le amount], none, none) => amount
  | (2, _, #[.u32le 0, .u64le amount, .u64le _, .programId], none, none) => amount
  | (4, _, #[.u8le 12, .u64le amount, .u8le _], none, none) => amount
  | (6, _, #[.u8le 1], none, none) => .lit 0
  | _ => .lit 0

private def decodePlain (env : Environment) (e : Expr) : Except String (Array Ops.Op) :=
  -- 必须在 peelLets 之前找 invoke：剥掉 `have sent := …` 后调用就没了。
  if let some inv := findInvoke env 16 e then
    .ok (invokeOps inv (invokeRet env e inv))
  else
  let e := peelLets (strip e)
  if let some v := asOkState env e then
    .ok #[.okState v]
  else if let some vs := asStateFields env e then
    .ok (returnStatesOf vs)
  else if let some v := asStateMk env e then
    .ok #[.returnState v]
  else if let some v := val env e then
    match v with
    | .field _ _ => .ok #[.returnU64 v]
    | .arg _ => .ok #[.returnState v]
    | .lit _ => .ok #[.returnU64 v]
    | .clockSlot | .signerKey0 | .accLamports0 | .accOwner0 | .accDataLen0
    | .accN | .isSigner0 | .isWritable0 | .isExecutable0 | .findPda _
    | .rentExemption _ => .ok #[.returnU64 v]
  else
    .error "extract/unsupported: body"

private def findBy (args : Array Expr) (p : Expr → Bool) : Option Expr :=
  args.find? p

private def lastNamedBin (env : Environment) (want : Name) (e : Expr) : Option (Ops.Val × Ops.Val) :=
  let rec go (fuel : Nat) (e : Expr) : Option (Ops.Val × Ops.Val) :=
    match fuel with
    | 0 => none
    | fuel' + 1 =>
      let e := strip e
      if isConstNamed e want then
        match binArgs e with
        | some (l, r) =>
          match val env l, val env r with
          | some lv, some rv => some (lv, rv)
          | _, _ => none
        | none => none
      else
        e.getAppArgs.findSome? (go fuel')
  go 8 e

private def decodeExpr (env : Environment) (fuel : Nat) (e : Expr) : Except String (Array Ops.Op) :=
  match fuel with
  | 0 => .error "extract/unsupported: ite depth"
  | fuel' + 1 => Id.run do
    if let some inv := findInvoke env 16 e then
      return .ok (invokeOps inv (invokeRet env e inv))
    let e := strip e
    if isConstNamed e ``ite && e.getAppArgs.size ≥ 5 then
      let args := e.getAppArgs
      let t := peelLets args[args.size - 2]!
      let f := peelLets args[args.size - 1]!
      if isErrorOverflow f then
        if let some condE := findBy args (fun a => (asCmp env a).isSome && (asCheckedAddGuard env a).isNone && (asCheckedMulGuard env a).isNone && (asCheckedSubGuard env a).isNone && (asNeZero env a).isNone) then
          match asCmp env condE, findInvoke env 8 t, asOkState env t with
          | some (cmp, lv, rv), some inv, _ =>
            return .ok #[.ite cmp lv rv (invokeOps inv (invokeRet env t inv)) #[.errorOverflow]]
          | some (cmp, lv, rv), none, some v =>
            return .ok #[.ite cmp lv rv #[.okState v] #[.errorOverflow]]
          | _, _, _ => return .error "extract/unsupported: ite then"
        else if let some condE := findBy args (fun a => (asCheckedAddGuard env a).isSome) then
          match asCheckedAddGuard env condE, asOkState env t with
          | some (lhs, rhs), some v =>
            return .ok #[.checkedAddU64 lhs rhs, .okState v, .errorOverflow]
          | _, _ => return .error "extract/unsupported: ite then"
        else if let some condE := findBy args (fun a => (asCheckedMulGuard env a).isSome) then
          match asCheckedMulGuard env condE, asOkState env t with
          | some (lhs, rhs), some v =>
            return .ok #[.checkedMulU64 lhs rhs, .okState v, .errorOverflow]
          | _, _ => return .error "extract/unsupported: ite then"
        else if let some condE := findBy args (fun a => (asCheckedSubGuard env a).isSome) then
          match asCheckedSubGuard env condE, asOkState env t with
          | some (lhs, rhs), some v =>
            return .ok #[.checkedSubU64 lhs rhs, .okState v, .errorOverflow]
          | _, _ => return .error "extract/unsupported: ite then"
        else if let some condE := findBy args (fun a => (asNeZero env a).isSome) then
          match asNeZero env condE with
          | none => return .error "extract/unsupported: ite then"
          | some den =>
            let v := (asOkState env t).getD (.arg 0)
            let fallback := (.field (.arg 1) "value", den)
            if (lastNamedBin env ``HMod.hMod t).isSome then
              let (lhs, rhs) := (lastNamedBin env ``HMod.hMod t).getD fallback
              return .ok #[.checkedModU64 lhs (if rhs == den then rhs else den), .okState v, .errorOverflow]
            else if (lastNamedBin env ``UInt64.mod t).isSome then
              let (lhs, rhs) := (lastNamedBin env ``UInt64.mod t).getD fallback
              return .ok #[.checkedModU64 lhs (if rhs == den then rhs else den), .okState v, .errorOverflow]
            else
              let (lhs, rhs) := (lastNamedBin env ``HDiv.hDiv t).getD fallback
              return .ok #[.checkedDivU64 lhs (if rhs == den then rhs else den), .okState v, .errorOverflow]
        else
          return .error "extract/unsupported: ite cond"
      else
        let some condE := findBy args (fun a => (asCmp env a).isSome)
          | return .error "extract/unsupported: ite cond"
        let some (cmp, lv, rv) := asCmp env condE
          | return .error "extract/unsupported: ite cond"
        match decodeExpr env fuel' t, decodeExpr env fuel' f with
        | .ok thn, .ok els => return .ok #[.ite cmp lv rv thn els]
        | .error r, _ => return .error r
        | _, .error r => return .error r
    else if let some inv := decodeInvokeArgs env e <|> findInvoke env 8 e then
      return .ok (invokeOps inv (invokeRet env e inv))
    else if endsWith e ".match_1" && e.getAppArgs.size ≥ 3 then
      -- `match opt with | none => a | some n => b` → ite (eq tag 0) a b。
      let args := e.getAppArgs
      let disc := args[args.size - 3]!
      let noneE := peelLets args[args.size - 2]!
      let someE := peelLets args[args.size - 1]!
      let tag :=
        match val env disc with
        | some (.field b n) =>
          if n.endsWith "_tag" then .field b n else .field b s!"{n}_tag"
        | some b => .field b "slot_tag"
        | none => .field (.arg 0) "slot_tag"
      let payload :=
        match tag with
        | .field b n =>
          let base := if n.endsWith "_tag" then n.dropEnd 4 |>.copy else n
          .field b s!"{base}_p0"
        | _ => .field (.arg 0) "slot_p0"
      let rec peelMatcher (fuel : Nat) (e : Expr) : Expr :=
        match fuel with
        | 0 => e
        | fuel' + 1 =>
          match strip e with
          | .lam _ _ body _ => peelMatcher fuel' body
          | e => e
      let noneBody := peelMatcher 8 noneE
      let someBody := peelMatcher 8 someE
      match decodeExpr env fuel' noneBody with
      | .error r => return .error r
      | .ok noneOps =>
        let someOps :=
          match strip someBody with
          | .bvar _ => #[.returnU64 payload]
          | _ =>
            match decodeExpr env fuel' someBody with
            | .ok ops =>
              match ops with
              | #[.returnU64 (.arg _)] => #[.returnU64 payload]
              | #[.returnState (.arg _)] => #[.returnU64 payload]
              | _ => ops
            | .error _ => #[.returnU64 payload]
        return .ok #[.ite .eq tag (.lit 0) noneOps someOps]
    else
      return decodePlain env e

def decodeBody (env : Environment) (e : Expr) : Except String (Array Ops.Op) :=
  let (_, body) := peelLams e
  decodeExpr env 16 body

private def writesOptionLeaf (fuel : Nat) (ops : Array Ops.Op) : Bool :=
  match fuel with
  | 0 => false
  | fuel' + 1 =>
    ops.any fun
      | .okState (.field _ n) => n.endsWith "_tag" || n.endsWith "_p0"
      | .okState (.lit _) => true
      | .okState (.arg _) => true
      | .ite _ _ _ t f => writesOptionLeaf fuel' t || writesOptionLeaf fuel' f
      | _ => false

private def hasIte (ops : Array Ops.Op) : Bool :=
  ops.any fun | .ite .. => true | _ => false

/-- 可变入口必须有 checked 算术、Option 双叶，或比较 ite（窄宽上界）。 -/
def decodeMutating (env : Environment) (e : Expr) : Except String (Array Ops.Op) := do
  let ops ← decodeBody env e
  if Ops.hasCheckedArith ops || writesOptionLeaf 8 ops || hasIte ops ||
      Ops.hasInvoke ops then
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
    | .increment => decodeMutating env e
    | _ => decodeBody env e
  let lean := IR.lastName n.toString
  let (nLams, _) := peelLams e
  let ops1 :=
    if lean == "modulo" then
      ops0.map fun
        | .checkedDivU64 l r => .checkedModU64 l r
        | op => op
    else ops0
  -- init 的 λ 从外到内编号；elaborated bvar 从内到外。翻过来对齐 ix 参数。
  let rec flipVal (fuel : Nat) (v : Ops.Val) : Ops.Val :=
    match fuel with
    | 0 => v
    | fuel' + 1 =>
      match v with
      | .arg i => if i < nLams then .arg (nLams - 1 - i) else v
      | .field b n => .field (flipVal fuel' b) n
      | .lit _ => v
      | .clockSlot | .signerKey0 | .accLamports0 | .accOwner0 | .accDataLen0
      | .accN | .isSigner0 | .isWritable0 | .isExecutable0 | .findPda _
      | .rentExemption _ => v
  let rec flipOp (fuel : Nat) (op : Ops.Op) : Ops.Op :=
    match fuel with
    | 0 => op
    | fuel' + 1 =>
      match op with
      | .returnState v => .returnState (flipVal fuel' v)
      | .returnU64 v => .returnU64 (flipVal fuel' v)
      | .okState v => .okState (flipVal fuel' v)
      | .checkedAddU64 l r => .checkedAddU64 (flipVal fuel' l) (flipVal fuel' r)
      | .checkedSubU64 l r => .checkedSubU64 (flipVal fuel' l) (flipVal fuel' r)
      | .checkedMulU64 l r => .checkedMulU64 (flipVal fuel' l) (flipVal fuel' r)
      | .checkedDivU64 l r => .checkedDivU64 (flipVal fuel' l) (flipVal fuel' r)
      | .checkedModU64 l r => .checkedModU64 (flipVal fuel' l) (flipVal fuel' r)
      | .ite c l r t f =>
        .ite c (flipVal fuel' l) (flipVal fuel' r)
          (t.map (flipOp fuel')) (f.map (flipOp fuel'))
      | .invoke prog metas data seed bump =>
        .invoke prog metas (data.map fun
          | .u64le v => .u64le (flipVal fuel' v)
          | w => w) seed (bump.map (flipVal fuel'))
      | .errorOverflow => .errorOverflow
  let ops :=
    if kind == .init && nLams > 1 then ops1.map (flipOp 8) else ops1
  let paramCount :=
    match kind with
    | .init => if nLams = 0 then 1 else nLams
    | .increment | .get => if nLams ≤ 1 then 0 else nLams - 1
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

private def fieldTypeExpr (env : Environment) (structName fieldName : Name) : Option Expr :=
  match getProjFnForField? env structName fieldName with
  | none => none
  | some proj =>
    match env.find? proj with
    | none => none
    | some info => some (peelForalls info.type)

private def leafSlots (env : Environment) (name : String) (ty : Expr) : Except String (Array IR.Slot) :=
  let ty := ty.consumeMData
  if ty.getAppFn.constName? == some ``UInt64 then
    .ok #[{ name, width := 8, abi := "u64-le" }]
  else if ty.getAppFn.constName? == some ``UInt32 then
    .ok #[{ name, width := 4, abi := "u32-le" }]
  else if ty.getAppFn.constName? == some ``UInt16 then
    .ok #[{ name, width := 2, abi := "u16-le" }]
  else if ty.getAppFn.constName? == some ``UInt8 then
    .ok #[{ name, width := 1, abi := "u8-le" }]
  else if ty.getAppFn.constName? == some ``Option then
    let args := ty.getAppArgs
    if args.size ≥ 1 && args[args.size - 1]!.consumeMData.getAppFn.constName? == some ``UInt64 then
      .ok #[
        { name := s!"{name}_tag", width := 8, abi := "u64-le" },
        { name := s!"{name}_p0", width := 8, abi := "u64-le" }
      ]
    else
      .error s!"extract/unsupported: field {name} is not Option UInt64"
  else if ty.getAppFn.constName? == some ``Vector then
    let args := ty.getAppArgs
    if args.size ≥ 2 && args[args.size - 2]!.consumeMData.getAppFn.constName? == some ``UInt64 then
      match asLit 8 args[args.size - 1]! with
      | some (.lit n) =>
        if n.toNat = 0 then
          .error s!"extract/unsupported: field {name} Vector length 0"
        else
          .ok ((List.range n.toNat).toArray.map fun i =>
            { name := s!"{name}_{i}", width := 8, abi := "u64-le" })
      | _ => .error s!"extract/unsupported: field {name} Vector length is not a literal"
    else
      .error s!"extract/unsupported: field {name} is not Vector UInt64 n"
  else if ty.getAppFn.constName? == some ``Array then
    .error s!"extract/unsupported: field {name} Array is not fixed-length; use Vector"
  else if ty.getAppFn.constName? == some ``Bool then
    .error s!"extract/unsupported: field {name} is not a supported leaf"
  else if let some tyName := ty.getAppFn.constName? then
    if isEnumLeaf env tyName then
      .ok #[{ name, width := 8, abi := "u64-le" }]
    else if isOptionLikeInductive env tyName then
      .ok #[
        { name := s!"{name}_tag", width := 8, abi := "u64-le" },
        { name := s!"{name}_p0", width := 8, abi := "u64-le" }
      ]
    else if match env.find? tyName with | some (.inductInfo _) => true | _ => false then
      .error s!"extract/unsupported: field {name} enum has payload"
    else
      .error s!"extract/unsupported: field {name} is not a supported leaf"
  else
    .error s!"extract/unsupported: field {name} is not a supported leaf"

/-- `Examples.Counter.init` → `Counter`。 -/
def programNameOfInit (n : Name) : String :=
  match n with
  | .str (.str _ mod) "init" => mod
  | .str _ "init" => "Program"
  | _ => "Program"

/-- 从 `init` 返回类型收槽。无 `extends`。叶子：UInt8/16/32/64、Option UInt64、Vector UInt64 n。 -/
def inferSlots (env : Environment) (initName : Name) : Except String (Array IR.Slot) := do
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
  let mut slots : Array IR.Slot := #[]
  for n in names do
    if (isSubobjectField? env structName n).isSome then
      throw "extract/unsupported: structure extends"
    let some ty := fieldTypeExpr env structName n
      | throw s!"extract/unsupported: field {n} has no type"
    slots := slots ++ (← leafSlots env n.toString ty)
  return slots

def inferFields (env : Environment) (initName : Name) : Except String (Array String) := do
  return (← inferSlots env initName).map (·.name)

private def valFields : Ops.Val → Array String
  | .field b n => valFields b |>.push n
  | .arg _ => #[]
  | .lit _ => #[]
  | .clockSlot | .signerKey0 | .accLamports0 | .accOwner0 | .accDataLen0
  | .accN | .isSigner0 | .isWritable0 | .isExecutable0 | .findPda _
  | .rentExemption _ => #[]

private def opFields : Ops.Op → Array String
  | .checkedAddU64 l r => valFields l ++ valFields r
  | .checkedSubU64 l r => valFields l ++ valFields r
  | .checkedMulU64 l r => valFields l ++ valFields r
  | .checkedDivU64 l r => valFields l ++ valFields r
  | .checkedModU64 l r => valFields l ++ valFields r
  | .ite _ l r t f =>
      valFields l ++ valFields r ++ t.flatMap opFields ++ f.flatMap opFields
  | .invoke _ _ data _ bump =>
      (data.flatMap fun
        | .u64le v => valFields v
        | _ => #[]) ++
        (match bump with | some v => valFields v | none => #[])
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
  let inferred ← inferSlots env initName
  let slots ←
    match fields? with
    | none => pure inferred
    | some fs =>
      if fs == inferred.map (·.name) then pure inferred
      else throw s!"extract/unsupported: fields {fs} != inferred {inferred.map (·.name)}"
  let initM ← extractMethod env .init initName
  let incM ← extractMethod env .increment incrementName
  let getM ← extractMethod env .get getName
  let program : IR.Program := {
    name := programName.getD (programNameOfInit initName)
    slots
    methods := #[initM, incM, getM]
  }
  unless IR.isProgramShape program do
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
  if inits.isEmpty then
    throw "extract/unsupported: missing init method"
  if muts.isEmpty then
    throw "extract/unsupported: missing mutating method"
  if views.isEmpty then
    throw "extract/unsupported: missing view method"
  let initName :=
    match inits.find? (fun n => IR.lastName n.toString == "init") with
    | some n => n
    | none => inits[0]!
  let inferred ← inferSlots env initName
  let slots ←
    match fields? with
    | none => pure inferred
    | some fs =>
      if fs == inferred.map (·.name) then pure inferred
      else throw s!"extract/unsupported: fields {fs} != inferred {inferred.map (·.name)}"
  let mut methods : Array IR.Method := #[]
  let mut seen : Array String := #[]
  for n in inits do
    let m ← extractMethod env .init n
    if seen.contains m.ixName then
      throw s!"extract/unsupported: duplicate ixName {m.ixName}"
    seen := seen.push m.ixName
    methods := methods.push m
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
    slots
    methods
  }
  unless IR.isProgramShape program do
    throw "extract/unsupported: not program shape"
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
