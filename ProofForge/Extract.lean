import Lean
import ProofForge.IR
import ProofForge.Ops
import ProofForge.Profile
import ProofForge.Attr
import ProofForge.Runtime

open Lean

namespace ProofForge.Extract

def sketchOfExpr (e : Expr) : Array String :=
  let names := e.getUsedConstantsAsSet.toList.toArray.qsort (·.toString < ·.toString)
  names.map (·.toString)

private def isConstNamed (e : Expr) (n : Name) : Bool :=
  e.consumeMData.getAppFn.constName? == some n

private def isVectorSet (e : Expr) : Bool :=
  isConstNamed e ``Vector.set ||
    (e.getAppFn.constName?.map (·.toString.endsWith "Vector.set")).getD false

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

/-- 把 `have x := v; e` 代进 `e`。剥 let 会丢掉 `have nodes := xs.set`。
必须走进 `dite` 的 proof λ，否则内层 `have` 还在。
`dite` 应用脊很长，fuel 要够。 -/
private def substLets (fuel : Nat) (e : Expr) : Expr :=
  match fuel with
  | 0 => e
  | fuel' + 1 =>
    match strip e with
    | .letE _ _ value body _ => substLets fuel' (body.instantiate1 (substLets fuel' value))
    | .lam n ty body bi => .lam n ty (substLets fuel' body) bi
    | .app _ _ =>
      let rec goApp (n : Nat) (e : Expr) : Expr :=
        match n, strip e with
        | n + 1, .app f a => .app (goApp n f) (substLets fuel' a)
        | _, e => substLets fuel' e
      goApp 32 e
    | e => e

/-- Drop only unused head lets and lower the remaining binders.
Effect calls commonly elaborate as `let _ := invoke; ok ...`; plain `peelLets` drops that
binder without lowering the source arguments, while substituting every let destroys the
local-result shape used by checked arithmetic decoding. -/
private def dropUnusedHeadLets (fuel : Nat) (e : Expr) : Expr :=
  match fuel with
  | 0 => e
  | fuel' + 1 =>
    match strip e with
    | .letE n ty value body nondep =>
      let body := dropUnusedHeadLets fuel' body
      if body.hasLooseBVar 0 then .letE n ty value body nondep
      else dropUnusedHeadLets fuel' (body.lowerLooseBVars 1 1)
    | e => e

private def isIteExpr (e : Expr) : Bool :=
  isConstNamed (peelLets (strip e)) ``ite || isConstNamed (peelLets (strip e)) ``dite

/-- 只代包着 `ite` 的 `have y := …; if y ≠ 0`。
`have next := mul; ok` 要留 bvar，给 `asOkState`。 -/
private def substIteLets (fuel : Nat) (e : Expr) : Expr :=
  match fuel with
  | 0 => e
  | fuel' + 1 =>
    match strip e with
    | .letE n ty value body nd =>
      let value := substIteLets fuel' value
      let body := substIteLets fuel' body
      if isIteExpr body then
        substIteLets fuel' (body.instantiate1 value)
      else
        .letE n ty value body nd
    | .lam n ty body bi => .lam n ty (substIteLets fuel' body) bi
    | .app _ _ =>
      let rec goApp (n : Nat) (e : Expr) : Expr :=
        match n, strip e with
        | n + 1, .app f a => .app (goApp n f) (substIteLets fuel' a)
        | _, e => substIteLets fuel' e
      goApp 32 e
    | e => e

/-- 剥 `pure` / `ForInStep.done` / `Option.some`；`Prod.mk` 只在末字段是 `PUnit` 时剥。 -/
private def peelControl (fuel : Nat) (e : Expr) : Expr :=
  match fuel with
  | 0 => peelLets (strip e)
  | fuel' + 1 =>
    let e := peelLets (strip e)
    if (isConstNamed e ``Pure.pure || endsWith e ".pure" ||
          isConstNamed e ``ForInStep.done || endsWith e ".done" ||
          isConstNamed e ``Option.some || endsWith e ".some") &&
        e.getAppArgs.size ≥ 1 then
      peelControl fuel' e.getAppArgs[e.getAppArgs.size - 1]!
    else if (isConstNamed e ``Prod.mk || endsWith e ".Prod.mk") && e.getAppArgs.size ≥ 2 then
      let last := strip e.getAppArgs[e.getAppArgs.size - 1]!
      if endsWith last ".unit" || isConstNamed last ``PUnit.unit then
        peelControl fuel' e.getAppArgs[e.getAppArgs.size - 2]!
      else e
    else e

private def isForInYield (e : Expr) : Bool :=
  let rec go (fuel : Nat) (e : Expr) : Bool :=
    match fuel with
    | 0 => false
    | fuel' + 1 =>
      let e := peelLets (strip e)
      if isConstNamed e ``ForInStep.yield || endsWith e ".yield" then true
      else
        match e with
        | .lam _ _ body _ => go fuel' body
        | .letE _ _ value body _ => go fuel' value || go fuel' body
        | _ => e.getAppArgs.any (go fuel')
  go 8 e

/-- `ForInStep.done` / `yield`：循环体里的 ite 不要降 proof λ。 -/
private def isForInStep (e : Expr) : Bool :=
  let rec go (fuel : Nat) (e : Expr) : Bool :=
    match fuel with
    | 0 => false
    | fuel' + 1 =>
      let e := peelLets (strip e)
      if isConstNamed e ``ForInStep.yield || endsWith e ".yield" ||
          isConstNamed e ``ForInStep.done || endsWith e ".done" then true
      else
        match e with
        | .lam _ _ body _ => go fuel' body
        | .letE _ _ value body _ => go fuel' value || go fuel' body
        | _ => e.getAppArgs.any (go fuel')
  go 8 e

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

/-- `s.book.price` → 槽 `book_price`。嵌套投影拼进一个 field 名。 -/
private def flattenField (base : Ops.Val) (leaf : String) : Ops.Val :=
  match base with
  | .field b parent => .field b s!"{parent}_{leaf}"
  | .indexGet b n i k _ =>
      -- 运行时下标上的元素投影：先估叶内偏移，`fillElemOff` 再用槽表改写。
      let off :=
        match leaf with
        | "left" => 0 | "right" => 8 | "parent" => 16
        | "color" => 24 | "key" => 32 | "value" => 40
        | _ => 0
      .indexGet b n i k off
  | b => .field b leaf

/-- 工具自己的模块。用户项目可以叫任何名字。 -/
private def isToolName (n : Name) : Bool :=
  let head := n.getRoot
  head == `ProofForge || head == `Lean || head == `Std || head == `Init ||
    head == `IO || head == `System || head == `Lake ||
    head == `HAdd || head == `HSub || head == `HMul || head == `HDiv ||
    head == `HMod || head == `HAnd || head == `HOr || head == `HXor ||
    head == `HShiftLeft || head == `HShiftRight || head == `Complement ||
    head == `LE || head == `LT || head == `GE || head == `GT ||
    head == `UInt8 || head == `UInt16 || head == `UInt32 || head == `UInt64 ||
    head == `Bool || head == `Nat || head == `Option || head == `Except ||
    head == `Prod || head == `Vector || head == `Array || head == `List ||
    head == `BitVec || head == `OfNat || head == `BEq || head == `Decidable ||
    head == `Float || head == `Float32 || head == `String || head == `Char

private def isReservedProj (last : String) : Bool :=
  last == "mk" || last == "set" || last == "ok" || last == "error" ||
    last == "getElem" || last == "getElem!" || last == "rfl" ||
    last.startsWith "_proof"

/-- 用户 datatype：structure 或 inductive，且不在工具模块里。 -/
private def isUserType (env : Environment) (n : Name) : Bool :=
  !isToolName n &&
    (isStructure env n ||
      match env.find? n with
      | some (.inductInfo _) => true
      | _ => false)

/-- 用户 structure / inductive 的投影 / 构造子。`UInt64.toNat`、`HSub.hSub` 不是。 -/
private def isUserName (env : Environment) (n : Name) : Bool :=
  if isToolName n || isReservedProj (IR.lastName n.toString) then
    false
  else if isUserType env n then
    true
  else
    match env.find? n with
    | some (.ctorInfo info) => isUserType env info.induct
    | some _ =>
      match n with
      | .str p last =>
        last != "toNat" && last != "toUInt64" && isUserType env p
      | _ => false
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
        let user := isUserName env n
        if (endsWith e ".findPda" || isConstNamed e ``ProofForge.Svm.Runtime.findPda) &&
            e.getAppArgs.size ≥ 1 then
          match strip e.getAppArgs[e.getAppArgs.size - 1]! with
          | .lit (.strVal s) => if s.isEmpty then none else some (.findPda s)
          | _ => none
        else if (endsWith e ".sha256Lit" || isConstNamed e ``ProofForge.Svm.Runtime.sha256Lit) &&
            e.getAppArgs.size ≥ 1 then
          match strip e.getAppArgs[e.getAppArgs.size - 1]! with
          | .lit (.strVal s) => some (.sha256Lit s)
          | _ => none
        else if (endsWith e ".keccak256Lit" || isConstNamed e ``ProofForge.Svm.Runtime.keccak256Lit) &&
            e.getAppArgs.size ≥ 1 then
          match strip e.getAppArgs[e.getAppArgs.size - 1]! with
          | .lit (.strVal s) => some (.keccak256Lit s)
          | _ => none
        else if (endsWith e ".accKeyWord" || isConstNamed e ``ProofForge.Svm.Runtime.accKeyWord) &&
            e.getAppArgs.size ≥ 2 then
          match asLit fuel' e.getAppArgs[e.getAppArgs.size - 2]!,
              asLit fuel' e.getAppArgs[e.getAppArgs.size - 1]! with
          | some (.lit acc), some (.lit word) =>
            let a := acc.toNat
            let w := word.toNat
            if IR.accInRange a && w ≤ 3 then some (.accKeyWord a w) else none
          | _, _ => none
        else if (endsWith e ".accOwnerWord" || isConstNamed e ``ProofForge.Svm.Runtime.accOwnerWord) &&
            e.getAppArgs.size ≥ 2 then
          match asLit fuel' e.getAppArgs[e.getAppArgs.size - 2]!,
              asLit fuel' e.getAppArgs[e.getAppArgs.size - 1]! with
          | some (.lit acc), some (.lit word) =>
            let a := acc.toNat
            let w := word.toNat
            if IR.accInRange a && w ≤ 3 then some (.accOwnerWord a w) else none
          | _, _ => none
        else if (endsWith e ".checkPda" || isConstNamed e ``ProofForge.Svm.Runtime.checkPda) &&
            e.getAppArgs.size ≥ 2 then
          match strip e.getAppArgs[e.getAppArgs.size - 2]!,
              asVal env fuel' e.getAppArgs[e.getAppArgs.size - 1]! with
          | .lit (.strVal s), some bump =>
            if s.isEmpty then none else some (.checkPda s bump)
          | _, _ => none
        else if (endsWith e ".rentExemption" ||
            isConstNamed e ``ProofForge.Svm.Runtime.rentExemption) &&
            e.getAppArgs.size ≥ 1 then
          match asLit fuel' e.getAppArgs[e.getAppArgs.size - 1]! with
          | some (.lit n) => some (.rentExemption n)
          | _ => none
        else if (endsWith e ".accLamports" || isConstNamed e ``ProofForge.Svm.Runtime.accLamports) &&
            e.getAppArgs.size ≥ 1 then
          match asLit fuel' e.getAppArgs[e.getAppArgs.size - 1]! with
          | some (.lit acc) =>
            let a := acc.toNat
            if IR.accInRange a then some (.accLamportsN a) else none
          | _ => none
        else if (endsWith e ".accDataLen" || isConstNamed e ``ProofForge.Svm.Runtime.accDataLen) &&
            e.getAppArgs.size ≥ 1 then
          match asLit fuel' e.getAppArgs[e.getAppArgs.size - 1]! with
          | some (.lit acc) =>
            let a := acc.toNat
            if IR.accInRange a then some (.accDataLenN a) else none
          | _ => none
        else if (endsWith e ".isSigner" || isConstNamed e ``ProofForge.Svm.Runtime.isSigner) &&
            e.getAppArgs.size ≥ 1 then
          match asLit fuel' e.getAppArgs[e.getAppArgs.size - 1]! with
          | some (.lit acc) =>
            let a := acc.toNat
            if IR.accInRange a then some (.isSignerN a) else none
          | _ => none
        else if (endsWith e ".isWritable" || isConstNamed e ``ProofForge.Svm.Runtime.isWritable) &&
            e.getAppArgs.size ≥ 1 then
          match asLit fuel' e.getAppArgs[e.getAppArgs.size - 1]! with
          | some (.lit acc) =>
            let a := acc.toNat
            if IR.accInRange a then some (.isWritableN a) else none
          | _ => none
        else if (endsWith e ".isExecutable" || isConstNamed e ``ProofForge.Svm.Runtime.isExecutable) &&
            e.getAppArgs.size ≥ 1 then
          match asLit fuel' e.getAppArgs[e.getAppArgs.size - 1]! with
          | some (.lit acc) =>
            let a := acc.toNat
            if IR.accInRange a then some (.isExecutableN a) else none
          | _ => none
        else if (endsWith e ".signerKey" || isConstNamed e ``ProofForge.Svm.Runtime.signerKey) &&
            e.getAppArgs.size ≥ 1 then
          match asLit fuel' e.getAppArgs[e.getAppArgs.size - 1]! with
          | some (.lit acc) =>
            let a := acc.toNat
            if IR.accInRange a then some (.signerKeyN a) else none
          | _ => none
        else if (endsWith e ".ownerIsSelf" || isConstNamed e ``ProofForge.Svm.Runtime.ownerIsSelf) &&
            e.getAppArgs.size ≥ 1 then
          match asLit fuel' e.getAppArgs[e.getAppArgs.size - 1]! with
          | some (.lit acc) =>
            let a := acc.toNat
            if IR.accInRange a then some (.ownerIsSelf a) else none
          | _ => none
        else if endsWith e ".evmMapGetAddr" || isConstNamed e ``ProofForge.Evm.Runtime.evmMapGetAddr then
          let args := e.getAppArgs
          let get (n : Nat) : Ops.Val :=
            if args.size ≥ n + 1 then (asVal env fuel' args[args.size - 1 - n]!).getD (.arg n)
            else .arg n
          some (.mapGetAddr (get 3) (get 2) (get 1) (get 0))
        else if endsWith e ".evmMapGetPair" || isConstNamed e ``ProofForge.Evm.Runtime.evmMapGetPair then
          let args := e.getAppArgs
          let get (n : Nat) : Ops.Val :=
            if args.size ≥ n + 1 then (asVal env fuel' args[args.size - 1 - n]!).getD (.arg n)
            else .arg n
          some (.mapGetPair (get 6) (get 5) (get 4) (get 3) (get 2) (get 1) (get 0))
        else if endsWith e ".evmMapGetU64" || isConstNamed e ``ProofForge.Evm.Runtime.evmMapGetU64 then
          let args := e.getAppArgs
          let get (n : Nat) : Ops.Val :=
            if args.size ≥ n + 1 then (asVal env fuel' args[args.size - 1 - n]!).getD (.arg n)
            else .arg n
          some (.mapGetU64 (get 1) (get 0))
        else if user && field.contains "." && e.getAppArgs.size ≥ 1 then
          let proj :=
            match field.splitOn "." with
            | [] => field
            | parts => parts.getLast!
          if proj == "mk" || proj == "ok" || proj == "error" ||
              proj.startsWith "_proof" || proj == "rfl" ||
              (field.startsWith "ProofForge.Runtime." || field.startsWith "ProofForge.Svm.Runtime." || field.startsWith "ProofForge.Evm.Runtime.") then none
          else if match env.find? n with
              | some (.ctorInfo _) => true
              | some (.inductInfo _) => true
              | _ => false then none
          else
            -- 整个 Vector 投影本身不是叶。下标 / 元素字段再展开。
            let skipVector :=
              match env.find? n with
              | some info =>
                info.type.getUsedConstantsAsSet.toList.any (· == ``Vector)
              | none => false
            if skipVector then none
            else
              match asVal env fuel' e.getAppArgs[e.getAppArgs.size - 1]! with
              | some b =>
                let leaf := if looksLikeOptionProj env n then s!"{proj}_tag" else proj
                -- `s.nodes[0]!.value`：基是 `nodes_0`，叶是 `value`。
                some (flattenField b leaf)
              | none =>
                match e.getAppArgs[e.getAppArgs.size - 1]! with
                | .bvar i =>
                  let leaf := if looksLikeOptionProj env n then s!"{proj}_tag" else proj
                  some (flattenField (.arg i) leaf)
                | _ => none
        else if (isConstNamed e ``UInt8.toUInt64 || isConstNamed e ``UInt64.toUInt8 ||
            isConstNamed e ``UInt16.toUInt64 || isConstNamed e ``UInt64.toUInt16 ||
            isConstNamed e ``UInt32.toUInt64 || isConstNamed e ``UInt64.toUInt32 ||
            isConstNamed e ``UInt64.toNat) &&
            e.getAppArgs.size ≥ 1 then
          asVal env fuel' e.getAppArgs[e.getAppArgs.size - 1]!
          else if (isConstNamed e ``HAdd.hAdd || endsWith e ".hAdd") && e.getAppArgs.size ≥ 2 then
          match asVal env fuel' e.getAppArgs[e.getAppArgs.size - 2]!,
                asVal env fuel' e.getAppArgs[e.getAppArgs.size - 1]! with
          | some l, some r => some (.addU64 l r)
          | _, _ => none
          else if (isConstNamed e ``HSub.hSub || endsWith e ".hSub" ||
              isConstNamed e ``Nat.sub) && e.getAppArgs.size ≥ 2 then
          match asVal env fuel' e.getAppArgs[e.getAppArgs.size - 2]!,
                asVal env fuel' e.getAppArgs[e.getAppArgs.size - 1]! with
          | some l, some r => some (.subU64 l r)
          | _, _ => none
          else if (isConstNamed e ``HMul.hMul || endsWith e ".hMul") &&
              e.getAppArgs.size ≥ 2 then
          match asVal env fuel' e.getAppArgs[e.getAppArgs.size - 2]!,
                asVal env fuel' e.getAppArgs[e.getAppArgs.size - 1]! with
          | some l, some r => some (.mulU64 l r)
          | _, _ => none
          else if (isConstNamed e ``HDiv.hDiv || endsWith e ".hDiv" ||
              isConstNamed e ``UInt64.div) && e.getAppArgs.size ≥ 2 then
          match asVal env fuel' e.getAppArgs[e.getAppArgs.size - 2]!,
                asVal env fuel' e.getAppArgs[e.getAppArgs.size - 1]! with
          | some l, some r => some (.divU64 l r)
          | _, _ => none
          else if (isConstNamed e ``HMod.hMod || endsWith e ".hMod" ||
              isConstNamed e ``UInt64.mod) && e.getAppArgs.size ≥ 2 then
          match asVal env fuel' e.getAppArgs[e.getAppArgs.size - 2]!,
                asVal env fuel' e.getAppArgs[e.getAppArgs.size - 1]! with
          | some l, some r => some (.modU64 l r)
          | _, _ => none
          else if (isConstNamed e ``HAnd.hAnd || endsWith e ".hAnd") && e.getAppArgs.size ≥ 2 then
          match asVal env fuel' e.getAppArgs[e.getAppArgs.size - 2]!,
                asVal env fuel' e.getAppArgs[e.getAppArgs.size - 1]! with
          | some l, some r => some (.bitAnd l r)
          | _, _ => none
        else if (isConstNamed e ``HOr.hOr || endsWith e ".hOr") && e.getAppArgs.size ≥ 2 then
          match asVal env fuel' e.getAppArgs[e.getAppArgs.size - 2]!,
                asVal env fuel' e.getAppArgs[e.getAppArgs.size - 1]! with
          | some l, some r => some (.bitOr l r)
          | _, _ => none
        else if (isConstNamed e ``HXor.hXor || endsWith e ".hXor") && e.getAppArgs.size ≥ 2 then
          match asVal env fuel' e.getAppArgs[e.getAppArgs.size - 2]!,
                asVal env fuel' e.getAppArgs[e.getAppArgs.size - 1]! with
          | some l, some r => some (.bitXor l r)
          | _, _ => none
        else if (isConstNamed e ``Complement.complement || endsWith e ".complement") &&
            e.getAppArgs.size ≥ 1 then
          match asVal env fuel' e.getAppArgs[e.getAppArgs.size - 1]! with
          | some v => some (.bitNot v)
          | none => none
        else if (isConstNamed e ``HShiftLeft.hShiftLeft || endsWith e ".hShiftLeft") &&
            e.getAppArgs.size ≥ 2 then
          match asVal env fuel' e.getAppArgs[e.getAppArgs.size - 2]!,
                asVal env fuel' e.getAppArgs[e.getAppArgs.size - 1]! with
          | some l, some r => some (.shiftL l r)
          | _, _ => none
        else if (isConstNamed e ``HShiftRight.hShiftRight || endsWith e ".hShiftRight") &&
            e.getAppArgs.size ≥ 2 then
          match asVal env fuel' e.getAppArgs[e.getAppArgs.size - 2]!,
                asVal env fuel' e.getAppArgs[e.getAppArgs.size - 1]! with
          | some l, some r => some (.shiftR l r)
          | _, _ => none
        else if (isConstNamed e ``Option.isSome || endsWith e ".isSome") && e.getAppArgs.size ≥ 1 then
          match asVal env fuel' e.getAppArgs[e.getAppArgs.size - 1]! with
          | some (.field b n) =>
            if n.endsWith "_tag" then some (.field b n)
            else some (.field b s!"{n}_tag")
          | some b => some (.field b s!"slot_tag")
          | none => none
        else if endsWith e ".u64Max" then
          some (.lit (~~~(0 : UInt64)))
        else if endsWith e ".shareBase" || endsWith e ".balBase" then
          some (.lit 0)
        else if endsWith e ".Token.allowBase" then
          some (.lit 1)
        else if endsWith e ".allowBase" then
          some (.lit 0)
        else if endsWith e ".clockSlot" || isConstNamed e ``ProofForge.Svm.Runtime.clockSlot then
          some .clockSlot
        else if endsWith e ".clockEpoch" || isConstNamed e ``ProofForge.Svm.Runtime.clockEpoch then
          some .clockEpoch
        else if endsWith e ".unixTime" || isConstNamed e ``ProofForge.Svm.Runtime.unixTime then
          some .unixTime
        else if endsWith e ".slotsPerEpoch" || isConstNamed e ``ProofForge.Svm.Runtime.slotsPerEpoch then
          some .slotsPerEpoch
        else if endsWith e ".cpiReturn" || isConstNamed e ``ProofForge.Svm.Runtime.cpiReturn then
          some .cpiReturn
        else if endsWith e ".signerKey0" || isConstNamed e ``ProofForge.Svm.Runtime.signerKey0 then
          some .signerKey0
        else if endsWith e ".evmCaller" || isConstNamed e ``ProofForge.Evm.Runtime.evmCaller then
          some .evmCaller
        else if endsWith e ".evmBlockNumber" || isConstNamed e ``ProofForge.Evm.Runtime.evmBlockNumber then
          some .evmBlockNumber
        else if endsWith e ".evmTimestamp" || isConstNamed e ``ProofForge.Evm.Runtime.evmTimestamp then
          some .evmTimestamp
        else if endsWith e ".evmChainId" || isConstNamed e ``ProofForge.Evm.Runtime.evmChainId then
          some .evmChainId
        else if endsWith e ".evmSelf" || isConstNamed e ``ProofForge.Evm.Runtime.evmSelf then
          some .evmSelf
        else if endsWith e ".evmCallValue" || isConstNamed e ``ProofForge.Evm.Runtime.evmCallValue then
          some .evmCallValue
        else if endsWith e ".evmSelfBalance" || isConstNamed e ``ProofForge.Evm.Runtime.evmSelfBalance then
          some .evmSelfBalance
        else if endsWith e ".evmCallerW0" || isConstNamed e ``ProofForge.Evm.Runtime.evmCallerW0 then
          some .evmCallerW0
        else if endsWith e ".evmCallerW1" || isConstNamed e ``ProofForge.Evm.Runtime.evmCallerW1 then
          some .evmCallerW1
        else if endsWith e ".evmCallerW2" || isConstNamed e ``ProofForge.Evm.Runtime.evmCallerW2 then
          some .evmCallerW2
        else if endsWith e ".evmSelfW0" || isConstNamed e ``ProofForge.Evm.Runtime.evmSelfW0 then
          some .evmSelfW0
        else if endsWith e ".evmSelfW1" || isConstNamed e ``ProofForge.Evm.Runtime.evmSelfW1 then
          some .evmSelfW1
        else if endsWith e ".evmSelfW2" || isConstNamed e ``ProofForge.Evm.Runtime.evmSelfW2 then
          some .evmSelfW2
        else if endsWith e ".accLamports0" || isConstNamed e ``ProofForge.Svm.Runtime.accLamports0 then
          some .accLamports0
        else if endsWith e ".accOwner0" || isConstNamed e ``ProofForge.Svm.Runtime.accOwner0 then
          some .accOwner0
        else if endsWith e ".accDataLen0" || isConstNamed e ``ProofForge.Svm.Runtime.accDataLen0 then
          some .accDataLen0
        else if endsWith e ".accN" || isConstNamed e ``ProofForge.Svm.Runtime.accN then
          some .accN
        else if endsWith e ".isSigner0" || isConstNamed e ``ProofForge.Svm.Runtime.isSigner0 then
          some .isSigner0
        else if endsWith e ".isWritable0" || isConstNamed e ``ProofForge.Svm.Runtime.isWritable0 then
          some .isWritable0
        else if endsWith e ".isExecutable0" || isConstNamed e ``ProofForge.Svm.Runtime.isExecutable0 then
          some .isExecutable0
        else if endsWith e ".accLamports1" || isConstNamed e ``ProofForge.Svm.Runtime.accLamports1 then
          some .accLamports1
        else if endsWith e ".accOwner1" || isConstNamed e ``ProofForge.Svm.Runtime.accOwner1 then
          some .accOwner1
        else if endsWith e ".accDataLen1" || isConstNamed e ``ProofForge.Svm.Runtime.accDataLen1 then
          some .accDataLen1
        else if endsWith e ".isSigner1" || isConstNamed e ``ProofForge.Svm.Runtime.isSigner1 then
          some .isSigner1
        else if endsWith e ".isWritable1" || isConstNamed e ``ProofForge.Svm.Runtime.isWritable1 then
          some .isWritable1
        else if endsWith e ".isExecutable1" || isConstNamed e ``ProofForge.Svm.Runtime.isExecutable1 then
          some .isExecutable1
        else if (endsWith e ".systemTransfer" ||
            isConstNamed e ``ProofForge.Svm.Runtime.systemTransfer) && e.getAppArgs.size ≥ 1 then
          asVal env fuel' e.getAppArgs[e.getAppArgs.size - 1]!
        else if endsWith e ".invokeAcc1" || isConstNamed e ``ProofForge.Svm.Runtime.invokeAcc1 ||
            endsWith e ".invoke" || isConstNamed e ``ProofForge.Svm.Runtime.invoke ||
            endsWith e ".invokeSigned" || isConstNamed e ``ProofForge.Svm.Runtime.invokeSigned then
          some (.lit 0)
        else if ((endsWith e ".evmDeposit" ||
            isConstNamed e ``ProofForge.Evm.Runtime.evmDeposit) ||
            (endsWith e ".evmLogTipped" ||
            isConstNamed e ``ProofForge.Evm.Runtime.evmLogTipped) ||
            (endsWith e ".evmLogIncremented" ||
            isConstNamed e ``ProofForge.Evm.Runtime.evmLogIncremented) ||
            (endsWith e ".evmLogTransfer" ||
            isConstNamed e ``ProofForge.Evm.Runtime.evmLogTransfer) ||
            (endsWith e ".evmLogApproval" ||
            isConstNamed e ``ProofForge.Evm.Runtime.evmLogApproval) ||
            (endsWith e ".evmSendEth" ||
            isConstNamed e ``ProofForge.Evm.Runtime.evmSendEth) ||
            (endsWith e ".evmMapGetU64" ||
            isConstNamed e ``ProofForge.Evm.Runtime.evmMapGetU64) ||
            (endsWith e ".evmMapSetU64" ||
            isConstNamed e ``ProofForge.Evm.Runtime.evmMapSetU64) ||
            (endsWith e ".evmMapGetAddr" ||
            isConstNamed e ``ProofForge.Evm.Runtime.evmMapGetAddr) ||
            (endsWith e ".evmMapSetAddr" ||
            isConstNamed e ``ProofForge.Evm.Runtime.evmMapSetAddr) ||
            (endsWith e ".evmMapGetPair" ||
            isConstNamed e ``ProofForge.Evm.Runtime.evmMapGetPair) ||
            (endsWith e ".evmMapSetPair" ||
            isConstNamed e ``ProofForge.Evm.Runtime.evmMapSetPair) ||
            (endsWith e ".evmTokenTransfer" ||
            isConstNamed e ``ProofForge.Evm.Runtime.evmTokenTransfer) ||
            (endsWith e ".evmTokenBalanceOfSelf" ||
            isConstNamed e ``ProofForge.Evm.Runtime.evmTokenBalanceOfSelf)) &&
            e.getAppArgs.size ≥ 1 then
            if endsWith e ".evmMapGetU64" || isConstNamed e ``ProofForge.Evm.Runtime.evmMapGetU64 then
            let args := e.getAppArgs
            let get (n : Nat) : Ops.Val :=
              if args.size ≥ n + 1 then (asVal env fuel' args[args.size - 1 - n]!).getD (.arg n)
              else .arg n
            some (.mapGetU64 (get 1) (get 0))
            else if endsWith e ".evmMapGetAddr" || isConstNamed e ``ProofForge.Evm.Runtime.evmMapGetAddr then
            let args := e.getAppArgs
            let get (n : Nat) : Ops.Val :=
              if args.size ≥ n + 1 then (asVal env fuel' args[args.size - 1 - n]!).getD (.arg n)
              else .arg n
            some (.mapGetAddr (get 3) (get 2) (get 1) (get 0))
            else if endsWith e ".evmMapGetPair" || isConstNamed e ``ProofForge.Evm.Runtime.evmMapGetPair then
            let args := e.getAppArgs
            let get (n : Nat) : Ops.Val :=
              if args.size ≥ n + 1 then (asVal env fuel' args[args.size - 1 - n]!).getD (.arg n)
              else .arg n
            some (.mapGetPair (get 6) (get 5) (get 4) (get 3) (get 2) (get 1) (get 0))
            else
            asVal env fuel' e.getAppArgs[e.getAppArgs.size - 1]!
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
        else if (isConstNamed e ``GetElem.getElem || isConstNamed e ``GetElem?.getElem! ||
            isConstNamed e ``Vector.get ||
            endsWith e ".getElem" || endsWith e ".getElem!" || endsWith e ".get") &&
            e.getAppArgs.size ≥ 2 then
          let args := e.getAppArgs
          -- Do not recursively search proof/type arguments for an index: their local binders
          -- are not source values. The collection/index positions are fixed by GetElem.
          let collIndex? : Option (Expr × Expr) :=
            if isConstNamed e ``GetElem.getElem || endsWith e ".getElem" then
              if h : args.size ≥ 3 then some (args[args.size - 3], args[args.size - 2])
              else none
            else if h : args.size ≥ 2 then
              some (args[args.size - 2], args[args.size - 1])
            else none
          let rec findState (fuel : Nat) (e : Expr) : Option Nat :=
            match fuel with
            | 0 => none
            | fuel' + 1 =>
              match strip e with
              | .bvar j => some j
              | e => e.getAppArgs.findSome? (findState fuel')
          let rec fieldNameOf (fuel : Nat) (e : Expr) : Option String :=
            match fuel with
            | 0 => none
            | fuel' + 1 =>
              match e.getAppFn.constName? with
              | some n =>
                let s := n.toString
                let last := IR.lastName s
                let user := isUserName env n
                let skipTy :=
                  match env.find? n with
                  | some (.inductInfo _) => true
                  | some (.ctorInfo _) => true
                  | some _ =>
                    -- `Node.value` 是元素投影，不是账户字段 `nodes`。
                    last == "value" || last == "key" || last == "left" ||
                      last == "right" || last == "parent" || last == "color"
                  | none => false
                if !user || isReservedProj last || skipTy then
                  e.getAppArgs.findSome? (fieldNameOf fuel')
                else some last
              | none => e.getAppArgs.findSome? (fieldNameOf fuel')
          match collIndex?.bind fun pair => (asVal env fuel' pair.2).map (pair.1, ·) with
          | some (collection, .lit n) =>
            let i := n.toNat
            let baseField :=
              match asVal env fuel' collection with
              | some (.field _ fname) => some fname
              | _ => none
            match findState fuel' collection, baseField with
            | some j, some fname =>
              let suf := s!"_{i}"
              let base :=
                if fname.endsWith suf then fname.dropEnd suf.length |>.copy else fname
              some (.field (.arg j) s!"{base}_{i}")
            | some j, none =>
              match fieldNameOf 8 collection with
              | some fname => some (.field (.arg j) s!"{fname}_{i}")
              | none => none
            | _, _ => none
          | some (collection, idx) =>
            let lits := args.filterMap (asLit fuel')
            let len :=
              if h : lits.size > 0 then
                match lits[0] with
                | .lit n => n.toNat
                | _ => 0
              else 0
            match findState fuel' collection, fieldNameOf 8 collection with
            | some j, some fname => some (.indexGet (.arg j) fname idx len)
            | some j, none => some (.indexGet (.arg j) "cells" idx len)
            | _, _ => none
          | none => none

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
  else if isConstNamed e ``GE.ge || endsWith e ".ge" || endsWith e ".hGe" then
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
  if isConstNamed e ``Prod.mk || endsWith e ".Prod.mk" then none
  else if endsWith e ".State.mk" || endsWith e ".mk" then
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

/--
Trace a nested `Vector.set` chain back to the user structure projection that owns the vector.
Element projections such as `Node.left` can occur in an intervening branch condition; only a
projection whose result type mentions `Vector` is a valid storage base.
-/
private def vectorBaseName (env : Environment) (fuel : Nat) (e : Expr) : Option String :=
  match fuel with
  | 0 => none
  | fuel' + 1 =>
    match e.getAppFn.constName? with
    | some n =>
      let last := IR.lastName n.toString
      let skipTy :=
        match env.find? n with
        | some (.inductInfo _) => true
        | some (.ctorInfo _) => true
        | _ => false
      let returnsVector :=
        match env.find? n with
        | some info => info.type.getUsedConstantsAsSet.toList.any (· == ``Vector)
        | none => false
      if !isUserName env n || isReservedProj last || skipTy || !returnsVector then
        e.getAppArgs.findSome? (vectorBaseName env fuel')
      else some last
    | none => e.getAppArgs.findSome? (vectorBaseName env fuel')

/-- `xs.set i v`：只抽出被改的那一叶。 -/
private def asVectorSet (env : Environment) (e : Expr) : Option Ops.Val :=
  let e := strip e
  if isVectorSet e then
    let args := e.getAppArgs
    -- 只认编译期常量下标。运行时下标走 `asIndexSet`。
    -- `Vector.set.{u} α n xs i v h` 里 `n` 是长度，不能当 index。
    let idx? : Option Nat :=
      Id.run do
        let mut seenLen := false
        for a in args do
          match asLit 8 a with
          | some (.lit n) =>
            if !seenLen then
              seenLen := true
            else
              return some n.toNat
          | _ => pure ()
        return none
    -- `Vector.set xs i v h`：值在字面量下标之后。
    -- 嵌套 `Node.mk` 时取被改的那一叶（preferLast）。
    let payload :=
      Id.run do
        let mut seenIdx := false
        for a in args do
          match asLit 8 a with
          | some (.lit _) =>
            seenIdx := true
          | _ =>
            if seenIdx then
              -- `{ s.nodes[0]! with value := v }` 展开成 `have __src := …; Node.mk …`。
              let a := peelLets (strip a)
              match asStateMk env a true with
              | some v => return some (true, v)
              | none =>
                match val env a with
                | some v => return some (false, v)
                | none => pure ()
        return none
    match idx?, payload, vectorBaseName env 16 e with
    | some i, some (true, v), some n => some (.field v s!"{n}_{i}_value")
    | some i, some (false, v), some n => some (.field v s!"{n}_{i}")
    | some i, some (_, v), none => some (.field v s!"cells_{i}")
    | _, _, _ => none
  else none

/-- `State.mk` 每个字段一个值。`Option` 展开成 tag + payload；`Vector` 展开成各叶。 -/
private def asIndexSets (env : Environment) (e0 : Expr) : Option (Array Ops.Op) :=
  let rec go (fuel : Nat) (e : Expr) : Option Expr :=
    match fuel with
    | 0 => none
    | fuel' + 1 =>
      let e := strip e
      match e with
      | .letE _ _ value body _ => go fuel' value <|> go fuel' body
      | .lam _ _ body _ => go fuel' body
      | _ =>
        if isConstNamed e ``Except.ok && e.getAppArgs.size ≥ 1 then
          go fuel' e.getAppArgs[e.getAppArgs.size - 1]!
        else if isConstNamed e ``Prod.mk && e.getAppArgs.size ≥ 2 then
          go fuel' e.getAppArgs[e.getAppArgs.size - 2]!
        else if isVectorSet e then
          some e
        else
          e.getAppArgs.findSome? (go fuel')
  match go 8 e0 with
  | none => none
  | some e =>
  if isVectorSet e then
    let args := e.getAppArgs
    let lits := args.filterMap (asLit 8)
    let len :=
      if h : lits.size > 0 then
        match lits[0] with
        | .lit n => n.toNat
        | _ => 0
      else 0
    -- `Vector.set α n xs i v h`：最后四项固定为 xs、下标、新元素、证明。
    -- 不要扫描证明参数；其中的局部 binder 不是源程序的动态下标。
    let parsed :=
      Id.run do
        if h : args.size ≥ 4 then
          let idx? := val env args[args.size - 3]
          let payload := substLets 8 (peelLets (strip args[args.size - 2]))
          let isCtor :=
            match payload.getAppFn.constName? with
            | some n =>
              match env.find? n with
              | some (.ctorInfo _) => true
              | _ => false
            | none => false
          if isCtor then return (false, idx?, some payload, none)
          else return (false, idx?, none, val env payload)
        else
          return (false, none, none, none)
    let rec changedLeaves (selfIdx : Option Ops.Val) (fuel : Nat) (e : Expr) :
        Array (String × Ops.Val) :=
      match fuel with
      | 0 => #[]
      | fuel' + 1 =>
        let e := substLets 16 (strip e)
        match e.getAppFn.constName? with
        | some n =>
          match env.find? n with
          | some (.ctorInfo c) =>
            if isUserType env c.induct && isStructure env c.induct then
              let names := getStructureFields env c.induct
              let args := e.getAppArgs
              let nF := names.size
              if nF == 0 || args.size < nF then #[]
              else
                -- `{ src with left := a, parent := b }`：叶来自别的节点 / 别的字段就算改了。
                -- `y.parent := x.parent` 两边都叫 parent，不能只看字段名。
                Id.run do
                  let mut acc : Array (String × Ops.Val) := #[]
                  for i in [0:nF] do
                    if h : i < nF ∧ i < args.size then
                      let fname := names[i].toString
                      let arg := substLets 8 (strip args[args.size - nF + i])
                      let looksSame :=
                        match val env arg with
                        | some (.field (.arg _) n) =>
                          n == fname || n.endsWith ("_" ++ fname)
                        | some (.indexGet _ _ i _ off) =>
                          -- 同一下标上的同一叶才算没改。
                          let sameOff :=
                            off ==
                              (match fname with
                               | "left" => 0 | "right" => 8 | "parent" => 16
                               | "color" => 24 | "key" => 32 | "value" => 40
                               | _ => 999)
                          sameOff &&
                            (match selfIdx with
                             | some j => i == j
                             | none => true)
                        | _ => false
                      unless looksSame do
                        match val env arg with
                        | some v => acc := acc.push (fname, v)
                        | none => pure ()
                  return acc
            else
              e.getAppArgs.foldl (init := #[]) fun a x =>
                a ++ changedLeaves selfIdx fuel' x
          | _ => e.getAppArgs.foldl (init := #[]) fun a x =>
              a ++ changedLeaves selfIdx fuel' x
        | none => e.getAppArgs.foldl (init := #[]) fun a x =>
            a ++ changedLeaves selfIdx fuel' x
    match parsed with
    | (true, _, _, _) => none
    | (false, some idx, some payloadE, _) =>
      match idx with
      | .lit _ => none
      | _ =>
        let leaves := changedLeaves (some idx) 8 payloadE
        let leaves :=
          if leaves.isEmpty then
            match val env payloadE with
            | some v => #[("", v)]
            | none => #[]
          else leaves
        if leaves.isEmpty then none
        else
          let name := (vectorBaseName env 16 e).getD "cells"
          some (leaves.map fun p =>
            let hint :=
              match p.1 with
              | "left" => 0 | "right" => 8 | "parent" => 16
              | "color" => 24 | "key" => 32 | "value" => 40
              | _ => 0
            Ops.Op.indexSet name idx p.2 len hint)
    | (false, some idx, none, some payload) =>
      match idx with
      | .lit _ => none
      | _ =>
        let name := (vectorBaseName env 16 e).getD "cells"
        some #[.indexSet name idx payload len 0]
    | _ => none
  else none

private def asIndexSet (env : Environment) (e0 : Expr) : Option Ops.Op :=
  match asIndexSets env e0 with
  | some ops => ops[0]?
  | none => none

private def asStateFields (env : Environment) (e : Expr) : Option (Array Ops.Val) :=
  let rec collect (fuel : Nat) (e : Expr) : Array Ops.Val :=
    match fuel with
    | 0 => #[]
    | fuel' + 1 =>
      let e := strip e
      if (endsWith e ".State.mk" || endsWith e ".mk") &&
          !(isConstNamed e ``Prod.mk || endsWith e ".Prod.mk") then
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
              else if endsWith a "Vector.mk" || isConstNamed a ``Vector.mk then
                match asVectorLits env a with
                | some vs => acc := acc ++ vs
                | none => pure ()
              else
                let nested := collect fuel' a
                if !nested.isEmpty then
                  acc := acc ++ nested
                else
                  match asVectorSet env a with
                  | some v => acc := acc.push v
                  | none =>
                    match val env a with
                    | some v => acc := acc.push v
                    | none => pure ()
          acc
      else #[]
  let acc := collect 8 e
  if acc.isEmpty then none else some acc

/-- 用户记录构造子的显式字段（丢掉类型参数 / 证明）。 -/
private def userCtorFields (env : Environment) (e : Expr) : Option (Array Expr) :=
  let e := peelLets (strip e)
  match e.getAppFn.constName? with
  | none => none
  | some n =>
    match env.find? n with
    | some (.ctorInfo c) =>
      if isUserType env c.induct && isStructure env c.induct then
        let args := e.getAppArgs
        if args.size ≥ c.numFields then
          some (args.extract (args.size - c.numFields) args.size)
        else none
      else none
    | _ => none

private def looksUnchangedField (v : Ops.Val) (leaf : String) : Bool :=
  match v with
  | .field _ n =>
    n == leaf || n.endsWith ("_" ++ leaf) || leaf.endsWith ("_" ++ n)
  | _ => false

/-- 把一个值摊成账户叶。`Vector.set` / 嵌套 `with` 只展开被改的那些。 -/
private partial def flattenLeaves (env : Environment) (base : String) (e : Expr) :
    Array (String × Ops.Val) :=
  let e := peelLets (strip e)
  if isVectorSet e then
    let args := e.getAppArgs
    -- `Vector.set α n xs i v h`：第一个字面量是长度，第二个是下标。
    -- 长度之后的第一个非字面量是旧向量，两下标之后才是新元素。
    let parsed :=
      Id.run do
        let mut nLits : Nat := 0
        let mut xs? : Option Expr := none
        let mut idx? : Option Nat := none
        let mut payload? : Option Expr := none
        for a in args do
          if endsWith a "._proof_1" || endsWith a "._proof_2" || endsWith a ".rfl" then
            pure ()
          else
            match asLit 8 a with
            | some (.lit n) =>
              if nLits == 0 then
                nLits := 1
              else if nLits == 1 then
                nLits := 2
                idx? := some n.toNat
              else
                pure ()
            | some _ =>
              pure ()
            | none =>
              if nLits == 1 && xs?.isNone then
                xs? := some (peelLets (strip a))
              else if nLits ≥ 2 && payload?.isNone then
                payload? := some (peelLets (strip a))
        return (idx?, xs?, payload?)
    match parsed with
    | (some i, xs?, some payload) =>
      let pre := if base.isEmpty then s!"{i}" else s!"{base}_{i}"
      let here := flattenLeaves env pre payload
      let here :=
        if here.isEmpty then
          match val env payload with
          | some v => #[(pre, v)]
          | none => #[]
        else here
      let prev :=
        match xs? with
        | some xs => flattenLeaves env base xs
        | none => #[]
      prev ++ here
    | _ => #[]
  else if let some fields := userCtorFields env e then
    match e.getAppFn.constName? with
    | none => #[]
    | some n =>
      match env.find? n with
      | some (.ctorInfo c) =>
        let names := getStructureFields env c.induct
        Id.run do
          let mut acc : Array (String × Ops.Val) := #[]
          for i in [0:fields.size] do
            if h : i < names.size ∧ i < fields.size then
              let fname := names[i].toString
              let child := if base.isEmpty then fname else s!"{base}_{fname}"
              let arg := fields[i]
              let nested := flattenLeaves env child arg
              let isVectorField :=
                match env.find? (c.induct.str fname) with
                | some info => info.type.getUsedConstantsAsSet.toList.any (· == ``Vector)
                | none => false
              if !nested.isEmpty then
                acc := acc ++ nested.filter fun p => !looksUnchangedField p.2 p.1
              else if isVectorField then
                -- A runtime-indexed vector is represented only by typed indexSet writes.
                -- Its root projection is not a scalar account leaf.
                pure ()
              else
                match asOptionPayload env arg with
                | some (.lit 0) =>
                  acc := acc.push (s!"{child}_tag", .lit 0) |>.push (s!"{child}_p0", .lit 0)
                | some v =>
                  acc := acc.push (s!"{child}_tag", .lit 1) |>.push (s!"{child}_p0", v)
                | none =>
                  match val env arg with
                  | some v =>
                    unless looksUnchangedField v child || looksUnchangedField v fname do
                      acc := acc.push (child, v)
                  | none =>
                    if isConstNamed arg ``Bool.true || endsWith arg ".true" then
                      acc := acc.push (child, .lit 1)
                    else if isConstNamed arg ``Bool.false || endsWith arg ".false" then
                      acc := acc.push (child, .lit 0)
                    else
                      match arg.getAppFn.constName? with
                      | some ctor =>
                        match env.find? ctor with
                        | some (.ctorInfo info) =>
                          match enumCtorIndex env info.induct ctor with
                          | some k => acc := acc.push (child, .lit (UInt64.ofNat k))
                          | none => pure ()
                        | _ => pure ()
                      | none =>
                        match asLit 8 arg with
                        | some v => acc := acc.push (child, v)
                        | none => pure ()
          acc
      | _ => #[]
  else
    match val env e with
    | some v =>
      if base.isEmpty || looksUnchangedField v base then #[] else #[(base, v)]
    | none => #[]

/-- `Except.ok (State.mk …, ret)`：按叶 diff，改了几个槽就写几条。 -/
private def asStoreFields (env : Environment) (e : Expr)
    (includeSingle : Bool := false) : Option (Array Ops.Op) :=
  let e := peelControl 8 (dropUnusedHeadLets 32 e)
  if isConstNamed e ``Except.ok then
    let args := e.getAppArgs
    if args.size ≥ 1 then
      let pair := strip args[args.size - 1]!
      if isConstNamed pair ``Prod.mk && pair.getAppArgs.size ≥ 2 then
        let st := pair.getAppArgs[pair.getAppArgs.size - 2]!
        let ret := pair.getAppArgs[pair.getAppArgs.size - 1]!
        let vectorBase := vectorBaseName env 32 st
        let leaves := (flattenLeaves env "" st).filter fun p => some p.1 != vectorBase
        if leaves.isEmpty || (!includeSingle && leaves.size == 1) then none
        else
          match val env ret with
          | none => none
          | some rv =>
            some ((leaves.map fun p => Ops.Op.storeField p.1 p.2).push (.okState rv))
      else none
    else none
  else none

private def asOkState (env : Environment) (e : Expr) : Option Ops.Val :=
  let e := peelControl 8 (dropUnusedHeadLets 32 e)
  if isConstNamed e ``Except.ok then
    let args := e.getAppArgs
    if args.size ≥ 1 then
      let pair := strip args[args.size - 1]!
      if isConstNamed pair ``Prod.mk then
        let pargs := pair.getAppArgs
        if pargs.size ≥ 2 then
          let st := pargs[pargs.size - 2]!
          let boolLit :=
            (strip st).getAppArgs.findSome? fun a =>
              if isConstNamed a ``Bool.true || endsWith a ".true" then some (.lit 1)
              else if isConstNamed a ``Bool.false || endsWith a ".false" then some (.lit 0)
              else none
          match boolLit with
          | some v => some v
          | none =>
          match asOptionPayload env st with
          | some v => some v
          | none =>
            -- `{ s with nodes := s.nodes.set i { … with value := v } }`
            -- 展开成 `State.mk s.root s.size (Vector.set …)`。`val` 会先吃到
            -- `s.root`，必须先认嵌套 Vector.set，否则 dest 落到错误槽。
            match asVectorSet env (strip st) <|>
                (strip st).getAppArgs.findSome? (asVectorSet env) with
            | some v => some v
            | none =>
            match val env st with
            | some (.clockSlot) => some .clockSlot
            | some (.clockEpoch) => some .clockEpoch
            | some (.unixTime) => some .unixTime
            | some (.slotsPerEpoch) => some .slotsPerEpoch
            | some (.cpiReturn) => some .cpiReturn
            | some (.signerKey0) => some .signerKey0
            | some (.accLamports0) => some .accLamports0
            | some (.accOwner0) => some .accOwner0
            | some (.accDataLen0) => some .accDataLen0
            | some (.accN) => some .accN
            | some (.isSigner0) => some .isSigner0
            | some (.isWritable0) => some .isWritable0
            | some (.isExecutable0) => some .isExecutable0
            | some (.accLamports1) => some .accLamports1
            | some (.accOwner1) => some .accOwner1
            | some (.accDataLen1) => some .accDataLen1
            | some (.isSigner1) => some .isSigner1
            | some (.isWritable1) => some .isWritable1
            | some (.isExecutable1) => some .isExecutable1
            | some (.findPda s) => some (.findPda s)
            | some (.checkPda s b) => some (.checkPda s b)
            | some (.rentExemption n) => some (.rentExemption n)
            | some (.sha256Lit s) => some (.sha256Lit s)
            | some (.keccak256Lit s) => some (.keccak256Lit s)
            | some (.accKeyWord a w) => some (.accKeyWord a w)
            | some (.accOwnerWord a w) => some (.accOwnerWord a w)
            | some (.accLamportsN a) => some (.accLamportsN a)
            | some (.accDataLenN a) => some (.accDataLenN a)
            | some (.isSignerN a) => some (.isSignerN a)
            | some (.isWritableN a) => some (.isWritableN a)
            | some (.isExecutableN a) => some (.isExecutableN a)
            | some (.signerKeyN a) => some (.signerKeyN a)
            | some (.ownerIsSelf a) => some (.ownerIsSelf a)
            | some v =>
              if Ops.hasEvmLeaf #[.returnU64 v] || Ops.isLangLeaf v then some v else none
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

private def errorCtorName (e : Expr) : Option String :=
  let e := peelControl 8 e
  if isConstNamed e ``Except.error then
    let args := e.getAppArgs
    if h : args.size > 0 then
      let ctor := strip args[args.size - 1]
      match ctor.getAppFn.constName? with
      | some n =>
        let last := IR.lastName n.toString
        if last == "overflow" then none else some last
      | none => none
    else none
  else none

private def isErrorOverflow (e : Expr) : Bool :=
  let e := peelControl 8 e
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
  n == (`ProofForge.Runtime).append suf.toName ||
    n == (`ProofForge.Svm.Runtime).append suf.toName ||
    n == (`ProofForge.Evm.Runtime).append suf.toName ||
    n.toString.endsWith s!".{suf}"

private def mentionsRuntime (e : Expr) (suf : String) : Bool :=
  let suf := if suf.front == '.' then String.ofList (suf.toList.drop 1) else suf
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
  if isConstNamed e ``ProofForge.Svm.Runtime.CpiMeta.mk || endsWith e ".mk" then
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
  if isConstNamed e ``ProofForge.Svm.Runtime.CpiWord.u8le || endsWith e ".u8le" then
    if e.getAppArgs.size ≥ 1 then
      match val env e.getAppArgs[e.getAppArgs.size - 1]! >>= natOfVal with
      | some n => some (.u8le (UInt64.ofNat n))
      | none => none
    else none
  else if isConstNamed e ``ProofForge.Svm.Runtime.CpiWord.u32le || endsWith e ".u32le" then
    if e.getAppArgs.size ≥ 1 then
      match val env e.getAppArgs[e.getAppArgs.size - 1]! >>= natOfVal with
      | some n => some (.u32le (UInt64.ofNat n))
      | none => none
    else none
  else if isConstNamed e ``ProofForge.Svm.Runtime.CpiWord.u64le || endsWith e ".u64le" then
    if e.getAppArgs.size ≥ 1 then
      match val env e.getAppArgs[e.getAppArgs.size - 1]! with
      | some v => some (.u64le v)
      | none => none
    else none
  else if isConstNamed e ``ProofForge.Svm.Runtime.CpiWord.ascii || endsWith e ".ascii" then
    if e.getAppArgs.size ≥ 1 then
      match e.getAppArgs[e.getAppArgs.size - 1]! with
      | .lit (.strVal s) => some (.ascii s)
      | _ => none
    else none
  else if isConstNamed e ``ProofForge.Svm.Runtime.CpiWord.programId || endsWith e ".programId" then
    some .programId
  else if isConstNamed e ``ProofForge.Svm.Runtime.CpiWord.accKey || endsWith e ".accKey" then
    if e.getAppArgs.size ≥ 1 then
      match val env e.getAppArgs[e.getAppArgs.size - 1]! >>= natOfVal with
      | some i => some (.accKey i)
      | none => none
    else none
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
  if isConstNamed e ``ProofForge.Svm.Runtime.invokeSigned || endsWith e ".invokeSigned" then
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
  else if isConstNamed e ``ProofForge.Svm.Runtime.invoke || endsWith e ".invoke" then
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
            if n.getRoot != `ProofForge then none
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
      mentionsRuntime e "createPda" ||
      mentionsRuntime e "systemAssign" ||
      mentionsRuntime e "systemAllocate" ||
      mentionsRuntime e "systemAllocateWithSeed" ||
      mentionsRuntime e "systemCreateWithSeed" ||
      mentionsRuntime e "systemAssignWithSeed" ||
      mentionsRuntime e "systemTransferWithSeed" ||
      mentionsRuntime e "tokenInitMint" ||
      mentionsRuntime e "tokenSyncNative" ||
      mentionsRuntime e "tokenTransferChecked" ||
      mentionsRuntime e "tokenMintToChecked" ||
      mentionsRuntime e "tokenBurnChecked" ||
      mentionsRuntime e "tokenInitAccount" ||
      mentionsRuntime e "tokenCloseAccount" ||
      mentionsRuntime e "tokenApproveChecked" ||
      mentionsRuntime e "tokenFreezeAccount" ||
      mentionsRuntime e "tokenThawAccount" ||
      mentionsRuntime e "tokenSetMintAuthority" ||
      mentionsRuntime e "tokenSetAccountAuthority" ||
      mentionsRuntime e "tokenApprove" ||
      mentionsRuntime e "tokenInitMultisig" ||
      mentionsRuntime e "systemAdvanceNonce" ||
      mentionsRuntime e "tokenRevoke" ||
      mentionsRuntime e "tokenAccountSize" ||
      mentionsRuntime e "memoWrite" ||
      mentionsRuntime e "ataCreateIdempotent" then
    go fuel e
  else none

private def invokeOps
    (inv : Nat × Array Ops.CpiMeta × Array Ops.CpiWord × Option String × Option Ops.Val)
    (ret : Ops.Val) : Array Ops.Op :=
  let (prog, metas, data, seed, bump) := inv
  #[.invoke prog metas data seed bump, .returnU64 ret]

private def invokeOp
    (inv : Nat × Array Ops.CpiMeta × Array Ops.CpiWord × Option String × Option Ops.Val) :
    Ops.Op :=
  let (prog, metas, data, seed, bump) := inv
  .invoke prog metas data seed bump

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
        | .letE _ _ value body _ => go fuel' (body.instantiate1 value)
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
  | (2, _, #[.u32le 0, .u64le amount, .u64le _, .programId], some _, some _) => amount
  | (1, _, #[.u32le 1, .programId], none, none) => .lit 0
  | (1, _, #[.u32le 8, .u64le space], none, none) => space
  | (2, _, #[.u32le 9, .accKey 0, .u64le _, .ascii "vault", .u64le space, .programId], none, none) => space
  | (2, _, #[.u32le 3, .accKey 0, .u64le _, .ascii "vault", .u64le lamports, .u64le _, .programId], none, none) => lamports
  | (2, _, #[.u32le 10, .accKey 0, .u64le _, .ascii "vault", .programId], none, none) => .lit 0
  | (3, _, #[.u32le 11, .u64le lamports, .u64le _, .ascii "vault", .programId], none, none) => lamports
  | (2, _, #[.u8le 20, .u8le 6, .accKey 0, .u8le 0], none, none) => .lit 0
  | (2, _, #[.u8le 17], none, none) => .lit 0
  | (4, _, #[.u8le 12, .u64le amount, .u8le _], none, none) => amount
  | (3, _, #[.u8le 14, .u64le amount, .u8le _], none, none) => amount
  | (3, _, #[.u8le 15, .u64le amount, .u8le _], none, none) => amount
  | (3, _, #[.u8le 18, .accKey 0], none, none) => .lit 0
  | (3, _, #[.u8le 9], none, none) => .lit 0
  | (4, _, #[.u8le 13, .u64le amount, .u8le _], none, none) => amount
  | (3, _, #[.u8le 10], none, none) => .lit 0
  | (3, _, #[.u8le 11], none, none) => .lit 0
  | (3, _, #[.u8le 6, .u8le 0, .u8le 1, .accKey 2], none, none) => .lit 0
  | (3, _, #[.u8le 5], none, none) => .lit 0
  | (2, _, #[.u8le 21], none, none) => .cpiReturn
  | (1, _, #[.ascii "ok"], none, none) => .lit 0
  | (6, _, #[.u8le 1], none, none) => .lit 0
  | _ => .lit 0

private def forRangeEnd (e : Expr) : Option Nat :=
  let rec rangeEnd (fuel : Nat) (e : Expr) : Option Nat :=
    match fuel with
    | 0 => none
    | fuel' + 1 =>
      let e := strip e
      if endsWith e ".mk" || e.getAppFn.constName?.isSome then
        let rargs := e.getAppArgs
        if rargs.size ≥ 2 then
          match asLit 8 rargs[1]! with
          | some (.lit n) => some n.toNat
          | _ => rargs.findSome? (rangeEnd fuel')
        else rargs.findSome? (rangeEnd fuel')
      else e.getAppArgs.findSome? (rangeEnd fuel')
  rangeEnd 8 e

/-- `forAccum` / `forBody`：下标位的 `.arg` 是循环变量。不要改 payload。 -/
private def rewriteLoopIx (v : Ops.Val) : Ops.Val :=
  let rec go (fuel : Nat) (v : Ops.Val) : Ops.Val :=
    match fuel with
    | 0 => v
    | fuel' + 1 =>
      match v with
      | .indexGet b n i k off =>
          .indexGet b n (go fuel' i) k off
      | .arg 1 => .loopIx
      | .field b n => .field (go fuel' b) n
      | .bitAnd l r => .bitAnd (go fuel' l) (go fuel' r)
      | .bitOr l r => .bitOr (go fuel' l) (go fuel' r)
      | .bitXor l r => .bitXor (go fuel' l) (go fuel' r)
      | .bitNot v => .bitNot (go fuel' v)
      | .shiftL l r => .shiftL (go fuel' l) (go fuel' r)
      | .shiftR l r => .shiftR (go fuel' l) (go fuel' r)
      | .addU64 l r => .addU64 (go fuel' l) (go fuel' r)
      | .subU64 l r => .subU64 (go fuel' l) (go fuel' r)
      | .mulU64 l r => .mulU64 (go fuel' l) (go fuel' r)
      | .divU64 l r => .divU64 (go fuel' l) (go fuel' r)
      | .modU64 l r => .modU64 (go fuel' l) (go fuel' r)
      | v => v
  go 8 v

private def rewriteLoopOp (op : Ops.Op) : Ops.Op :=
  let rec go (fuel : Nat) (op : Ops.Op) : Ops.Op :=
    match fuel with
    | 0 => op
    | fuel' + 1 =>
      match op with
      | .checkedAddU64 l r => .checkedAddU64 (rewriteLoopIx l) (rewriteLoopIx r)
      | .checkedSubU64 l r => .checkedSubU64 (rewriteLoopIx l) (rewriteLoopIx r)
      | .checkedMulU64 l r => .checkedMulU64 (rewriteLoopIx l) (rewriteLoopIx r)
      | .checkedDivU64 l r => .checkedDivU64 (rewriteLoopIx l) (rewriteLoopIx r)
      | .checkedModU64 l r => .checkedModU64 (rewriteLoopIx l) (rewriteLoopIx r)
      | .ite c l r t f =>
          .ite c (rewriteLoopIx l) (rewriteLoopIx r) (t.map (go fuel')) (f.map (go fuel'))
      | .invoke prog metas data seed bump =>
          .invoke prog metas (data.map fun
            | .u64le v => .u64le (rewriteLoopIx v)
            | w => w) seed (bump.map rewriteLoopIx)
      | .indexSet n i v k off =>
          .indexSet n (rewriteLoopIx i) (rewriteLoopIx v) k off
      | .storeField n v => .storeField n (rewriteLoopIx v)
      | .okState v => .okState (rewriteLoopIx v)
      | .returnU64 v => .returnU64 (rewriteLoopIx v)
      | .returnState _ => .errorOverflow
      | .forAccum n v => .forAccum n (rewriteLoopIx v)
      | .forBody n body => .forBody n (body.map (go fuel'))
      | op => op
  go 8 op

/--
普通 accumulator / early-return 循环沿用原来的 callback 归一化：账户参数落到
`.arg 0`，动态索引就是 `loopIx`，而 `indexSet` payload 仍是外层方法参数。
State-carrying loop 不能用这条宽松规则，继续走上面的精确 binder 重写。
-/
private def rewritePlainLoopIx (v : Ops.Val) : Ops.Val :=
  let rec go (fuel : Nat) (v : Ops.Val) : Ops.Val :=
    match fuel with
    | 0 => v
    | fuel' + 1 =>
      match v with
      | .indexGet b n i k off =>
          let b' := match b with | .arg _ => .arg 0 | _ => go fuel' b
          let i' := match i with | .lit _ => i | _ => .loopIx
          .indexGet b' n i' k off
      | .field b n => .field (go fuel' b) n
      | .bitAnd l r => .bitAnd (go fuel' l) (go fuel' r)
      | .bitOr l r => .bitOr (go fuel' l) (go fuel' r)
      | .bitXor l r => .bitXor (go fuel' l) (go fuel' r)
      | .bitNot x => .bitNot (go fuel' x)
      | .shiftL l r => .shiftL (go fuel' l) (go fuel' r)
      | .shiftR l r => .shiftR (go fuel' l) (go fuel' r)
      | .addU64 l r => .addU64 (go fuel' l) (go fuel' r)
      | .subU64 l r => .subU64 (go fuel' l) (go fuel' r)
      | .mulU64 l r => .mulU64 (go fuel' l) (go fuel' r)
      | .divU64 l r => .divU64 (go fuel' l) (go fuel' r)
      | .modU64 l r => .modU64 (go fuel' l) (go fuel' r)
      | v => v
  go 8 v

private def rewritePlainLoopOp (op : Ops.Op) : Ops.Op :=
  let rec go (fuel : Nat) (op : Ops.Op) : Ops.Op :=
    match fuel with
    | 0 => op
    | fuel' + 1 =>
      let rv := rewritePlainLoopIx
      match op with
      | .checkedAddU64 l r => .checkedAddU64 (rv l) (rv r)
      | .checkedSubU64 l r => .checkedSubU64 (rv l) (rv r)
      | .checkedMulU64 l r => .checkedMulU64 (rv l) (rv r)
      | .checkedDivU64 l r => .checkedDivU64 (rv l) (rv r)
      | .checkedModU64 l r => .checkedModU64 (rv l) (rv r)
      | .ite c l r t f =>
          let l' := match l with | .arg _ => .loopIx | _ => rv l
          let r' := match r with | .arg _ => .loopIx | _ => rv r
          .ite c l' r' (t.map (go fuel')) (f.map (go fuel'))
      | .invoke prog metas data seed bump =>
          .invoke prog metas (data.map fun | .u64le v => .u64le (rv v) | w => w)
            seed (bump.map rv)
      | .indexSet n i v k off =>
          let i' := match i with | .lit _ => i | _ => .loopIx
          let v' := match v with | .arg _ => .arg 0 | _ => v
          .indexSet n i' v' k off
      | .storeField n v => .storeField n v
      | .okState v => .okState (match v with | .arg _ => .arg 0 | _ => v)
      | .returnU64 v => .returnU64 (rv v)
      | .returnState _ => .errorOverflow
      | .forAccum n v => .forAccum n (rv v)
      | .forBody n body => .forBody n (body.map (go fuel'))
      | op => op
  go 8 op

private def findForIn (env : Environment) (e : Expr) : Option (Nat × Ops.Val) :=
  let rec go (fuel : Nat) (e : Expr) : Option (Nat × Ops.Val) :=
    match fuel with
    | 0 => none
    | fuel' + 1 =>
      let e := e.consumeMData
      if e.getAppFn.constName? == some ``Id.run || endsWith e ".run" then
        if e.getAppArgs.size ≥ 1 then go fuel' e.getAppArgs[e.getAppArgs.size - 1]!
        else none
      else if e.getAppFn.constName? == some ``ForIn.forIn || endsWith e ".forIn" then
        let args := e.getAppArgs
        let n? := args.findSome? forRangeEnd
        let rec findAdd (fuel : Nat) (e : Expr) : Option Ops.Val :=
          match fuel with
          | 0 => none
          | fuel' + 1 =>
            let e := strip e
            if isConstNamed e ``HAdd.hAdd && e.getAppArgs.size ≥ 2 then
              (asVal env 8 e.getAppArgs[e.getAppArgs.size - 1]!).map rewritePlainLoopIx
            else
              match e with
              | .lam _ _ body _ => findAdd fuel' body
              | .letE _ _ value body _ => findAdd fuel' value <|> findAdd fuel' body
              | _ => e.getAppArgs.findSome? (findAdd fuel')
        let addend? := args.findSome? (findAdd 16)
        match n?, addend? with
        | some n, some v =>
          if n = 0 || n > 64 then none else some (n, v)
        | _, _ => none
      else
        match e with
        | .letE _ _ value body _ => go fuel' value <|> go fuel' body
        | .lam _ _ body _ => go fuel' body
        | .app f a => go fuel' f <|> go fuel' a
        | _ => none
  go 16 e

/-- `for i in [:n]` 里 `ForInStep.done` 提前返回。累加仍走 `findForIn`。 -/
private def findForBodyExpr (env : Environment) (e : Expr) : Option (Nat × Expr) :=
  let rec go (fuel : Nat) (e : Expr) : Option (Nat × Expr) :=
    match fuel with
    | 0 => none
    | fuel' + 1 =>
      let e := e.consumeMData
      if e.getAppFn.constName? == some ``Id.run || endsWith e ".run" then
        if e.getAppArgs.size ≥ 1 then go fuel' e.getAppArgs[e.getAppArgs.size - 1]!
        else none
      else if e.getAppFn.constName? == some ``ForIn.forIn || endsWith e ".forIn" then
        if (findForIn env e).isSome then none
        else
          let args := e.getAppArgs
          let n? := args.findSome? forRangeEnd
          -- `forIn xs init (fun i r => body)`：最后一个 λ 是循环体。
          let rec lastLam (fuel : Nat) (e : Expr) : Option Expr :=
            match fuel with
            | 0 => none
            | fuel' + 1 =>
              match strip e with
              | .lam _ _ body _ =>
                match strip body with
                | .lam _ _ body2 _ => some (peelLets body2)
                | _ => some (peelLets body)
              | .letE _ _ _ body _ => lastLam fuel' body
              | e => e.getAppArgs.findSome? (lastLam fuel')
          let bodyE? :=
            if args.size > 0 then lastLam 8 args[args.size - 1]! else none
          match n?, bodyE? with
          | some n, some bodyE =>
            if n = 0 || n > 64 then none else some (n, bodyE)
          | _, _ => none
      else
        match e with
        | .letE _ _ value body _ => go fuel' value <|> go fuel' body
        | .lam _ _ body _ => go fuel' body
        | .app f a => go fuel' f <|> go fuel' a
        | _ => none
  go 16 e

/--
`do let mut st := s; for ... do st := ...; k st` 的 loop body 与 continuation。
真正是否为 state-carrying loop 由 body 解码出的显式 store 判定；普通 early-return
`forBody` 继续走旧路径。
-/
private def findForStateExpr (_env : Environment) (e : Expr) : Option (Nat × Expr × Expr) :=
  let rec findForExpr (fuel : Nat) (e : Expr) : Option Expr :=
    match fuel with
    | 0 => none
    | fuel' + 1 =>
      let e := strip e
      if e.getAppFn.constName? == some ``ForIn.forIn || endsWith e ".forIn" then some e
      else
        match e with
        | .letE _ _ value body _ => findForExpr fuel' value <|> findForExpr fuel' body
        | .lam _ _ body _ => findForExpr fuel' body
        | _ => e.getAppArgs.findSome? (findForExpr fuel')
  let loopParts? := do
    let forExpr ← findForExpr 32 e
    let n ← forExpr.getAppArgs.findSome? forRangeEnd
    let rec lastLam (fuel : Nat) (e : Expr) : Option Expr :=
      match fuel with
      | 0 => none
      | fuel' + 1 =>
        match strip e with
        | .lam _ _ body _ =>
          match strip body with
          | .lam _ _ body2 _ => some (substLets 128 body2)
          | _ => some (substLets 128 body)
        | .letE _ _ _ body _ => lastLam fuel' body
        | e => e.getAppArgs.findSome? (lastLam fuel')
    let args := forExpr.getAppArgs
    if args.size < 2 then none else
    -- State-carrying `for` starts from the mutable state binder itself. Early-return loops
    -- use an `MProd (Option result) PUnit` constructor accumulator and stay on the legacy path.
    match strip args[args.size - 2]! with
    | .bvar _ => pure ()
    | _ => none
    let body ← if h : args.size > 0 then lastLam 16 args[args.size - 1] else none
    if n = 0 || n > 64 then none else some (n, body)
  let rec findContinuation (fuel : Nat) (e : Expr) : Option Expr :=
    match fuel with
    | 0 => none
    | fuel' + 1 =>
      let e := strip e
      if e.getAppFn.constName? == some ``Id.run || endsWith e ".run" then
        if e.getAppArgs.size ≥ 1 then
          findContinuation fuel' e.getAppArgs[e.getAppArgs.size - 1]!
        else none
      else
        match e with
        | .letE _ _ value body _ => findContinuation fuel' (body.instantiate1 value)
        | _ =>
          if e.getAppFn.constName? == some ``Bind.bind || endsWith e ".bind" then
            let args := e.getAppArgs
            if args.any fun a => (findForExpr 16 a).isSome then
              match args.findRev? fun a => match strip a with | .lam .. => true | _ => false with
              | some continuation =>
                match strip continuation with
                | .lam _ _ continuationBody _ =>
                  some (peelControl 16 (substLets 128 continuationBody))
                | _ => none
              | none => none
            else args.findSome? (findContinuation fuel')
          else
            e.getAppArgs.findSome? (findContinuation fuel')
  match loopParts?, findContinuation 32 e with
  | some (n, bodyE), some continuation => some (n, bodyE, continuation)
  | _, _ => none

/-- 收集 `xs.set … .set …` 整条链。先外层（旧向量），后内层（新写）。
一次 `set` 可以改多叶（`left` + `parent`）。 -/
private def collectIndexSets (env : Environment) (e : Expr) : Array Ops.Op :=
  let rec go (fuel : Nat) (e : Expr) (acc : Array Ops.Op) : Array Ops.Op :=
    match fuel with
    | 0 => acc
    | fuel' + 1 =>
      let e := strip e
      match e with
      | .letE _ _ value body _ => go fuel' (body.instantiate1 value) acc
      | .lam _ _ body _ => go fuel' body acc
      | _ =>
        if isConstNamed e ``Except.ok && e.getAppArgs.size ≥ 1 then
          go fuel' e.getAppArgs[e.getAppArgs.size - 1]! acc
        else if isConstNamed e ``Prod.mk && e.getAppArgs.size ≥ 2 then
          go fuel' e.getAppArgs[e.getAppArgs.size - 2]! acc
        else if isVectorSet e then
          -- `Vector.set α n xs i v h`：只沿 xs 追溯旧写。payload/下标里的
          -- vector reads 不是写；遍历全部参数会把旧链指数级重复收集。
          let args := e.getAppArgs
          let acc :=
            if h : args.size ≥ 4 then go fuel' args[args.size - 4] acc else acc
          match asIndexSets env e with
          | some ops => acc ++ ops
          | none => acc
        else
          e.getAppArgs.foldl (init := acc) fun a x => go fuel' x a
  go 16 e #[]

private def findIndexSet (env : Environment) (e : Expr) : Option Ops.Op :=
  (collectIndexSets env e)[0]?

private def findRuntimeApp (fuel : Nat) (e : Expr) (want : Name) (suffix : String) :
    Option Expr :=
  let rec go (fuel : Nat) (e : Expr) : Option Expr :=
    match fuel with
    | 0 => none
    | fuel' + 1 =>
      let e := e.consumeMData
      if e.getAppFn.constName? == some want || endsWith e suffix then
        some e
      else
        match e with
        | .letE _ _ value body _ => go fuel' value <|> go fuel' body
        | .lam _ _ body _ => go fuel' body
        | .app f a => go fuel' f <|> go fuel' a
        | _ => none
  go fuel e

private def findUnaryRuntime (env : Environment) (want : Name) (suffix : String)
    (e : Expr) : Option Ops.Val :=
  if mentionsRuntime e suffix then
    match findRuntimeApp 16 e want suffix with
    | some app =>
      if app.getAppArgs.size ≥ 1 then
        match val env app.getAppArgs[app.getAppArgs.size - 1]! with
        | some v => some v
        | none => some (.arg 0)
      else some (.arg 0)
    | none => some (.arg 0)
  else none

private def nthFromEnd (args : Array Expr) (n : Nat) : Option Expr :=
  if args.size ≥ n + 1 then some args[args.size - 1 - n]! else none

private def valAtEnd (env : Environment) (args : Array Expr) (n : Nat) : Ops.Val :=
  match nthFromEnd args n with
  | some e => (val env e).getD (.arg n)
  | none => .arg n

private def findEvmDeposit (env : Environment) (e : Expr) : Option Ops.Val :=
  findUnaryRuntime env ``ProofForge.Evm.Runtime.evmDeposit ".evmDeposit" e

private def findEvmLogTipped (env : Environment) (e : Expr) : Option Ops.Val :=
  findUnaryRuntime env ``ProofForge.Evm.Runtime.evmLogTipped ".evmLogTipped" e

private def findEvmLogIncremented (env : Environment) (e : Expr) : Option Ops.Val :=
  findUnaryRuntime env ``ProofForge.Evm.Runtime.evmLogIncremented ".evmLogIncremented" e

private def findEvmLogTransfer (env : Environment) (e : Expr) : Option Ops.Val :=
  findUnaryRuntime env ``ProofForge.Evm.Runtime.evmLogTransfer ".evmLogTransfer" e

private def findEvmLogApproval (env : Environment) (e : Expr) : Option Ops.Val :=
  findUnaryRuntime env ``ProofForge.Evm.Runtime.evmLogApproval ".evmLogApproval" e

private def findEvmSendEth (env : Environment) (e : Expr) :
    Option (Ops.Val × Ops.Val × Ops.Val × Ops.Val) :=
  if mentionsRuntime e "evmSendEth" then
    match findRuntimeApp 16 e ``ProofForge.Evm.Runtime.evmSendEth ".evmSendEth" with
    | some app =>
      let args := app.getAppArgs
      some (valAtEnd env args 3, valAtEnd env args 2, valAtEnd env args 1, valAtEnd env args 0)
    | none => some (.arg 0, .arg 1, .arg 2, .arg 3)
  else none

private def findBinaryRuntime (env : Environment) (want : Name) (suffix : String)
    (e : Expr) : Option (Ops.Val × Ops.Val) :=
  if mentionsRuntime e suffix then
    match findRuntimeApp 16 e want suffix with
    | some app =>
      let args := app.getAppArgs
      if args.size ≥ 2 then some (valAtEnd env args 1, valAtEnd env args 0)
      else some (.arg 0, .arg 1)
    | none => some (.arg 0, .arg 1)
  else none

private def findTernaryRuntime (env : Environment) (want : Name) (suffix : String)
    (e : Expr) : Option (Ops.Val × Ops.Val × Ops.Val) :=
  if mentionsRuntime e suffix then
    match findRuntimeApp 16 e want suffix with
    | some app =>
      let args := app.getAppArgs
      if args.size ≥ 3 then
        some (valAtEnd env args 2, valAtEnd env args 1, valAtEnd env args 0)
      else some (.arg 0, .arg 1, .arg 2)
    | none => some (.arg 0, .arg 1, .arg 2)
  else none

private def findEvmMapGetU64 (env : Environment) (e : Expr) :
    Option (Ops.Val × Ops.Val) :=
  findBinaryRuntime env ``ProofForge.Evm.Runtime.evmMapGetU64 ".evmMapGetU64" e

private def findEvmMapSetU64 (env : Environment) (e : Expr) :
    Option (Ops.Val × Ops.Val × Ops.Val) :=
  findTernaryRuntime env ``ProofForge.Evm.Runtime.evmMapSetU64 ".evmMapSetU64" e

private def findEvmMapGetAddr (env : Environment) (e : Expr) :
    Option (Ops.Val × Ops.Val × Ops.Val × Ops.Val) :=
  if mentionsRuntime e "evmMapGetAddr" then
    match findRuntimeApp 16 e ``ProofForge.Evm.Runtime.evmMapGetAddr ".evmMapGetAddr" with
    | some app =>
      let args := app.getAppArgs
      some (valAtEnd env args 3, valAtEnd env args 2, valAtEnd env args 1, valAtEnd env args 0)
    | none => some (.arg 0, .arg 1, .arg 2, .arg 3)
  else none

private def findEvmMapSetAddr (env : Environment) (e : Expr) :
    Option (Ops.Val × Ops.Val × Ops.Val × Ops.Val × Ops.Val) :=
  if mentionsRuntime e "evmMapSetAddr" then
    match findRuntimeApp 16 e ``ProofForge.Evm.Runtime.evmMapSetAddr ".evmMapSetAddr" with
    | some app =>
      let args := app.getAppArgs
      some (valAtEnd env args 4, valAtEnd env args 3, valAtEnd env args 2,
        valAtEnd env args 1, valAtEnd env args 0)
    | none => some (.arg 0, .arg 1, .arg 2, .arg 3, .arg 4)
  else none

private def findEvmMapGetPair (env : Environment) (e : Expr) :
    Option (Ops.Val × Ops.Val × Ops.Val × Ops.Val × Ops.Val × Ops.Val × Ops.Val) :=
  if mentionsRuntime e "evmMapGetPair" then
    match findRuntimeApp 16 e ``ProofForge.Evm.Runtime.evmMapGetPair ".evmMapGetPair" with
    | some app =>
      let args := app.getAppArgs
      some (valAtEnd env args 6, valAtEnd env args 5, valAtEnd env args 4,
        valAtEnd env args 3, valAtEnd env args 2, valAtEnd env args 1, valAtEnd env args 0)
    | none => some (.arg 0, .arg 1, .arg 2, .arg 3, .arg 4, .arg 5, .arg 6)
  else none

private def findEvmMapSetPair (env : Environment) (e : Expr) :
    Option (Ops.Val × Ops.Val × Ops.Val × Ops.Val × Ops.Val × Ops.Val × Ops.Val × Ops.Val) :=
  if mentionsRuntime e "evmMapSetPair" then
    match findRuntimeApp 16 e ``ProofForge.Evm.Runtime.evmMapSetPair ".evmMapSetPair" with
    | some app =>
      let args := app.getAppArgs
      some (valAtEnd env args 7, valAtEnd env args 6, valAtEnd env args 5,
        valAtEnd env args 4, valAtEnd env args 3, valAtEnd env args 2,
        valAtEnd env args 1, valAtEnd env args 0)
    | none => some (.arg 0, .arg 1, .arg 2, .arg 3, .arg 4, .arg 5, .arg 6, .arg 7)
  else none

private def findEvmTokenTransfer (env : Environment) (e : Expr) :
    Option (Ops.Val × Ops.Val × Ops.Val × Ops.Val × Ops.Val × Ops.Val × Ops.Val) :=
  if mentionsRuntime e "evmTokenTransfer" then
    match findRuntimeApp 16 e ``ProofForge.Evm.Runtime.evmTokenTransfer ".evmTokenTransfer" with
    | some app =>
      let args := app.getAppArgs
      some (valAtEnd env args 6, valAtEnd env args 5, valAtEnd env args 4,
        valAtEnd env args 3, valAtEnd env args 2, valAtEnd env args 1, valAtEnd env args 0)
    | none => some (.arg 0, .arg 1, .arg 2, .arg 3, .arg 4, .arg 5, .arg 6)
  else none

private def findEvmTokenBalance (env : Environment) (e : Expr) :
    Option (Ops.Val × Ops.Val × Ops.Val) :=
  findTernaryRuntime env ``ProofForge.Evm.Runtime.evmTokenBalanceOfSelf
    ".evmTokenBalanceOfSelf" e

private def opOfRuntimeApp (env : Environment) (app : Expr) : Option Ops.Op :=
  let args := app.getAppArgs
  if isConstNamed app ``ProofForge.Evm.Runtime.evmDeposit || endsWith app ".evmDeposit" then
    some (.evmDeposit (valAtEnd env args 0))
  else if isConstNamed app ``ProofForge.Evm.Runtime.evmSendEth || endsWith app ".evmSendEth" then
    some (.evmSendEth (valAtEnd env args 3) (valAtEnd env args 2)
      (valAtEnd env args 1) (valAtEnd env args 0))
  else if isConstNamed app ``ProofForge.Evm.Runtime.evmLogTipped || endsWith app ".evmLogTipped" then
    some (.evmLog "Tipped" (valAtEnd env args 0))
  else if isConstNamed app ``ProofForge.Evm.Runtime.evmLogIncremented ||
      endsWith app ".evmLogIncremented" then
    some (.evmLog "Incremented" (valAtEnd env args 0))
  else if isConstNamed app ``ProofForge.Evm.Runtime.evmLogTransfer ||
      endsWith app ".evmLogTransfer" then
    some (.evmLog "Transfer" (valAtEnd env args 0))
  else if isConstNamed app ``ProofForge.Evm.Runtime.evmLogApproval ||
      endsWith app ".evmLogApproval" then
    some (.evmLog "Approval" (valAtEnd env args 0))
  else if isConstNamed app ``ProofForge.Evm.Runtime.evmMapSetU64 || endsWith app ".evmMapSetU64" then
    some (.mapSetU64 (valAtEnd env args 2) (valAtEnd env args 1) (valAtEnd env args 0))
  else if isConstNamed app ``ProofForge.Evm.Runtime.evmMapSetAddr || endsWith app ".evmMapSetAddr" then
    some (.mapSetAddr (valAtEnd env args 4) (valAtEnd env args 3) (valAtEnd env args 2)
      (valAtEnd env args 1) (valAtEnd env args 0))
  else if isConstNamed app ``ProofForge.Evm.Runtime.evmMapSetPair || endsWith app ".evmMapSetPair" then
    some (.mapSetPair (valAtEnd env args 7) (valAtEnd env args 6) (valAtEnd env args 5)
      (valAtEnd env args 4) (valAtEnd env args 3) (valAtEnd env args 2)
      (valAtEnd env args 1) (valAtEnd env args 0))
  else if isConstNamed app ``ProofForge.Evm.Runtime.evmTokenTransfer ||
      endsWith app ".evmTokenTransfer" then
    some (.evmTokenTransfer (valAtEnd env args 6) (valAtEnd env args 5) (valAtEnd env args 4)
      (valAtEnd env args 3) (valAtEnd env args 2) (valAtEnd env args 1) (valAtEnd env args 0))
  else none

private def collectEvmEffectOps (env : Environment) (e : Expr) : Array Ops.Op :=
  let specs : Array (Name × String) := #[
    (``ProofForge.Evm.Runtime.evmDeposit, ".evmDeposit"),
    (``ProofForge.Evm.Runtime.evmSendEth, ".evmSendEth"),
    (``ProofForge.Evm.Runtime.evmLogTipped, ".evmLogTipped"),
    (``ProofForge.Evm.Runtime.evmLogIncremented, ".evmLogIncremented"),
    (``ProofForge.Evm.Runtime.evmLogTransfer, ".evmLogTransfer"),
    (``ProofForge.Evm.Runtime.evmLogApproval, ".evmLogApproval"),
    (``ProofForge.Evm.Runtime.evmMapSetU64, ".evmMapSetU64"),
    (``ProofForge.Evm.Runtime.evmMapSetAddr, ".evmMapSetAddr"),
    (``ProofForge.Evm.Runtime.evmMapSetPair, ".evmMapSetPair"),
    (``ProofForge.Evm.Runtime.evmTokenTransfer, ".evmTokenTransfer")
  ]
  let rec walk (fuel : Nat) (e : Expr) (acc : Array Ops.Op) : Array Ops.Op :=
    match fuel with
    | 0 => acc
    | fuel' + 1 =>
      let e := e.consumeMData
      if specs.any (fun (want, suf) =>
          e.getAppFn.constName? == some want || endsWith e suf) then
        match opOfRuntimeApp env e with
        | some op => acc.push op
        | none => acc
      else
        match e with
        | .letE _ _ value body _ => walk fuel' body (walk fuel' value acc)
        | .lam _ _ body _ => walk fuel' body acc
        | .app f a => walk fuel' a (walk fuel' f acc)
        | _ => acc
  walk 24 e #[]

private def retOfEvmOps (ops : Array Ops.Op) : Ops.Val :=
  match ops.back? with
  | some (.evmDeposit v) => v
  | some (.evmSendEth _ _ _ v) => v
  | some (.evmLog _ v) => v
  | some (.mapSetU64 _ _ v) => v
  | some (.mapSetAddr _ _ _ _ v) => v
  | some (.mapSetPair _ _ _ _ _ _ _ v) => v
  | some (.evmTokenTransfer _ _ _ _ _ _ v) => v
  | _ => .arg 0

private def decodeEvmEffect (env : Environment) (e : Expr) : Option (Array Ops.Op) :=
  let writes := collectEvmEffectOps env e
  if writes.size ≥ 1 then
    some (writes.push (.returnU64 (retOfEvmOps writes)))
  else if let some amount := findEvmDeposit env e then
    some #[.evmDeposit amount, .returnU64 amount]
  else if let some (w0, w1, w2, amt) := findEvmSendEth env e then
    some #[.evmSendEth w0 w1 w2 amt, .returnU64 amt]
  else if let some amount := findEvmLogTipped env e then
    some #[.evmLog "Tipped" amount, .returnU64 amount]
  else if let some amount := findEvmLogIncremented env e then
    some #[.evmLog "Incremented" amount, .returnU64 amount]
  else if let some amount := findEvmLogTransfer env e then
    some #[.evmLog "Transfer" amount, .returnU64 amount]
  else if let some amount := findEvmLogApproval env e then
    some #[.evmLog "Approval" amount, .returnU64 amount]
  else if let some (b, k, v) := findEvmMapSetU64 env e then
    some #[.mapSetU64 b k v, .returnU64 v]
  else if let some (b, a0, a1, a2, v) := findEvmMapSetAddr env e then
    some #[.mapSetAddr b a0 a1 a2 v, .returnU64 v]
  else if let some (b, o0, o1, o2, s0, s1, s2, v) := findEvmMapSetPair env e then
    some #[.mapSetPair b o0 o1 o2 s0 s1 s2 v, .returnU64 v]
  else if let some (t0, t1, t2, d0, d1, d2, amt) := findEvmTokenTransfer env e then
    some #[.evmTokenTransfer t0 t1 t2 d0 d1 d2 amt, .returnU64 amt]
  else if let some (b, k) := findEvmMapGetU64 env e then
    some #[.mapGetU64 b k, .returnU64 k]
  else if let some (b, a0, a1, a2) := findEvmMapGetAddr env e then
    some #[.mapGetAddr b a0 a1 a2, .returnU64 a0]
  else if let some (b, o0, o1, o2, s0, s1, s2) := findEvmMapGetPair env e then
    some #[.mapGetPair b o0 o1 o2 s0 s1 s2, .returnU64 o0]
  else if let some (t0, t1, t2) := findEvmTokenBalance env e then
    some #[.evmTokenBalanceOfSelf t0 t1 t2, .returnU64 t0]
  else none

/-- A vector root is not a scalar slot. Mixed static/dynamic writeback can see an inline
helper's vector parameter as a changed structure field; discard that synthetic root store. -/
private def dropVectorRootStores (dynamic stores : Array Ops.Op) : Array Ops.Op :=
  let vectorNames := dynamic.filterMap fun
    | .indexSet name _ _ _ _ => some name
    | _ => none
  stores.filter fun
    | .storeField name _ => !vectorNames.contains name
    | _ => true

/-- Zeta-reduce syntax-only aliases at the head of an expression.
Compiler intrinsics and loops stay explicit so later effect/control decoding still sees them. -/
private def zetaPureHeadLets (env : Environment) (fuel : Nat) (e : Expr) : Expr :=
  match fuel with
  | 0 => e
  | fuel' + 1 =>
    match strip e with
    | .letE _ _ value body _ =>
        let effectful :=
          (findInvoke env 16 value).isSome || (decodeEvmEffect env value).isSome ||
            (findForIn env value).isSome || (findForBodyExpr env value).isSome
        let directAlias := match strip body with | .bvar 0 => true | _ => false
        if effectful || (!directAlias && !isIteExpr body) then e
        else zetaPureHeadLets env fuel' (body.instantiate1 value)
    | e => e

/--
Profile 已检查过且显式标记的用户 helper 在控制流边界按需 β 展开。这个边界
让有界合约能把匹配和结算步骤拆成具名函数，而不要求某个后端认识合约名字。
-/
private def unfoldUserHelper (env : Environment) (e : Expr) : Option (Name × Expr) :=
  let e := strip e
  let args := e.getAppArgs
  match e.getAppFn.constName? with
  | none => none
  | some n =>
    if Attr.isInline env n then
      match env.find? n with
      | some (.defnInfo info) => some (n, info.value.beta args)
      | _ => none
    else none

private def findYieldPayload (e : Expr) : Option Expr :=
  let rec go (fuel : Nat) (e : Expr) : Option Expr :=
    match fuel with
    | 0 => none
    | fuel' + 1 =>
      let e := strip e
      if isConstNamed e ``ForInStep.yield || endsWith e ".yield" then
        if e.getAppArgs.size ≥ 1 then
          -- The payload remains under the yielded state/control binder. Keep accumulator 0,
          -- and lower the loop index plus outer method arguments back to callback scope.
          some (e.getAppArgs[e.getAppArgs.size - 1]!.lowerLooseBVars 1 1)
        else none
      else
        match e with
        | .letE _ _ value body _ => go fuel' body <|> go fuel' value
        -- Yield can sit under a dependent branch proof lambda. Dropping that binder without
        -- lowering would turn the loop index and outer arguments into unrelated `.arg`s.
        | .lam _ _ body _ => go fuel' (body.lowerLooseBVars 1 1)
        | _ => e.getAppArgs.findSome? (go fuel')
  go 32 e

/-- State loop 的 `yield newState` 只写账户并继续，不生成 commit/exit。 -/
private def asYieldStores (env : Environment) (e : Expr) : Option (Array Ops.Op) :=
  match findYieldPayload e with
  | none => none
  | some state =>
    let dynamic := collectIndexSets env state
    let static := (flattenLeaves env "" state).map fun p => Ops.Op.storeField p.1 p.2
    some (dynamic ++ static)

private def decodePlain (env : Environment) (e : Expr) : Except String (Array Ops.Op) :=
  -- 必须在 peelLets 之前找效应：剥掉 `have sent := …` 后调用就没了。
  if let some inv := findInvoke env 16 e then
    .ok (invokeOps inv (invokeRet env e inv))
  else if let some ops := decodeEvmEffect env e then
    .ok ops
  else if let some (n, addend) := findForIn env e then
    .ok #[.forAccum n addend, .returnU64 addend]
  else if let some stores := asYieldStores env e then
    .ok stores
  else
  let isets := collectIndexSets env e
  if isets.size ≥ 1 then
    match asStoreFields env e true with
    | some stores => .ok (isets ++ dropVectorRootStores isets stores)
    | none =>
      match isets[isets.size - 1]! with
      | .indexSet _ _ v _ _ => .ok (isets.push (.okState v))
      | _ => .ok isets
  else if let some op := findIndexSet env e then
    match op with
    | .indexSet _ _ v _ _ => .ok #[op, .okState v]
    | _ => .ok #[op]
  else
  let e := peelControl 8 e
  if isErrorOverflow e then
    .ok #[.errorOverflow]
  else if let some name := errorCtorName e then
    .ok #[.errorNamed name]
  else if let some ops := asStoreFields env e then
    .ok ops
  else if let some v := asOkState env e then
    .ok #[.okState v]
  else if let some vs := asStateFields env e then
    .ok (returnStatesOf vs)
  else if let some v := asStateMk env e then
    .ok #[.returnState v]
  else if isConstNamed e ``Prod.mk && e.getAppArgs.size ≥ 2 then
    match val env e.getAppArgs[e.getAppArgs.size - 2]!,
          val env e.getAppArgs[e.getAppArgs.size - 1]! with
    | some a, some b => .ok #[.returnU64 a, .returnU64 b]
    | _, _ => .error "extract/unsupported: pair return"
  else if let some v := val env e then
    match v with
    | .field _ _ => .ok #[.returnU64 v]
    | .arg _ => .ok #[.returnU64 v]
    | .lit _ => .ok #[.returnU64 v]
    | .clockSlot | .clockEpoch | .unixTime | .slotsPerEpoch | .signerKey0 | .accLamports0 | .accOwner0 | .accDataLen0
    | .accN | .isSigner0 | .isWritable0 | .isExecutable0
    | .accLamports1 | .accOwner1 | .accDataLen1
    | .isSigner1 | .isWritable1 | .isExecutable1 | .findPda _
    | .checkPda _ _ | .rentExemption _ | .cpiReturn | .sha256Lit _ | .keccak256Lit _
    | .accKeyWord _ _ | .accOwnerWord _ _
    | .accLamportsN _ | .accDataLenN _ | .isSignerN _ | .isWritableN _ | .isExecutableN _
    | .signerKeyN _ | .ownerIsSelf _ => .ok #[.returnU64 v]
    | .indexGet .. => .ok #[.returnU64 v]
    | .addU64 .. | .subU64 .. | .mulU64 .. | .divU64 .. | .modU64 .. =>
        .ok #[.returnU64 v]
    | .bitAnd .. | .bitOr .. | .bitXor .. | .bitNot .. | .shiftL .. | .shiftR .. =>
        .ok #[.returnU64 v]
    | v =>
      if Ops.hasEvmLeaf #[.returnU64 v] || Ops.isLangLeaf v then .ok #[.returnU64 v]
      else .error "extract/unsupported: body"
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

private def decodeExpr (env : Environment) (fuel : Nat) (e : Expr)
    (stateful : Bool := false) : Except String (Array Ops.Op) :=
  match fuel with
  | 0 => .error "extract/unsupported: ite depth"
  | fuel' + 1 => Id.run do
    let fullySubstituted := substLets 256 e
    let controlled := peelControl 16 fullySubstituted
    let e :=
      if (unfoldUserHelper env fullySubstituted).isSome then fullySubstituted
      else if (unfoldUserHelper env controlled).isSome then controlled
      else e
    let e0 := strip e
    let stateLoop? : Option (Except String (Array Ops.Op)) :=
      match findForStateExpr env e with
      | none => none
      | some (n, bodyE, continuation) =>
        match decodeExpr env fuel' bodyE (stateful := true) with
        | .error reason => some (.error s!"extract/unsupported: state loop body: {reason}")
        | .ok bodyOps =>
          if Ops.hasStoreField bodyOps || Ops.hasIndexSet bodyOps then
            match decodeExpr env fuel' continuation with
            | .error reason =>
              match findOkRet env continuation with
              | some ret =>
                some (.ok (#[.forBody n (bodyOps.map rewriteLoopOp), .okState ret]))
              | none => some (.error s!"extract/unsupported: state loop continuation: {reason}")
            | .ok continuationOps =>
              some (.ok (#[.forBody n (bodyOps.map rewriteLoopOp)] ++ continuationOps))
          else none
    if let some result := stateLoop? then
      return result
    else if (isConstNamed e0 ``ite || isConstNamed e0 ``dite) && e0.getAppArgs.size ≥ 5 then
      -- 已经是比较 / dite，不要再往下搜 forIn（循环体自己就是 ite）。
      pure ()
    else if let some inv := findInvoke env 16 e then
      return .ok (invokeOps inv (invokeRet env e inv))
    else if let some ops := decodeEvmEffect env e then
      return .ok ops
    else if let some (n, addend) := findForIn env e then
      return .ok #[.forAccum n addend, .returnU64 addend]
    else if let some (n, bodyE) := findForBodyExpr env e then
      match decodeExpr env fuel' bodyE with
      | .ok ops => return .ok #[.forBody n (ops.map rewritePlainLoopOp), .errorOverflow]
      | .error r => return .error r
    let e := strip e
    if (isConstNamed e ``ite || isConstNamed e ``dite) && e.getAppArgs.size ≥ 5 then
      let args := e.getAppArgs
      let rec peelProofLam (fuel : Nat) (lower : Bool) (e : Expr) : Expr :=
        match fuel with
        | 0 => e
        | fuel' + 1 =>
          match strip e with
          -- 先代入 `have __src`，再降 proof λ。反过来会把 `h` 叠到 `__src` 上。
          | .lam _ _ body _ =>
            let body := substLets 16 body
            let body := if lower then body.lowerLooseBVars 1 1 else body
            peelProofLam fuel' lower body
          | e => e
      -- 不在这里 peelLets：`let debit := evmMapSetAddr …` 必须留给 decodeEvmEffect。
      -- 只代 then / else：入口代整个 ite 会把 `have y` 塞进 `y ≠ 0`，asCmp 认不出。
      let tRaw := args[args.size - 2]!
      let fRaw := args[args.size - 1]!
      let lower :=
        stateful ||
          (!(collectIndexSets env tRaw).isEmpty &&
            !isForInStep tRaw && !isForInStep fRaw)
      let t := substIteLets 64 (peelProofLam 4 lower tRaw)
      let f := substIteLets 64 (peelProofLam 4 stateful fRaw)
      let checkedSubMatches (candidate : Expr) : Bool :=
        match asCheckedSubGuard env candidate with
        | none => false
        | some (guardLhs, guardRhs) =>
          let directResult :=
            match strip t with
            | .letE _ _ value _ _ => val env value
            | _ => asOkState env t
          let directMatch :=
            match directResult with
            | some (.subU64 bodyLhs bodyRhs) =>
                guardLhs == bodyLhs && guardRhs == bodyRhs
            | _ => false
          let nestedMatch :=
            match lastNamedBin env ``HSub.hSub t with
            | some (bodyLhs, bodyRhs) =>
                guardLhs == bodyLhs && guardRhs == bodyRhs
            | none => false
          directMatch || nestedMatch
      let rec hasNestedIte (fuel : Nat) (e : Expr) : Bool :=
        match fuel with
        | 0 => false
        | fuel' + 1 =>
          let e := strip e
          if isConstNamed e ``ite || isConstNamed e ``dite then true
          else
            match e with
            | .letE _ _ value body _ =>
                hasNestedIte fuel' value || hasNestedIte fuel' body
            | .lam _ _ body _ => hasNestedIte fuel' body
            | .app fn arg => hasNestedIte fuel' fn || hasNestedIte fuel' arg
            | _ => false
      -- A recursive invoke search must not erase an intervening source branch.
      let directInvoke := if hasNestedIte 64 t then none else findInvoke env 8 t
      if isErrorOverflow f && !isForInYield f then
        if let some condE := findBy args (fun a =>
            (asCmp env a).isSome &&
              (asCheckedAddGuard env a).isNone &&
              (asCheckedMulGuard env a).isNone &&
              !checkedSubMatches a &&
              -- 真支再套 ite 时，`y ≠ 0` 是比较，不是除法守卫。
              ((asNeZero env a).isNone ||
                isConstNamed (peelLets (strip t)) ``ite ||
                  isConstNamed (peelLets (strip t)) ``dite)) then
          let decodedThen := decodeExpr env fuel' t (stateful := stateful)
          match asCmp env condE, directInvoke, decodeEvmEffect env t, asIndexSet env t,
              asStoreFields env t, asOkState env t, decodedThen with
          | some (.ne, .lit 0, .lit 1), some inv, _, _, _, _, _ =>
            return .ok (invokeOps inv (invokeRet env t inv))
          | some (.ne, .lit 1, .lit 0), some inv, _, _, _, _, _ =>
            return .ok (invokeOps inv (invokeRet env t inv))
          | some (cmp, lv, rv), some inv, _, _, _, _, _ =>
            return .ok #[.ite cmp lv rv (invokeOps inv (invokeRet env t inv)) #[.errorOverflow]]
          | some (cmp, lv, rv), none, some evmOps, _, _, _, _ =>
            return .ok #[.ite cmp lv rv evmOps #[.errorOverflow]]
          | some (cmp, lv, rv), none, none, some iset, _, _, _ =>
            if hasNestedIte 64 t then
              match decodeExpr env fuel' t (stateful := stateful) with
              | .ok thn => return .ok #[.ite cmp lv rv thn #[.errorOverflow]]
              | .error r => return .error r
            else
              let isets := collectIndexSets env t
              let ops := if isets.size ≥ 1 then isets else #[iset]
              match asStoreFields env t true with
              | some stores =>
                return .ok #[.ite cmp lv rv
                  (ops ++ dropVectorRootStores ops stores) #[.errorOverflow]]
              | none =>
                match ops[ops.size - 1]! with
                | .indexSet _ _ v _ _ =>
                  -- 多叶 set 的返回值是 `.ok (_, y)`。循环体不要用 findOkRet。
                  let ret :=
                    if isForInStep t then v else (findOkRet env t).getD v
                  return .ok #[.ite cmp lv rv (ops.push (.okState ret)) #[.errorOverflow]]
                | _ => return .ok #[.ite cmp lv rv ops #[.errorOverflow]]
          | some (cmp, lv, rv), none, none, none, some stores, _, _ =>
            return .ok #[.ite cmp lv rv stores #[.errorOverflow]]
          | some (cmp, lv, rv), none, none, none, none, some v, _ =>
            return .ok #[.ite cmp lv rv #[.okState v] #[.errorOverflow]]
          | some (cmp, lv, rv), none, none, none, none, none, .ok thn =>
            match decodeExpr env fuel' f (stateful := stateful) with
            | .ok els => return .ok #[.ite cmp lv rv thn els]
            | .error _ => return .ok #[.ite cmp lv rv thn #[.errorOverflow]]
          | some _, none, none, none, none, none, .error reason =>
            return .error s!"extract/unsupported: comparison continuation: {reason}"
          | _, _, _, _, _, _, _ => return .error "extract/unsupported: ite then/cmp"
        else if let some condE := findBy args (fun a => (asCheckedAddGuard env a).isSome) then
          match asCheckedAddGuard env condE, directInvoke, decodeEvmEffect env t,
              decodeExpr env fuel' t (stateful := stateful), asStoreFields env t,
              asOkState env t with
          | some (lhs, rhs), some inv, _, _, some stores, _ =>
            return .ok (#[.checkedAddU64 lhs rhs, invokeOp inv] ++ stores)
          | some _, none, some evmOps, _, _, _ =>
            let some (cmp, lv, rv) := asCmp env condE
              | return .error "extract/unsupported: ite then"
            return .ok #[.ite cmp lv rv evmOps #[.errorOverflow]]
          | some (lhs, rhs), none, none, .ok thn, _, _ =>
            -- then 支可以再套比较 / CPI。先做 checked-add，再跑内层。
            -- 内层若只是 okState，仍压成旧的三连。
            match thn.toList with
            | [.okState v] =>
              let dest := match lhs with | .field .. => lhs | _ => v
              return .ok #[.checkedAddU64 lhs rhs, .okState dest, .errorOverflow]
            | _ =>
              return .ok (#[.checkedAddU64 lhs rhs] ++ thn)
          | some (lhs, rhs), none, none, .error _, some stores, _ =>
            return .ok (#[.checkedAddU64 lhs rhs] ++ stores)
          | some (lhs, rhs), none, none, .error _, none, some v =>
            let dest := match lhs with | .field .. => lhs | _ => v
            return .ok #[.checkedAddU64 lhs rhs, .okState dest, .errorOverflow]
          | some _, none, none, .error reason, none, none =>
            return .error s!"extract/unsupported: checked-add continuation: {reason}"
          | _, _, _, _, _, _ => return .error "extract/unsupported: ite then/add"
        else if let some condE := findBy args (fun a =>
            (asCheckedMulGuard env a).isSome && (collectIndexSets env t).isEmpty) then
          match asCheckedMulGuard env condE,
              decodeExpr env fuel' t (stateful := stateful),
              asStoreFields env t, asOkState env t with
          | some (lhs, rhs), _, some stores, _ =>
            match stores.toList with
            | [.okState v] =>
              let dest := match lhs with | .field .. => lhs | _ => v
              return .ok #[.checkedMulU64 lhs rhs, .okState dest, .errorOverflow]
            | _ =>
              return .ok (#[.checkedMulU64 lhs rhs] ++ stores ++ #[.errorOverflow])
          | some (lhs, rhs), .ok thn, none, _ =>
            match thn.toList with
            | [.okState v] =>
              let dest := match lhs with | .field .. => lhs | _ => v
              return .ok #[.checkedMulU64 lhs rhs, .okState dest, .errorOverflow]
            | _ =>
              return .ok (#[.checkedMulU64 lhs rhs] ++ thn ++ #[.errorOverflow])
          | some (lhs, rhs), .error _, none, some v =>
            let dest := match lhs with | .field .. => lhs | _ => v
            return .ok #[.checkedMulU64 lhs rhs, .okState dest, .errorOverflow]
          | _, _, _, _ => return .error "extract/unsupported: ite then/mul"
        else if let some condE := findBy args (fun a =>
            checkedSubMatches a && (collectIndexSets env t).isEmpty) then
          match asCheckedSubGuard env condE, directInvoke, decodeEvmEffect env t,
              decodeExpr env fuel' t (stateful := stateful),
              decodeExpr env fuel' f (stateful := stateful), asStoreFields env t,
              asOkState env t with
          | some _, some inv, _, _, _, _, _ =>
            let some (cmp, lv, rv) := asCmp env condE
              | return .error "extract/unsupported: ite then"
            return .ok #[.ite cmp lv rv (invokeOps inv (invokeRet env t inv)) #[.errorOverflow]]
          | some _, none, some evmOps, _, _, _, _ =>
            let some (cmp, lv, rv) := asCmp env condE
              | return .error "extract/unsupported: ite then"
            return .ok #[.ite cmp lv rv evmOps #[.errorOverflow]]
          | some (lhs, rhs), none, none, _, .ok #[.errorOverflow], _, some v =>
            let dest := match lhs with | .field .. => lhs | _ => v
            return .ok #[.checkedSubU64 lhs rhs, .okState dest, .errorOverflow]
          | some _, none, none, .ok thn, .ok els, _, _ =>
            let some (cmp, lv, rv) := asCmp env condE
              | return .error "extract/unsupported: ite then"
            return .ok #[.ite cmp lv rv thn els]
          | some (lhs, rhs), none, none, _, _, some stores, _ =>
            return .ok (#[.checkedSubU64 lhs rhs] ++ stores)
          | some (lhs, rhs), none, none, _, _, none, some v =>
            let dest := match lhs with | .field .. => lhs | _ => v
            return .ok #[.checkedSubU64 lhs rhs, .okState dest, .errorOverflow]
          | _, _, _, _, _, _, _ => return .error "extract/unsupported: ite then/sub"
        else if let some condE := findBy args (fun a =>
            (asNeZero env a).isSome && (collectIndexSets env t).isEmpty) then
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
        let isValueCmp (a : Expr) : Bool :=
          (asCmp env a).isSome &&
            (asCheckedAddGuard env a).isNone &&
            (asCheckedMulGuard env a).isNone &&
            !checkedSubMatches a
        if isForInYield f && !stateful then
          let some condE := findBy args isValueCmp <|> findBy args (fun a => (asCmp env a).isSome)
            | return .error "extract/unsupported: ite cond"
          let some (cmp, lv, rv) := asCmp env condE
            | return .error "extract/unsupported: ite cond"
          match decodeExpr env fuel' t (stateful := stateful) with
          | .ok thn => return .ok #[.ite cmp lv rv thn #[]]
          | .error r => return .error s!"extract/unsupported: forBody then {r}"
        let some condE := findBy args isValueCmp <|> findBy args (fun a => (asCmp env a).isSome)
          | return .error "extract/unsupported: ite cond"
        let some (cmp, lv, rv) := asCmp env condE
          | return .error "extract/unsupported: ite cond"
        match decodeExpr env fuel' t (stateful := stateful),
            decodeExpr env fuel' f (stateful := stateful) with
        | .ok thn, .ok els => return .ok #[.ite cmp lv rv thn els]
        | .error r, _ =>
          return .error (if stateful then s!"state loop then: {r}" else r)
        | _, .error r =>
          return .error (if stateful then s!"state loop else: {r}" else r)
    else if let some ops := decodeEvmEffect env e then
      return .ok ops
    else if let some inv := decodeInvokeArgs env e <|> findInvoke env 8 e then
      return .ok (invokeOps inv (invokeRet env e inv))
    else if let some (name, unfolded) := unfoldUserHelper env e then
      match decodeExpr env fuel' (substIteLets 256 unfolded) (stateful := stateful) with
      | .ok ops => return .ok ops
      | .error reason => return .error s!"extract/unsupported: inline {name}: {reason}"
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
      match decodeExpr env fuel' noneBody (stateful := stateful) with
      | .error r => return .error r
      | .ok noneOps =>
        let someOps :=
          match strip someBody with
          | .bvar _ => #[.returnU64 payload]
          | _ =>
            match decodeExpr env fuel' someBody (stateful := stateful) with
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
  -- Canonicalize syntax-only aliases around control flow before shape decoding.
  -- Effectful lets remain visible to the dedicated intrinsic decoders.
  let fullySubstituted := substLets 256 body
  let body :=
    if (unfoldUserHelper env fullySubstituted).isSome then fullySubstituted
    else zetaPureHeadLets env 32 body
  decodeExpr env 128 (substIteLets 256 body)

private def writesOptionLeaf (fuel : Nat) (ops : Array Ops.Op) : Bool :=
  match fuel with
  | 0 => false
  | fuel' + 1 =>
    ops.any fun
      | .okState (.field _ n) => n.endsWith "_tag" || n.endsWith "_p0"
      | .okState (.lit _) => true
      | .okState (.arg _) => true
      | .storeField n _ => n.endsWith "_tag" || n.endsWith "_p0"
      | .ite _ _ _ t f => writesOptionLeaf fuel' t || writesOptionLeaf fuel' f
      | _ => false

private def hasIte (ops : Array Ops.Op) : Bool :=
  ops.any fun | .ite .. => true | _ => false

/-- 可变入口必须有 checked 算术、Option 双叶，或比较 ite（窄宽上界）。 -/
def decodeMutating (env : Environment) (e : Expr) : Except String (Array Ops.Op) := do
  let ops ← decodeBody env e
  if Ops.hasCheckedArith ops || writesOptionLeaf 8 ops || hasIte ops ||
      Ops.hasInvoke ops || Ops.hasEvmEffect ops || Ops.hasLangOp ops ||
        Ops.hasForAccum ops || Ops.hasIndexSet ops || Ops.hasStoreField ops then
    return ops
  else
    throw "extract/unsupported: mutating method missing checked arith"

private def widthOfType (e : Expr) : Option Nat :=
  match e.consumeMData.getAppFn.constName? with
  | some ``UInt8 => some 1
  | some ``UInt16 => some 2
  | some ``UInt32 => some 4
  | some ``UInt64 => some 8
  | _ => none

/-- 用户参数宽。init 全算；mutate/view 丢掉第一个 state。 -/
private def inferParamWidths (_env : Environment) (e : Expr) (kind : IR.MethodKind) :
    Array Nat :=
  let rec collect (fuel : Nat) (e : Expr) (acc : Array Nat) : Array Nat :=
    match fuel with
    | 0 => acc
    | fuel' + 1 =>
      match strip e with
      | .lam _ ty body _ =>
        collect fuel' body (acc.push ((widthOfType ty).getD 8))
      | .letE _ _ _ body _ => collect fuel' body acc
      | _ => acc
  let widths := collect 32 e #[]
  match kind with
  | .init => widths
  | .increment | .get => if widths.isEmpty then #[] else widths.extract 1 widths.size

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
  let (nLams, methodBody) := peelLams e
  let stateLoop := (findForStateExpr env methodBody).isSome && ops0.any fun
    | .forBody _ body => Ops.hasStoreField body || Ops.hasIndexSet body
    | _ => false
  let rec normalizeStateLoopVal (fuel : Nat) (v : Ops.Val) : Ops.Val :=
    match fuel with
    | 0 => v
    | fuel' + 1 =>
      let state := .arg (nLams - 1)
      match v with
      -- Loop body binders are accumulator 0 and index 1. `rewriteLoopIx` has already
      -- canonicalized index 1; shift the remaining outer method arguments back by two.
      | .arg i => if i ≥ 2 then .arg (i - 2) else v
      | .field _ name => .field state name
      | .indexGet _ name index len off =>
          .indexGet state name (normalizeStateLoopVal fuel' index) len off
      | .checkPda seed bump => .checkPda seed (normalizeStateLoopVal fuel' bump)
      | .bitAnd l r => .bitAnd (normalizeStateLoopVal fuel' l) (normalizeStateLoopVal fuel' r)
      | .bitOr l r => .bitOr (normalizeStateLoopVal fuel' l) (normalizeStateLoopVal fuel' r)
      | .bitXor l r => .bitXor (normalizeStateLoopVal fuel' l) (normalizeStateLoopVal fuel' r)
      | .bitNot x => .bitNot (normalizeStateLoopVal fuel' x)
      | .shiftL l r => .shiftL (normalizeStateLoopVal fuel' l) (normalizeStateLoopVal fuel' r)
      | .shiftR l r => .shiftR (normalizeStateLoopVal fuel' l) (normalizeStateLoopVal fuel' r)
      | .addU64 l r => .addU64 (normalizeStateLoopVal fuel' l) (normalizeStateLoopVal fuel' r)
      | .subU64 l r => .subU64 (normalizeStateLoopVal fuel' l) (normalizeStateLoopVal fuel' r)
      | .mulU64 l r => .mulU64 (normalizeStateLoopVal fuel' l) (normalizeStateLoopVal fuel' r)
      | .divU64 l r => .divU64 (normalizeStateLoopVal fuel' l) (normalizeStateLoopVal fuel' r)
      | .modU64 l r => .modU64 (normalizeStateLoopVal fuel' l) (normalizeStateLoopVal fuel' r)
      | v => v
  let rec normalizeStateLoopOp (fuel : Nat) (op : Ops.Op) : Ops.Op :=
    match fuel with
    | 0 => op
    | fuel' + 1 =>
      let nv := normalizeStateLoopVal fuel'
      match op with
      | .checkedAddU64 l r => .checkedAddU64 (nv l) (nv r)
      | .checkedSubU64 l r => .checkedSubU64 (nv l) (nv r)
      | .checkedMulU64 l r => .checkedMulU64 (nv l) (nv r)
      | .checkedDivU64 l r => .checkedDivU64 (nv l) (nv r)
      | .checkedModU64 l r => .checkedModU64 (nv l) (nv r)
      | .ite cmp l r t f =>
          .ite cmp (nv l) (nv r) (t.map (normalizeStateLoopOp fuel'))
            (f.map (normalizeStateLoopOp fuel'))
      | .invoke prog metas data seed bump =>
          .invoke prog metas (data.map fun | .u64le v => .u64le (nv v) | w => w)
            seed (bump.map nv)
      | .forAccum bound addend => .forAccum bound (nv addend)
      | .forBody bound body => .forBody bound (body.map (normalizeStateLoopOp fuel'))
      | .indexSet name index value len off => .indexSet name (nv index) (nv value) len off
      | .storeField name value => .storeField name (nv value)
      | .okState value => .okState (nv value)
      | .returnU64 value => .returnU64 (nv value)
      | .returnState value => .returnState (nv value)
      | op => op
  let ops0 := if stateLoop then ops0.map (normalizeStateLoopOp 32) else ops0
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
      | .arg i =>
        if kind == .init && i < nLams then .arg (nLams - 1 - i)
        else if kind == .increment && nLams > 1 && i + 1 < nLams then
          .arg (nLams - 2 - i)
        else if kind == .get && nLams > 1 && i + 1 < nLams then
          .arg (nLams - 2 - i)
        else v
      | .field b n => .field (flipVal fuel' b) n
      | .lit _ => v
      | .clockSlot | .clockEpoch | .unixTime | .slotsPerEpoch | .signerKey0 | .accLamports0 | .accOwner0 | .accDataLen0
      | .accN | .isSigner0 | .isWritable0 | .isExecutable0
      | .accLamports1 | .accOwner1 | .accDataLen1
      | .isSigner1 | .isWritable1 | .isExecutable1 | .findPda _
      | .rentExemption _ | .cpiReturn | .sha256Lit _ | .keccak256Lit _
      | .accKeyWord _ _ | .accOwnerWord _ _
      | .accLamportsN _ | .accDataLenN _ | .isSignerN _ | .isWritableN _ | .isExecutableN _
      | .signerKeyN _ | .ownerIsSelf _ => v
      | .checkPda s b => .checkPda s (flipVal fuel' b)
      | .bitAnd l r => .bitAnd (flipVal fuel' l) (flipVal fuel' r)
      | .bitOr l r => .bitOr (flipVal fuel' l) (flipVal fuel' r)
      | .bitXor l r => .bitXor (flipVal fuel' l) (flipVal fuel' r)
      | .bitNot v => .bitNot (flipVal fuel' v)
      | .shiftL l r => .shiftL (flipVal fuel' l) (flipVal fuel' r)
      | .shiftR l r => .shiftR (flipVal fuel' l) (flipVal fuel' r)
      | .indexGet b n i k off =>
          .indexGet (flipVal fuel' b) n (flipVal fuel' i) k off
      | .loopIx => v
      | .addU64 l r => .addU64 (flipVal fuel' l) (flipVal fuel' r)
      | .subU64 l r => .subU64 (flipVal fuel' l) (flipVal fuel' r)
      | .mulU64 l r => .mulU64 (flipVal fuel' l) (flipVal fuel' r)
      | .divU64 l r => .divU64 (flipVal fuel' l) (flipVal fuel' r)
      | .modU64 l r => .modU64 (flipVal fuel' l) (flipVal fuel' r)
      | .mapGetU64 b k => .mapGetU64 (flipVal fuel' b) (flipVal fuel' k)
      | .mapGetAddr b a0 a1 a2 =>
          .mapGetAddr (flipVal fuel' b) (flipVal fuel' a0) (flipVal fuel' a1) (flipVal fuel' a2)
      | .mapGetPair b a0 a1 a2 c0 c1 c2 =>
          .mapGetPair (flipVal fuel' b) (flipVal fuel' a0) (flipVal fuel' a1)
            (flipVal fuel' a2) (flipVal fuel' c0) (flipVal fuel' c1) (flipVal fuel' c2)
      | v => v
  let rec flipOp (fuel : Nat) (op : Ops.Op) : Ops.Op :=
    match fuel with
    | 0 => op
    | fuel' + 1 =>
      match op with
      | .returnState v => .returnState (flipVal fuel' v)
      | .returnU64 v => .returnU64 (flipVal fuel' v)
      | .storeField n v => .storeField n (flipVal fuel' v)
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
      | .evmDeposit v => .evmDeposit (flipVal fuel' v)
      | .evmSendEth a b c d =>
          .evmSendEth (flipVal fuel' a) (flipVal fuel' b) (flipVal fuel' c) (flipVal fuel' d)
      | .evmLog n v => .evmLog n (flipVal fuel' v)
      | .forAccum n v => .forAccum n (flipVal fuel' v)
      | .forBody n body => .forBody n (body.map (flipOp fuel'))
      | .indexSet n i v k off =>
          .indexSet n (flipVal fuel' i) (flipVal fuel' v) k off
      | .mapGetU64 b k => .mapGetU64 (flipVal fuel' b) (flipVal fuel' k)
      | .mapSetU64 b k v =>
          .mapSetU64 (flipVal fuel' b) (flipVal fuel' k) (flipVal fuel' v)
      | .mapGetAddr b a0 a1 a2 =>
          .mapGetAddr (flipVal fuel' b) (flipVal fuel' a0) (flipVal fuel' a1) (flipVal fuel' a2)
      | .mapSetAddr b a0 a1 a2 v =>
          .mapSetAddr (flipVal fuel' b) (flipVal fuel' a0) (flipVal fuel' a1)
            (flipVal fuel' a2) (flipVal fuel' v)
      | .mapGetPair b a0 a1 a2 c0 c1 c2 =>
          .mapGetPair (flipVal fuel' b) (flipVal fuel' a0) (flipVal fuel' a1)
            (flipVal fuel' a2) (flipVal fuel' c0) (flipVal fuel' c1) (flipVal fuel' c2)
      | .mapSetPair b a0 a1 a2 c0 c1 c2 v =>
          .mapSetPair (flipVal fuel' b) (flipVal fuel' a0) (flipVal fuel' a1)
            (flipVal fuel' a2) (flipVal fuel' c0) (flipVal fuel' c1)
            (flipVal fuel' c2) (flipVal fuel' v)
      | .evmTokenTransfer a b c d e f g =>
          .evmTokenTransfer (flipVal fuel' a) (flipVal fuel' b) (flipVal fuel' c)
            (flipVal fuel' d) (flipVal fuel' e) (flipVal fuel' f) (flipVal fuel' g)
      | .evmTokenBalanceOfSelf a b c =>
          .evmTokenBalanceOfSelf (flipVal fuel' a) (flipVal fuel' b) (flipVal fuel' c)
      | .errorOverflow => .errorOverflow
      | .errorNamed n => .errorNamed n
  let ops :=
    if (kind == .init && nLams > 1) ||
        (kind == .increment && nLams > 2) ||
        (kind == .get && nLams > 2) then
      ops1.map (flipOp 16)
    else ops1
  let paramCount :=
    match kind with
    | .init => if nLams = 0 then 1 else nLams
    | .increment | .get => if nLams ≤ 1 then 0 else nLams - 1
  let paramWidths := inferParamWidths env e kind
  let retCount :=
    match kind with
    | .get =>
      let nRet := ops.foldl (init := 0) fun acc op =>
        match op with | .returnU64 _ => acc + 1 | _ => acc
      if nRet = 0 then 1 else nRet
    | _ => 1
  return {
    kind, name := n.toString, ixName := IR.ixNameOfLean lean
    paramCount, paramWidths, retCount, sketch, ops
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

private structure SchemaFragment where
  leaves : Array Core.Leaf := #[]
  vectors : Array Core.VectorLayout := #[]

private def SchemaFragment.byteWidth (fragment : SchemaFragment) : Nat :=
  fragment.leaves.foldl (init := 0) fun width leaf => width + leaf.width

private def scalarFragment (name : String) (place : Core.Place)
    (ty : Core.ScalarTy) : SchemaFragment :=
  { leaves := #[{ place, name, ty }] }

private def optionFragment (name : String) (place : Core.Place) : SchemaFragment :=
  { leaves := #[
      { place := place.push .optionTag, name := s!"{name}_tag", ty := .optionTag },
      { place := place.push .optionPayload, name := s!"{name}_p0", ty := .uint 64 }
    ] }

private def leafSchema (env : Environment) (fuel : Nat) (name : String)
    (place : Core.Place) (ty : Expr) : Except String SchemaFragment :=
  match fuel with
  | 0 => .error s!"extract/unsupported: field {name} nest depth"
  | fuel' + 1 =>
    let ty := ty.consumeMData
    if ty.getAppFn.constName? == some ``UInt64 then
      .ok (scalarFragment name place (.uint 64))
    else if ty.getAppFn.constName? == some ``UInt32 then
      .ok (scalarFragment name place (.uint 32))
    else if ty.getAppFn.constName? == some ``UInt16 then
      .ok (scalarFragment name place (.uint 16))
    else if ty.getAppFn.constName? == some ``UInt8 then
      .ok (scalarFragment name place (.uint 8))
    else if ty.getAppFn.constName? == some ``Option then
      let args := ty.getAppArgs
      if args.size ≥ 1 && args[args.size - 1]!.consumeMData.getAppFn.constName? == some ``UInt64 then
        .ok (optionFragment name place)
      else
        .error s!"extract/unsupported: field {name} is not Option UInt64"
    else if ty.getAppFn.constName? == some ``Vector then
      let args := ty.getAppArgs
      if args.size ≥ 2 then
        match asLit 8 args[args.size - 1]! with
        | some (.lit n) =>
          if n.toNat = 0 then
            .error s!"extract/unsupported: field {name} Vector length 0"
          else
            Id.run do
              let mut leaves : Array Core.Leaf := #[]
              let mut vectors : Array Core.VectorLayout := #[]
              let mut elementBytes : Nat := 0
              let mut elementLeaves : Nat := 0
              for i in List.range n.toNat do
                let itemPlace := place.push (.index i)
                match leafSchema env fuel' s!"{name}_{i}" itemPlace args[args.size - 2]! with
                | .error reason => return .error reason
                | .ok item =>
                    if i == 0 then
                      elementBytes := item.byteWidth
                      elementLeaves := item.leaves.size
                    leaves := leaves ++ item.leaves
                    vectors := vectors ++ item.vectors
              let vector : Core.VectorLayout := {
                place, name, length := n.toNat, elementBytes, elementLeaves
              }
              return .ok { leaves, vectors := #[vector] ++ vectors }
        | _ => .error s!"extract/unsupported: field {name} Vector length is not a literal"
      else
        .error s!"extract/unsupported: field {name} is not Vector UInt64 n"
    else if ty.getAppFn.constName? == some ``Array then
      .error s!"extract/unsupported: field {name} Array is not fixed-length; use Vector"
    else if ty.getAppFn.constName? == some ``Bool then
      .ok (scalarFragment name place .bool)
    else if let some tyName := ty.getAppFn.constName? then
      if isEnumLeaf env tyName then
        .ok (scalarFragment name place (.enum tyName.toString))
      else if isOptionLikeInductive env tyName then
        .ok (optionFragment name place)
      else if isUserName env tyName && isStructure env tyName &&
          !(isEnumLeaf env tyName) && !(isOptionLikeInductive env tyName) then
        if !(getStructureParentInfo env tyName).isEmpty then
          .error s!"extract/unsupported: field {name} record inheritance"
        else
          let fields := getStructureFields env tyName
          if fields.isEmpty then
            .error s!"extract/unsupported: field {name} record has no fields"
          else
            Id.run do
              let mut acc : SchemaFragment := {}
              let mut ordinal : Nat := 0
              for f in fields do
                if (isSubobjectField? env tyName f).isSome then
                  return .error s!"extract/unsupported: field {name} record inheritance"
                let some fty := fieldTypeExpr env tyName f
                  | return .error s!"extract/unsupported: field {name}.{f} has no type"
                let childPlace := place.push (.field tyName.toString ordinal f.toString)
                match leafSchema env fuel' s!"{name}_{f}" childPlace fty with
                | .error r => return .error r
                | .ok fragment =>
                    acc := {
                      leaves := acc.leaves ++ fragment.leaves
                      vectors := acc.vectors ++ fragment.vectors
                    }
                ordinal := ordinal + 1
              return .ok acc
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

/-- 从 `init` 返回类型收 typed state schema。无 `extends`。 -/
def inferSchema (env : Environment) (initName : Name) : Except String Core.Schema := do
  let some info := env.find? initName
    | throw s!"extract/unsupported: unknown {initName}"
  let some structName := (peelForalls info.type).getAppFn.constName?
    | throw "extract/unsupported: init return is not a structure"
  unless isStructure env structName do
    throw s!"extract/unsupported: init return is not a structure {structName}"
  unless (getStructureParentInfo env structName).isEmpty do
    throw "extract/unsupported: record inheritance"
  let names := getStructureFields env structName
  if names.isEmpty then
    throw "extract/unsupported: structure has no fields"
  let mut leaves : Array Core.Leaf := #[]
  let mut vectors : Array Core.VectorLayout := #[]
  let mut ordinal : Nat := 0
  for n in names do
    if (isSubobjectField? env structName n).isSome then
      throw "extract/unsupported: record inheritance"
    let some ty := fieldTypeExpr env structName n
      | throw s!"extract/unsupported: field {n} has no type"
    let place : Core.Place := {
      steps := #[.field structName.toString ordinal n.toString]
    }
    let fragment ← leafSchema env 8 n.toString place ty
    leaves := leaves ++ fragment.leaves
    vectors := vectors ++ fragment.vectors
    ordinal := ordinal + 1
  return { rootType := structName.toString, leaves, vectors }

/-- Compatibility physical slots are now a derived view of the typed schema. -/
def inferSlots (env : Environment) (initName : Name) : Except String (Array IR.Slot) := do
  return IR.slotsOfSchema (← inferSchema env initName)

def inferFields (env : Environment) (initName : Name) : Except String (Array String) := do
  return (← inferSlots env initName).map (·.name)

private def valFields : Ops.Val → Array String
  | .field b n => valFields b |>.push n
  | .arg _ => #[]
  | .lit _ => #[]
  | .clockSlot | .clockEpoch | .unixTime | .slotsPerEpoch | .signerKey0 | .accLamports0 | .accOwner0 | .accDataLen0
  | .accN | .isSigner0 | .isWritable0 | .isExecutable0
  | .accLamports1 | .accOwner1 | .accDataLen1
  | .isSigner1 | .isWritable1 | .isExecutable1 | .findPda _
  | .rentExemption _ | .cpiReturn | .sha256Lit _ | .keccak256Lit _
  | .accKeyWord _ _ | .accOwnerWord _ _
  | .accLamportsN _ | .accDataLenN _ | .isSignerN _ | .isWritableN _ | .isExecutableN _
  | .signerKeyN _ | .ownerIsSelf _ => #[]
  | .checkPda _ b => valFields b
  | .bitAnd l r | .bitOr l r | .bitXor l r | .shiftL l r | .shiftR l r =>
      valFields l ++ valFields r
  | .bitNot v => valFields v
  | .indexGet b _ i _ => valFields b ++ valFields i
  | .loopIx => #[]
  | .addU64 l r | .subU64 l r | .mulU64 l r | .divU64 l r | .modU64 l r =>
      valFields l ++ valFields r
  | .mapGetU64 b k => valFields b ++ valFields k
  | .mapGetAddr b a0 a1 a2 =>
      valFields b ++ valFields a0 ++ valFields a1 ++ valFields a2
  | .mapGetPair b a0 a1 a2 c0 c1 c2 =>
      valFields b ++ valFields a0 ++ valFields a1 ++ valFields a2 ++
        valFields c0 ++ valFields c1 ++ valFields c2
  | v => if Ops.hasEvmLeaf #[.returnU64 v] then #[] else #[]

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
  | .evmDeposit v => valFields v
  | .evmSendEth a b c d => valFields a ++ valFields b ++ valFields c ++ valFields d
  | .evmLog _ v => valFields v
  | .forAccum _ v => valFields v
  | .forBody _ body => body.flatMap opFields
  | .indexSet _ i v _ _ => valFields i ++ valFields v
  | .storeField n v => #[n] ++ valFields v
  | .mapGetU64 b k => valFields b ++ valFields k
  | .mapSetU64 b k v => valFields b ++ valFields k ++ valFields v
  | .mapGetAddr b a0 a1 a2 => valFields b ++ valFields a0 ++ valFields a1 ++ valFields a2
  | .mapSetAddr b a0 a1 a2 v =>
      valFields b ++ valFields a0 ++ valFields a1 ++ valFields a2 ++ valFields v
  | .mapGetPair b a0 a1 a2 c0 c1 c2 =>
      valFields b ++ valFields a0 ++ valFields a1 ++ valFields a2 ++
        valFields c0 ++ valFields c1 ++ valFields c2
  | .mapSetPair b a0 a1 a2 c0 c1 c2 v =>
      valFields b ++ valFields a0 ++ valFields a1 ++ valFields a2 ++
        valFields c0 ++ valFields c1 ++ valFields c2 ++ valFields v
  | .evmTokenTransfer a b c d e f g =>
      valFields a ++ valFields b ++ valFields c ++ valFields d ++
        valFields e ++ valFields f ++ valFields g
  | .evmTokenBalanceOfSelf a b c => valFields a ++ valFields b ++ valFields c
  | .okState v => valFields v
  | .errorOverflow => #[]
  | .errorNamed _ => #[]
  | .returnU64 v => valFields v
  | .returnState v => valFields v

private def fillElemOff (p : IR.Program) : IR.Program :=
  let rec goVal (fuel : Nat) (v : Ops.Val) : Ops.Val :=
    match fuel with
    | 0 => v
    | fuel' + 1 =>
      match v with
      | .indexGet b n i k off =>
          let leaf := IR.vectorLeafName p n off
          let off' :=
            if leaf.isEmpty then off else IR.vectorLeafOff p n leaf
          .indexGet (goVal fuel' b) n (goVal fuel' i) k off'
      | .field b n => .field (goVal fuel' b) n
      | .addU64 l r => .addU64 (goVal fuel' l) (goVal fuel' r)
      | .subU64 l r => .subU64 (goVal fuel' l) (goVal fuel' r)
      | .mulU64 l r => .mulU64 (goVal fuel' l) (goVal fuel' r)
      | .divU64 l r => .divU64 (goVal fuel' l) (goVal fuel' r)
      | .modU64 l r => .modU64 (goVal fuel' l) (goVal fuel' r)
      | v => v
  let rec goOp (fuel : Nat) (op : Ops.Op) : Ops.Op :=
    match fuel with
    | 0 => op
    | fuel' + 1 =>
      match op with
      | .indexSet n i v k off =>
          let leaf := IR.vectorLeafName p n off
          let off' :=
            if leaf.isEmpty then off else IR.vectorLeafOff p n leaf
          .indexSet n (goVal 8 i) (goVal 8 v) k off'
      | .ite c l r t f =>
          .ite c (goVal 8 l) (goVal 8 r) (t.map (goOp fuel')) (f.map (goOp fuel'))
      | .forBody n body => .forBody n (body.map (goOp fuel'))
      | .okState v => .okState (goVal 8 v)
      | .returnU64 v => .returnU64 (goVal 8 v)
      | op => op
  { p with methods := p.methods.map fun m => { m with ops := m.ops.map (goOp 8) } }

/-- Make state writeback explicit once, after source schema and normalized Ops are both available. -/
private def evaluateProgram (p : IR.Program) : Except String IR.Program := do
  let mut methods := #[]
  for method in p.methods do
    let evaluation ←
      match Core.evaluate p.schema method.ops with
      | .ok evaluation => pure evaluation
      | .error reason => throw s!"{method.ixName}: {reason}"
    methods := methods.push { method with evaluation }
  return { p with methods }

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
  let schema ← inferSchema env initName
  let inferred := IR.slotsOfSchema schema
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
    schema
    methods := #[initM, incM, getM]
  }
  unless IR.isProgramShape program do
    throw "extract/unsupported: not three-method shape"
  unless IR.schemaMatchesSlots program do
    throw "extract/unsupported: schema does not match slots"
  let program := fillElemOff program
  let program ← evaluateProgram program
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
  if isUInt64Type ret || (widthOfType ret).isSome then
    return .get
  if ret.getAppFn.constName? == some ``Prod then
    return .get
  if let some structName := ret.getAppFn.constName? then
    if isStructure env structName && structName != ``UInt64 &&
        structName != ``Prod then
      return .init
  throw s!"extract/unsupported: cannot classify {n}"

private def sortNames (ns : Array Name) : Array Name :=
  ns.qsort (·.toString < ·.toString)

/-- 收同一名字空间下 `@[pf_entry]` 的根。须恰好一个 init、至少一个 mutate、至少一个 view。 -/
def extractModule (env : Environment) (ns : Name)
    (fields? : Option (Array String) := none) :
    Except String IR.Program := do
  let tagged := sortNames (Attr.entriesIn env ns)
  if tagged.isEmpty then
    throw "extract/unsupported: no pf_entry"
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
  let schema ← inferSchema env initName
  let inferred := IR.slotsOfSchema schema
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
    schema
    methods
  }
  unless IR.isProgramShape program do
    throw "extract/unsupported: not program shape"
  unless IR.schemaMatchesSlots program do
    throw "extract/unsupported: schema does not match slots"
  let program := fillElemOff program
  let program ← evaluateProgram program
  checkUsedFields program
  match IR.layoutMarkerHex program with
  | .error reason => throw reason
  | .ok _ => pure ()
  for m in program.methods do
    match IR.discHex m with
    | .error reason => throw reason
    | .ok _ => pure ()
  return program

end ProofForge.Extract
