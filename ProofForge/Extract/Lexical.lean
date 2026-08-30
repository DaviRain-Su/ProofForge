import Lean
import ProofForge.Extract.Ops
import ProofForge.Profile
import ProofForge.Attr
import ProofForge.Core.Value
import ProofForge.Svm.Runtime
import ProofForge.Evm.Runtime
import ProofForge.Evm.Codec
import ProofForge.Extract.Ops

open Lean

namespace ProofForge.Extract


opaque localRef (i : Nat) : UInt64
opaque methodArgRef (i : Nat) : UInt64
/-- Extractor-only marker for one yielded invocation-local scalar frame. It disappears into
existing `letLocal`/`setLocal` operations before target lowering. -/
def scalarFrameYield {α : Type} (_base : Nat) (value : α) : α := value
def methodArgLocalBase : Nat := 1000000

def sketchOfExpr (e : Expr) : Array String :=
  let names := e.getUsedConstantsAsSet.toList.toArray.qsort (·.toString < ·.toString)
  names.map (·.toString)

def isConstNamed (e : Expr) (n : Name) : Bool :=
  e.consumeMData.getAppFn.constName? == some n

def addr20Name : Name := ``ProofForge.Evm.Runtime.Addr20
def uint128Name : Name := ``ProofForge.Core.Value.UInt128
def uint256Name : Name := ``ProofForge.Core.Value.UInt256
def fixedBytesName : Name := ``ProofForge.Core.Value.FixedBytes
def boundedVecName : Name := ``ProofForge.Core.Value.BoundedVec
def boundedBytesName : Name := ``ProofForge.Core.Value.BoundedBytes
def boundedStringName : Name := ``ProofForge.Core.Value.BoundedString
def evmUInt256AliasName : Name := ``ProofForge.Evm.Runtime.UInt256
def evmBytes32AliasName : Name := ``ProofForge.Evm.Runtime.Bytes32

def natLiteral? (e : Expr) : Option Nat :=
  let rec go (fuel : Nat) (e : Expr) : Option Nat :=
    match fuel with
    | 0 => none
    | fuel' + 1 =>
      let e := e.consumeMData
      match e with
      | .lit (.natVal n) => some n
      | _ =>
        if e.getAppFn.constName? == some ``OfNat.ofNat then
          e.getAppArgs.findSome? (go fuel')
        else none
  go 8 e

def fixedBytesSize? (e : Expr) : Option Nat := do
  let e := e.consumeMData
  if e.getAppFn.constName? == some evmBytes32AliasName then return 32
  if e.getAppFn.constName? != some fixedBytesName then none else pure ()
  let size ← e.getAppArgs.back?
  let n ← natLiteral? size
  if Core.Value.FixedBytes.validSize n then some n else none

def isAddr20Type (e : Expr) : Bool :=
  e.consumeMData.getAppFn.constName? == some addr20Name

def isUInt128Type (e : Expr) : Bool :=
  e.consumeMData.getAppFn.constName? == some uint128Name

def isUInt256Type (e : Expr) : Bool :=
  let name := e.consumeMData.getAppFn.constName?
  name == some uint256Name || name == some evmUInt256AliasName

def isBytes32Type (e : Expr) : Bool :=
  fixedBytesSize? e == some 32

def addr20ProjLeaf (n : Name) : Option String :=
  let last := Core.IR.lastName n.toString
  if n == ``ProofForge.Evm.Runtime.Addr20.w0 || n.toString.endsWith ".Addr20.w0" then some "w0"
  else if n == ``ProofForge.Evm.Runtime.Addr20.w1 || n.toString.endsWith ".Addr20.w1" then some "w1"
  else if n == ``ProofForge.Evm.Runtime.Addr20.w2 || n.toString.endsWith ".Addr20.w2" then some "w2"
  else if last == "w0" || last == "w1" || last == "w2" then
    match n with
    | .str p _ => if p == addr20Name || p.toString.endsWith ".Addr20" then some last else none
    | _ => none
  else none

def uint256ProjLeaf (n : Name) : Option String :=
  let last := Core.IR.lastName n.toString
  if n == ``ProofForge.Core.Value.UInt128.w0 ||
      n == ``ProofForge.Core.Value.UInt256.w0 ||
      n == ``ProofForge.Core.Value.FixedBytes.w0 then some "w0"
  else if n == ``ProofForge.Core.Value.UInt128.w1 ||
      n == ``ProofForge.Core.Value.UInt256.w1 ||
      n == ``ProofForge.Core.Value.FixedBytes.w1 then some "w1"
  else if n == ``ProofForge.Core.Value.UInt256.w2 ||
      n == ``ProofForge.Core.Value.FixedBytes.w2 then some "w2"
  else if n == ``ProofForge.Core.Value.UInt256.w3 ||
      n == ``ProofForge.Core.Value.FixedBytes.w3 then some "w3"
  else if last == "w0" || last == "w1" || last == "w2" || last == "w3" then
    match n with
    | .str p _ =>
        if p == uint128Name || p == uint256Name || p == fixedBytesName then some last
        else none
    | _ => none
  else none

def uint256LimbLit : String → UInt64
  | "w0" => 0 | "w1" => 1 | "w2" => 2 | _ => 3

def isVectorSet (e : Expr) : Bool :=
  isConstNamed e ``Vector.set ||
    (e.getAppFn.constName?.map (·.toString.endsWith "Vector.set")).getD false

def strip (e : Expr) : Expr :=
  e.consumeMData

def endsWith (e : Expr) (suf : String) : Bool :=
  (e.getAppFn.constName?.map (·.toString.endsWith suf)).getD false

def peelLams (e : Expr) : Nat × Expr :=
  let rec go (fuel : Nat) (n : Nat) (e : Expr) : Nat × Expr :=
    match fuel with
    | 0 => (n, e)
    | fuel' + 1 =>
      match strip e with
      | .lam _ _ body _ => go fuel' (n + 1) body
      | e => (n, e)
  go 32 0 e

def peelLets (e : Expr) : Expr :=
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
def substLets (fuel : Nat) (e : Expr) : Expr :=
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
def dropUnusedHeadLets (fuel : Nat) (e : Expr) : Expr :=
  match fuel with
  | 0 => e
  | fuel' + 1 =>
    match strip e with
    | .letE n ty value body nondep =>
      let body := dropUnusedHeadLets fuel' body
      if body.hasLooseBVar 0 then .letE n ty value body nondep
      else dropUnusedHeadLets fuel' (body.lowerLooseBVars 1 1)
    | e => e

def isIteExpr (e : Expr) : Bool :=
  isConstNamed (peelLets (strip e)) ``ite || isConstNamed (peelLets (strip e)) ``dite

/-- Find an outer guard under only `Id.run` and leading lets, without searching through the guard
or hoisting a loop from one of its branches. -/
def guardedRunBody? (fuel : Nat) (e : Expr) : Option Expr :=
  match fuel with
  | 0 => none
  | fuel' + 1 =>
    let e := strip e
    if isConstNamed e ``ite || isConstNamed e ``dite then some e
    else if isConstNamed e ``Id.run && e.getAppArgs.size ≥ 1 then
      guardedRunBody? fuel' e.getAppArgs[e.getAppArgs.size - 1]!
    else
      match e with
      | .letE _ _ value body _ => guardedRunBody? fuel' (body.instantiate1 value)
      | _ => none

/-- Preserve `UInt64` lets for lexical lowering. Zeta-reduce narrow scalar aliases and
aliases around `ite`; retain control/state lets for their dedicated decoders. -/
def substIteLets (fuel : Nat) (e : Expr) : Expr :=
  match fuel with
  | 0 => e
  | fuel' + 1 =>
    match strip e with
    | .letE n ty value body nd =>
      let value := substIteLets fuel' value
      let body := substIteLets fuel' body
      let tyName := ty.consumeMData.getAppFn.constName?
      if tyName == some ``UInt64 then
        .letE n ty value body nd
      else if tyName == some ``UInt8 || tyName == some ``UInt16 ||
          tyName == some ``UInt32 || isIteExpr body then
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

/-- Substitute scalar captures while retaining mutable state/control lets needed to recognize a
state-carrying `for` loop. -/
def substUInt64Lets (fuel : Nat) (e : Expr) : Expr :=
  match fuel with
  | 0 => e
  | fuel' + 1 =>
    match strip e with
    | .letE n ty value body nd =>
      let value := substUInt64Lets fuel' value
      let body := substUInt64Lets fuel' body
      if ty.consumeMData.getAppFn.constName? == some ``UInt64 then
        -- An unused UInt64 can still own an effect (for example `let _ := invoke ...`).
        -- Keep it until effect-aware loop normalization can distinguish the call from a
        -- disposable scalar alias.
        if body.hasLooseBVar 0 then substUInt64Lets fuel' (body.instantiate1 value)
        else .letE n ty value body nd
      else
        .letE n ty value body nd
    | .lam n ty body bi => .lam n ty (substUInt64Lets fuel' body) bi
    | .app _ _ =>
      let rec goApp (n : Nat) (e : Expr) : Expr :=
        match n, strip e with
        | n + 1, .app fn arg => .app (goApp n fn) (substUInt64Lets fuel' arg)
        | _, e => substUInt64Lets fuel' e
      goApp 32 e
    | e => e

/-- 剥 `pure` / `ForInStep.done` / `Option.some`；`Prod.mk` 只在末字段是 `PUnit` 时剥。 -/
def peelControl (fuel : Nat) (e : Expr) : Expr :=
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

def isForInYield (e : Expr) : Bool :=
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

/-- An early `return` from a `for` callback elaborates to `ForInStep.done`; it belongs to the
early-return loop lowering, not the state-carrying loop lowering. -/
def isForInDone (e : Expr) : Bool :=
  let rec go (fuel : Nat) (e : Expr) : Bool :=
    match fuel with
    | 0 => false
    | fuel' + 1 =>
      let e := peelLets (strip e)
      if isConstNamed e ``ForInStep.done || endsWith e ".done" then true
      else
        match e with
        | .lam _ _ body _ => go fuel' body
        | .letE _ _ value body _ => go fuel' value || go fuel' body
        | _ => e.getAppArgs.any (go fuel')
  go 32 e

/-- `ForInStep.done` / `yield`：循环体里的 ite 不要降 proof λ。 -/
def isForInStep (e : Expr) : Bool :=
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
def enumCtorIndex (env : Environment) (tyName ctor : Name) : Option Nat :=
  match env.find? tyName with
  | some (.inductInfo info) =>
    if info.numParams != 0 || info.numIndices != 0 || info.ctors.isEmpty || info.isRec then
      none
    else
      info.ctors.findIdx? (· == ctor)
  | _ => none

def isEnumLeaf (env : Environment) (tyName : Name) : Bool :=
  match env.find? tyName with
  | some (.inductInfo info) =>
    info.numParams == 0 && info.numIndices == 0 && !info.ctors.isEmpty && !info.isRec &&
      info.ctors.all fun ctor =>
        match env.find? ctor with
        | some (.ctorInfo c) => c.numFields == 0
        | _ => false
  | _ => false

/-- One constructor carrying one `UInt64`: a representational newtype, not a tagged union. -/
def isUInt64Newtype (env : Environment) (tyName : Name) : Bool :=
  if isStructure env tyName then false
  else
    match env.find? tyName with
    | some (.inductInfo info) =>
      info.numParams == 0 && info.numIndices == 0 && info.ctors.length == 1 && !info.isRec &&
        match env.find? info.ctors[0]! with
        | some (.ctorInfo ctor) =>
          ctor.numFields == 1 &&
            match strip ctor.type with
            | .forallE _ ty _ _ => ty.consumeMData.getAppFn.constName? == some ``UInt64
            | _ => false
        | _ => false
    | _ => false

def forallDomainAt? (fuel index : Nat) (type : Expr) : Option Expr :=
  match fuel with
  | 0 => none
  | fuel' + 1 =>
    match strip type with
    | .forallE _ domain body _ =>
      if index == 0 then some domain else forallDomainAt? fuel' (index - 1) body
    | _ => none

private def uint64CtorPayloadWidth? (env : Environment) (ctorName : Name) : Option Nat := do
  let .ctorInfo ctor ← env.find? ctorName | none
  for index in [:ctor.numFields] do
    let fieldTy ← forallDomainAt? 32 index ctor.type
    if fieldTy.consumeMData.getAppFn.constName? != some ``UInt64 then none else pure ()
  return ctor.numFields

/--
Three or more constructors with only `UInt64` fields. Their fixed representation is one tag plus
the largest constructor payload; shorter alternatives receive canonical zero padding.
-/
def uint64VariantPayloadWidth? (env : Environment) (tyName : Name) : Option Nat :=
  if isStructure env tyName then none
  else
    match env.find? tyName with
    | some (.inductInfo info) =>
      if info.numParams != 0 || info.numIndices != 0 || info.ctors.length < 3 || info.isRec then
        none
      else Id.run do
        let mut payloadWidth := 0
        for ctorName in info.ctors do
          let some ctorWidth := uint64CtorPayloadWidth? env ctorName | return none
          payloadWidth := max payloadWidth ctorWidth
        if payloadWidth == 0 then return none
        return some payloadWidth
    | _ => none

private def isUInt64Variant (env : Environment) (tyName : Name) : Bool :=
  (uint64VariantPayloadWidth? env tyName).isSome

def uint64NewtypeCtorPayload? (env : Environment) (e : Expr) : Option Expr := do
  let ctorName ← e.getAppFn.constName?
  let .ctorInfo ctor ← env.find? ctorName | none
  if !isUInt64Newtype env ctor.induct || e.getAppArgs.isEmpty then none
  else e.getAppArgs[e.getAppArgs.size - 1]?

def containsUInt64NewtypeCtor (env : Environment) (fuel : Nat) (e : Expr) : Bool :=
  match fuel with
  | 0 => false
  | fuel' + 1 =>
    (uint64NewtypeCtorPayload? env e).isSome ||
      e.getAppArgs.any (containsUInt64NewtypeCtor env fuel')

/-- A one-case matcher is representationally its payload branch; use Lean's matcher metadata. -/
def reduceUInt64NewtypeMatch? (env : Environment) (e : Expr) : Option Expr := do
  let matcherName ← e.getAppFn.constName?
  let info ← Lean.Meta.getMatcherInfoCore? env matcherName
  if info.numDiscrs != 1 || info.numAlts != 1 then none else pure ()
  let altInfo ← info.altInfos[0]?
  if altInfo.numFields != 1 then none else pure ()
  let decl ← env.find? matcherName
  let discrType ← forallDomainAt? 32 info.getFirstDiscrPos decl.type
  let tyName ← discrType.consumeMData.getAppFn.constName?
  if !isUInt64Newtype env tyName then none else pure ()
  let args := e.getAppArgs
  let discr ← args[info.getFirstDiscrPos]?
  let alt ← args[info.getFirstAltPos]?
  match strip alt with
  | .lam _ _ body _ => some (body.instantiate1 discr)
  | _ => none

/-- 两构造子：一个 0 字段、一个 1 个 UInt64。按 Option 双叶展开。 -/
def isOptionLikeInductive (env : Environment) (tyName : Name) : Bool :=
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

def matcherDiscrTypeName? (env : Environment) (e : Expr) : Option Name := do
  let matcherName ← e.getAppFn.constName?
  let info ← Lean.Meta.getMatcherInfoCore? env matcherName
  if info.numDiscrs != 1 then none else pure ()
  let decl ← env.find? matcherName
  let discrType ← forallDomainAt? 32 info.getFirstDiscrPos decl.type
  discrType.consumeMData.getAppFn.constName?

def isOptionLikeMatcher (env : Environment) (e : Expr) : Bool :=
  match matcherDiscrTypeName? env e with
  | some tyName => tyName == ``Option || isOptionLikeInductive env tyName
  | none => false

def isUInt64VariantMatcher (env : Environment) (e : Expr) : Bool :=
  match matcherDiscrTypeName? env e with
  | some tyName => isUInt64Variant env tyName
  | none => false

def peelMatcherLams (fuel : Nat) (e : Expr) : Expr :=
  match fuel with
  | 0 => e
  | fuel' + 1 =>
    match strip e with
    | .lam _ _ body _ => peelMatcherLams fuel' body
    | e => e

def asLit (fuel : Nat) (e : Expr) : Option Ops.Val :=
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

def looksLikeOptionProj (env : Environment) (n : Name) : Bool :=
  match env.find? n with
  | some info => info.type.getUsedConstantsAsSet.toList.any (· == ``Option)
  | none => false

/-- `s.book.price` → 槽 `book_price`。动态向量投影保留逻辑叶名，稍后由 schema 解析。 -/
def flattenField (base : Ops.Val) (leaf : String) : Ops.Val :=
  match base with
  | .field b parent => .field b s!"{parent}_{leaf}"
  | b@(.indexGet ..) => .field b leaf
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
def isUserType (env : Environment) (n : Name) : Bool :=
  !isToolName n &&
    (isStructure env n ||
      match env.find? n with
      | some (.inductInfo _) => true
      | _ => false)

/-- 用户 structure / inductive 的投影 / 构造子。`UInt64.toNat`、`HSub.hSub` 不是。 -/
def isUserName (env : Environment) (n : Name) : Bool :=
  if isToolName n || isReservedProj (Core.IR.lastName n.toString) then
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

/-- Compiler-owned boundary carriers expose ordinary source projections even though they live in
the `ProofForge` namespace. Their target representation is still selected by the codec adapter.
The legacy bounded carriers remain explicit; reusable static SDK datatypes opt in once with
`@[pf_boundary]`, rather than adding every projection name here. -/
def isBoundaryProjectionName (env : Environment) (n : Name) : Bool :=
  n == ``ProofForge.Core.Value.BoundedVec.length ||
    n == ``ProofForge.Core.Value.BoundedVec.values ||
    n == ``ProofForge.Core.Value.BoundedBytes.length ||
    n == ``ProofForge.Core.Value.BoundedBytes.values ||
    n == ``ProofForge.Core.Value.BoundedString.length ||
    n == ``ProofForge.Core.Value.BoundedString.values ||
    Attr.isBoundary env n.getPrefix ||
    match env.getProjectionFnInfo? n with
    | some projection =>
        match env.find? projection.ctorName with
        | some (.ctorInfo ctor) => Attr.isBoundary env ctor.induct
        | _ => false
    | none => false

/-- Recover the schema path owned by nested user-structure projections.
`s.book.right` is represented by two projection applications but owns the flattened leaf
`book_right`; stopping at the terminal projection would collide with every other nested `right`. -/
private def projectionPath (env : Environment) (fuel : Nat) (e : Expr) : Option String :=
  match fuel with
  | 0 => none
  | fuel' + 1 => do
    let e := strip e
    let n ← e.getAppFn.constName?
    let _ ← env.getProjectionFnInfo? n
    if !isUserName env n && !isBoundaryProjectionName env n then none else
    let leaf := Core.IR.lastName n.toString
    let args := e.getAppArgs
    let parent :=
      if h : args.size > 0 then projectionPath env fuel' args[args.size - 1]
      else none
    match parent with
    | some parent => some s!"{parent}_{leaf}"
    | none => some leaf

/-- Trace an expression to the user projection whose result is the owning fixed vector. -/
def vectorBaseName (env : Environment) (fuel : Nat) (e : Expr) : Option String :=
  match fuel with
  | 0 => none
  | fuel' + 1 =>
    match e.getAppFn.constName? with
    | some n =>
      let last := Core.IR.lastName n.toString
      let skipTy :=
        match env.find? n with
        | some (.inductInfo _) => true
        | some (.ctorInfo _) => true
        | _ => false
      let returnsVector :=
        match env.find? n with
        | some info => info.type.getUsedConstantsAsSet.toList.any (· == ``Vector)
        | none => false
      if (!isUserName env n && !isBoundaryProjectionName env n) ||
          isReservedProj last || skipTy || !returnsVector then
        e.getAppArgs.findSome? (vectorBaseName env fuel')
      else projectionPath env fuel' e
    | none => e.getAppArgs.findSome? (vectorBaseName env fuel')

/--
Profile 已检查过且显式标记的用户 helper 按需 β 展开。控制流与 State
归一化共用这一个边界；未标记的定义不会因为碰巧能展开而进入 IR。
-/
def unfoldUserHelper (env : Environment) (e : Expr) : Option (Name × Expr) :=
  let e := strip e
  match e.getAppFn.constName? with
  | none => none
  | some n =>
    if Attr.isInline env n then
      match env.find? n with
      | some (.defnInfo info) => some (n, info.value.beta e.getAppArgs)
      | _ => none
    else none

/-- Bounded Source-facade unfold. Addr20 / UInt256 projections and `eq20` operands share this
so a new `@[pf_inline]` helper does not grow a per-recipe decoder. -/
def unfoldUserHelpers (env : Environment) : Nat → Expr → Expr
  | 0, e => e
  | fuel + 1, e =>
    match unfoldUserHelper env e with
    | some (_, unfolded) => unfoldUserHelpers env fuel unfolded
    | none => e

def resultType (fuel : Nat) (type : Expr) : Expr :=
  match fuel with
  | 0 => type
  | fuel' + 1 =>
    match strip type with
    | .forallE _ _ body _ => resultType fuel' body
    | type => type

def isScalarResult (env : Environment) (type : Expr) : Bool :=
  match (resultType 16 type).consumeMData.getAppFn.constName? with
  | some name =>
      name == ``UInt8 || name == ``UInt16 || name == ``UInt32 || name == ``UInt64 ||
        name == ``Bool || isUInt64Newtype env name
  | none => false

private def firstUserInputType (env : Environment) : Nat → Expr → Option Name
  | 0, _ => none
  | fuel + 1, type =>
      match strip type with
      | .forallE _ input body _ =>
          match input.consumeMData.getAppFn.constName? with
          | some name => if isUserType env name then some name else firstUserInputType env fuel body
          | none => firstUserInputType env fuel body
      | _ => none

/-- A marked structure helper is a state transition only when its result preserves the type of
its first user-typed input. This separates `State → … → State` updates from pure readers such as
`State → address → Node` without relying on declaration names. -/
def inlineHelperPreservesUserType (env : Environment) (name : Name) : Bool :=
  match env.find? name with
  | some (.defnInfo helper) =>
      match firstUserInputType env 16 helper.type,
          (resultType 16 helper.type).consumeMData.getAppFn.constName? with
      | some input, some output => input == output
      | _, _ => false
  | _ => false

/- Reduce projections through constructor literals and pure `pf_inline` descriptor builders. This
is the compile-time erasure boundary used by static account-storage handles: nested layout records
may improve source naming without constructing descriptors or carrying geometry at runtime. State
helpers are deliberately excluded because their projections own mutable transition semantics. -/
mutual
  private partial def normalizePureInlineToCtor? (env : Environment) (fuel : Nat)
      (ctorName : Name) (e : Expr) : Option Expr :=
    match fuel with
    | 0 => none
    | fuel' + 1 =>
      let e := strip e
      if e.getAppFn.constName? == some ctorName then some e
      else if let some reduced := reduceCtorProjectionFuel? env fuel' e then
        normalizePureInlineToCtor? env fuel' ctorName reduced
      else if let some (helper, unfolded) := unfoldUserHelper env e then
        if inlineHelperPreservesUserType env helper then none
        else normalizePureInlineToCtor? env fuel' ctorName (substLets fuel' unfolded)
      else none

  partial def reduceCtorProjectionFuel? (env : Environment) (fuel : Nat)
      (e : Expr) : Option Expr := do
    let fuel' ← match fuel with | 0 => none | fuel' + 1 => some fuel'
    let projection ← e.getAppFn.constName?
    let projectionInfo ← env.getProjectionFnInfo? projection
    let args := e.getAppArgs
    let base ← args[args.size - 1]?
    let ctor ← normalizePureInlineToCtor? env fuel' projectionInfo.ctorName base
    let .ctorInfo ctorInfo ← env.find? projectionInfo.ctorName | none
    let fields := ctor.getAppArgs
    if fields.size < ctorInfo.numFields || projectionInfo.i ≥ ctorInfo.numFields then none
    else fields[fields.size - ctorInfo.numFields + projectionInfo.i]?
end

private def reduceDirectCtorProjection? (env : Environment) (e : Expr) : Option Expr := do
  let projection ← e.getAppFn.constName?
  let projectionInfo ← env.getProjectionFnInfo? projection
  let args := e.getAppArgs
  let base ← args[args.size - 1]?
  let base := strip base
  let ctorName ← base.getAppFn.constName?
  if ctorName != projectionInfo.ctorName then none else pure ()
  let .ctorInfo ctor ← env.find? ctorName | none
  let fields := base.getAppArgs
  if fields.size < ctor.numFields || projectionInfo.i ≥ ctor.numFields then none
  else fields[fields.size - ctor.numFields + projectionInfo.i]?

def reduceCtorProjection? (env : Environment) (e : Expr) : Option Expr :=
  reduceDirectCtorProjection? env e <|> do
    let projection ← e.getAppFn.constName?
    let name := projection.toString
    if !name.startsWith "ProofForge.Svm.AccountStorage." &&
        !name.startsWith "ProofForge.Evm.HashedMap." &&
        !name.startsWith "ProofForge.Evm.ClosedCall." &&
        !name.startsWith "ProofForge.Evm.WideWord." &&
        !name.startsWith "ProofForge.Evm.NativeFx." &&
        !name.startsWith "MProd." &&
        !Attr.isInline env projection then none else pure ()
    reduceCtorProjectionFuel? env 64 e

private partial def normalizePureInlineCtorOf? (env : Environment) (fuel : Nat)
    (inductName : Name) (e : Expr) : Option Expr :=
  match fuel with
  | 0 => none
  | fuel' + 1 =>
    let e := strip e
    let isCtor :=
      match e.getAppFn.constName?.bind env.find? with
      | some (.ctorInfo ctor) => ctor.induct == inductName
      | _ => false
    if isCtor then some e
    else if let some reduced := reduceCtorProjectionFuel? env fuel' e then
      normalizePureInlineCtorOf? env fuel' inductName reduced
    else if let some (helper, unfolded) := unfoldUserHelper env e then
      if inlineHelperPreservesUserType env helper then none
      else normalizePureInlineCtorOf? env fuel' inductName (substLets fuel' unfolded)
    else none

/-- Iota-reduce a matcher only when its sole discriminant is a constructor literal obtained
through pure marked descriptor builders. The structural gate lets new static Queue/Map/Allocator
facades reuse descriptor erasure without adding their namespaces here; dynamic contract variants,
recursive inductives, and state-preserving helpers keep their existing explicit lowering. -/
def reducePureInlineMatch? (env : Environment) (e : Expr) : Option Expr := do
  let matcherName ← e.getAppFn.constName?
  let matcher ← Lean.Meta.getMatcherInfoCore? env matcherName
  if matcher.numDiscrs != 1 then none else pure ()
  let decl ← env.find? matcherName
  let discrType ← forallDomainAt? 32 matcher.getFirstDiscrPos decl.type
  let inductName ← discrType.consumeMData.getAppFn.constName?
  let .inductInfo induct ← env.find? inductName | none
  if induct.isRec then none else pure ()
  let args := e.getAppArgs
  let discrExpr ← args[matcher.getFirstDiscrPos]?
  let discr ← normalizePureInlineCtorOf? env 64 inductName discrExpr
  let ctorName ← discr.getAppFn.constName?
  let some altIndex := induct.ctors.findIdx? (· == ctorName) | none
  let alt ← args[matcher.getFirstAltPos + altIndex]?
  let .ctorInfo ctor ← env.find? ctorName | none
  let ctorArgs := discr.getAppArgs
  if ctorArgs.size < ctor.numFields then none
  else
    let branch := alt.beta (ctorArgs.extract (ctorArgs.size - ctor.numFields) ctorArgs.size)
    if ctor.numFields == 0 then
      match strip branch with
      | .lam _ type body _ =>
          if type.consumeMData.getAppFn.constName? == some ``Unit then
            some (body.instantiate1 (mkConst ``Unit.unit))
          else some branch
      | _ => some branch
    else some branch

private partial def staticBool? (env : Environment) (fuel : Nat) (e : Expr) : Option Bool :=
  match fuel with
  | 0 => none
  | fuel' + 1 =>
    let e := strip e
    if let some ctor := normalizePureInlineCtorOf? env fuel' ``Bool e then
      if ctor.getAppFn.constName? == some ``Bool.true then some true
      else if ctor.getAppFn.constName? == some ``Bool.false then some false
      else none
    else if (isConstNamed e ``Eq || isConstNamed e ``BEq.beq) && e.getAppArgs.size ≥ 2 then
      let args := e.getAppArgs
      match staticBool? env fuel' args[args.size - 2]!,
          staticBool? env fuel' args[args.size - 1]! with
      | some left, some right => some (left == right)
      | _, _ => none
    else none

private partial def staticNat? (env : Environment) (fuel : Nat) (e : Expr) : Option Nat :=
  match fuel with
  | 0 => none
  | fuel' + 1 =>
    let e := strip e
    match e with
    | .lit (.natVal value) => some value
    | _ =>
      if let some reduced := reduceCtorProjectionFuel? env fuel' e then
        staticNat? env fuel' reduced
      else if isConstNamed e ``OfNat.ofNat then
        e.getAppArgs.findSome? (staticNat? env fuel')
      else if isConstNamed e ``String.length && !e.getAppArgs.isEmpty then
        match strip e.getAppArgs[e.getAppArgs.size - 1]! with
        | .lit (.strVal value) => some value.length
        | _ => none
      else if (isConstNamed e ``HAdd.hAdd || isConstNamed e ``Nat.add) &&
          e.getAppArgs.size ≥ 2 then
        let args := e.getAppArgs
        match staticNat? env fuel' args[args.size - 2]!,
            staticNat? env fuel' args[args.size - 1]! with
        | some left, some right => some (left + right)
        | _, _ => none
      else if (isConstNamed e ``HMul.hMul || isConstNamed e ``Nat.mul) &&
          e.getAppArgs.size ≥ 2 then
        let args := e.getAppArgs
        match staticNat? env fuel' args[args.size - 2]!,
            staticNat? env fuel' args[args.size - 1]! with
        | some left, some right => some (left * right)
        | _, _ => none
      else if isConstNamed e ``ite && e.getAppArgs.size ≥ 4 then
        let args := e.getAppArgs
        match staticBool? env fuel' args[args.size - 4]! with
        | some true => staticNat? env fuel' args[args.size - 2]!
        | some false => staticNat? env fuel' args[args.size - 1]!
        | none => none
      else if let some (helper, unfolded) := unfoldUserHelper env e then
        if inlineHelperPreservesUserType env helper then none else staticNat? env fuel' unfolded
      else none

/-- Read a scalar literal through the static Nat geometry used by source storage descriptors. -/
def asStaticLit (env : Environment) (fuel : Nat) (e : Expr) : Option Ops.Val :=
  asLit fuel e <|> do
    let value ←
      if isConstNamed e ``UInt64.ofNat && !e.getAppArgs.isEmpty then
        staticNat? env fuel e.getAppArgs[e.getAppArgs.size - 1]!
      else
        staticNat? env fuel e
    if value < UInt64.size then some (.lit (UInt64.ofNat value)) else none

/-- EVM map namespaces are closed storage-layout descriptors, never runtime arithmetic. -/
private partial def closedU64? : Ops.Val → Option UInt64
  | .lit value => some value
  | .addU64 left right => return (← closedU64? left) + (← closedU64? right)
  | .subU64 left right => return (← closedU64? left) - (← closedU64? right)
  | .mulU64 left right => return (← closedU64? left) * (← closedU64? right)
  | _ => none

def foldClosedU64 (value : Ops.Val) : Ops.Val :=
  (closedU64? value).map (.lit ·) |>.getD value

def asEvmMapBaseLit (env : Environment) (fuel : Nat) (e : Expr) : Option Ops.Val :=
  ((asLit fuel e).bind fun value => closedU64? value |>.map (.lit ·)) <|> do
    let value ←
      if isConstNamed e ``UInt64.ofNat && !e.getAppArgs.isEmpty then
        staticNat? env fuel e.getAppArgs[e.getAppArgs.size - 1]!
      else
        staticNat? env fuel e
    if value < UInt64.size then some (.lit (UInt64.ofNat value)) else none

/-- Reduce a projection over a marked structure helper without guessing from its name. A helper
whose first user-typed input and result have the same type is a State transition already emitted
by `decodeYieldState`, so its projection reads the current mutable source. Other helpers are pure
structure readers (for example a vector-node lookup), so project from their unfolded value. -/
def reduceInlineProjection? (env : Environment) (e : Expr) : Option Expr := do
  let projection ← e.getAppFn.constName?
  let _ ← env.getProjectionFnInfo? projection
  let args := e.getAppArgs
  let base ← args[args.size - 1]?
  let (helperName, unfolded) ← unfoldUserHelper env base
  let baseArgs := base.getAppArgs
  let source ← baseArgs[0]?
  let replacement :=
    if inlineHelperPreservesUserType env helperName then source else unfolded
  return e.replace fun child => if child == base then some replacement else none

def staticUInt64? : Ops.Val → Option UInt64
  | .lit value => some value
  | .bitNot value => staticUInt64? value |>.map (~~~·)
  | _ => none

/-- Decode a literal `#[...]` without interpreting its element type. Kept before `asVal` so
compile-time PDA seed lists can be values as well as CPI operands. -/
private def asStaticArrayElems (e : Expr) : Option (Array Expr) :=
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
    fromList 32 e.getAppArgs[e.getAppArgs.size - 1]! #[]
  else if isConstNamed e ``List.toArray && e.getAppArgs.size ≥ 1 then
    fromList 32 e.getAppArgs[e.getAppArgs.size - 1]! #[]
  else if isConstNamed e ``Array.empty || endsWith e ".empty" then
    some #[]
  else none

private def asPdaSeed (e : Expr) : Option Ops.PdaSeed :=
  let e := strip e
  if isConstNamed e ``ProofForge.Svm.Runtime.PdaSeed.ascii || endsWith e ".ascii" then
    if e.getAppArgs.size ≥ 1 then
      match strip e.getAppArgs[e.getAppArgs.size - 1]! with
      | .lit (.strVal value) => if value.isEmpty then none else some (.ascii value)
      | _ => none
    else none
  else if isConstNamed e ``ProofForge.Svm.Runtime.PdaSeed.stateKey || endsWith e ".stateKey" then
    some .stateKey
  else if isConstNamed e ``ProofForge.Svm.Runtime.PdaSeed.accKey || endsWith e ".accKey" then
    if e.getAppArgs.size ≥ 1 then
      match asLit 8 e.getAppArgs[e.getAppArgs.size - 1]! with
      | some (.lit i) => some (.accKey i.toNat)
      | _ => none
    else none
  else if isConstNamed e ``ProofForge.Svm.Runtime.PdaSeed.accData || endsWith e ".accData" then
    if e.getAppArgs.size ≥ 3 then
      let args := e.getAppArgs
      match asLit 8 args[args.size - 3]!, asLit 8 args[args.size - 2]!,
          asLit 8 args[args.size - 1]! with
      | some (.lit account), some (.lit offset), some (.lit length) =>
          some (.accData account.toNat offset.toNat length.toNat)
      | _, _, _ => none
    else none
  else none

def asPdaSeeds (e : Expr) : Option (Array Ops.PdaSeed) := do
  let elems ← asStaticArrayElems e
  elems.mapM asPdaSeed


end ProofForge.Extract
