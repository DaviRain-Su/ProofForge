import Lean

open Lean

namespace ProofForge.Profile

inductive Decision where
  | accept
  | reject (reason : String)
  deriving BEq, Repr, Inhabited

/-- 保留方法名，只做标识符门，不是闭包检查。 -/
def isReservedMethodName (name : String) : Bool :=
  name == "init" || name == "increment" || name == "get"

def checkRootName (name : String) : Decision :=
  if isReservedMethodName name then
    .accept
  else
    .reject s!"profile/rejected: {name}"

private def maxClosure : Nat := 4096

private def forbiddenTypeConst : Name → Option String
  | ``IO => some "IO"
  | ``EIO => some "EIO"
  | ``Task => some "Task"
  | ``BaseIO => some "BaseIO"
  | _ => none

/-- 用户模块声明才施加 extern/opaque/implemented_by 门。
Lean/Std/Init 以及 prelude 类型（`UInt64.ofNat`）不算用户代码。
任意 Lake 包里的合约（仓库内 `Examples` 或外部包）都算。 -/
private def isFrameworkRoot (n : Name) : Bool :=
  n == `Lean || n == `Std || n == `Init || n == `IO || n == `System ||
    n == `Lake || n == `UInt8 || n == `UInt16 || n == `UInt32 || n == `UInt64 ||
    n == `Bool || n == `Nat || n == `String || n == `Char || n == `ByteArray ||
    n == `Array || n == `List || n == `Option || n == `Except || n == `Prod ||
    n == `Vector || n == `BitVec || n == `Int || n == `Fin || n == `Name ||
    n == `Unit || n == `True || n == `False || n == `Eq || n == `HAdd ||
    n == `HSub || n == `HMul || n == `HDiv || n == `HMod || n == `HAnd ||
    n == `HOr || n == `HXor || n == `HShiftLeft || n == `HShiftRight ||
    n == `Complement || n == `LE || n == `LT || n == `GE || n == `GT ||
    n == `BEq || n == `Decidable || n == `DecidableEq || n == `Inhabited ||
    n == `Repr || n == `OfNat || n == `ForIn || n == `Id ||
    n == `panicCore || n == `panicWithPos || n == `outOfBounds ||
    n == `Float || n == `Float32 || n == `USize

private def isUserDecl (n : Name) : Bool :=
  match n with
  | .str p _ =>
    let head := n.getRoot
    -- `floatSpec` / `UInt64.ofNat`：父匿名，或根是 prelude 类型。
    -- `Examples.Counter.init`、`Acme.Swap.buy`：有模块路径。
    !head.isAnonymous && !isFrameworkRoot head && !p.isAnonymous
  | .num p _ =>
    let head := n.getRoot
    !head.isAnonymous && !isFrameworkRoot head && !p.isAnonymous
  | .anonymous => false

private def enqueueUsed (used : NameSet) (queue : Array Name) (seen : NameSet) :
    Array Name × NameSet :=
  used.toList.foldl (init := (queue, seen)) fun (q, s) n =>
    if s.contains n then (q, s) else (q.push n, s.insert n)

private def visit
    (env : Environment) (fuel : Nat)
    (queue : Array Name) (idx : Nat) (seen : NameSet) (out : Array Name) :
    Except String (Array Name) :=
  match fuel with
  | 0 => .error "profile/rejected: closure exceeds 4096"
  | fuel' + 1 =>
    if h : idx < queue.size then
      if out.size ≥ maxClosure then
        .error "profile/rejected: closure exceeds 4096"
      else
        let n := queue[idx]
        match env.find? n with
        | none => .error s!"profile/rejected: unknown {n}"
        | some info =>
          let out := out.push n
          let (queue, seen) := enqueueUsed info.getUsedConstantsAsSet queue seen
          let (queue, seen) :=
            match info with
            | .inductInfo v =>
              v.ctors.foldl (init := (queue, seen)) fun (q, s) ctor =>
                if s.contains ctor then (q, s) else (q.push ctor, s.insert ctor)
            | _ => (queue, seen)
          visit env fuel' queue (idx + 1) seen out
    else
      .ok out

/-- 传递闭包：定义体 + 类型 + inductive 构造子。找不到的常量直接拒绝。 -/
def collectClosure (env : Environment) (root : Name) : Except String (Array Name) :=
  visit env maxClosure #[root] 0 (({} : NameSet).insert root) #[]

/--
可执行闭包检查。拒绝 partial / unsafe / opaque / extern / implemented_by /
可执行 axiom（含 sorry）/ IO·Task 类型 / 入口类型里的 `Nat`。
-/
def check (env : Environment) (root : Name) : Decision :=
  match collectClosure env root with
  | .error reason => .reject reason
  | .ok names => Id.run do
      match env.find? root with
      | none => return .reject s!"profile/rejected: unknown {root}"
      | some rootInfo =>
        if rootInfo.type.getUsedConstantsAsSet.contains ``Nat then
          return .reject s!"profile/rejected: Nat in root type {root}"
      for n in names do
        let some info := env.find? n
          | return .reject s!"profile/rejected: unknown {n}"
        if info.isPartial then
          return .reject s!"profile/rejected: partial {n}"
        if isUserDecl n && n != ``sorryAx then
          if info.isUnsafe then
            return .reject s!"profile/rejected: unsafe {n}"
          if (getExternAttrData? env n).isSome then
            return .reject s!"profile/rejected: extern {n}"
          if (Compiler.getImplementedBy? env n).isSome then
            return .reject s!"profile/rejected: implemented_by {n}"
          match info with
          | .defnInfo v =>
            if v.safety == .partial then
              return .reject s!"profile/rejected: partial {n}"
          | .opaqueInfo _ =>
            return .reject s!"profile/rejected: partial {n}"
          | .axiomInfo v =>
            -- kernel 公理（propext / Quot.sound）放行；用户 sorry 走 sorryAx。
            if v.name == ``sorryAx then
              return .reject s!"profile/rejected: axiom {v.name}"
          | _ => pure ()
        if n == ``sorryAx then
          return .reject s!"profile/rejected: axiom sorryAx"
        let used := info.getUsedConstantsAsSet
        if let some tag := used.toList.findSome? forbiddenTypeConst then
          return .reject s!"profile/rejected: {tag} in {n}"
      return .accept

def checkAll (env : Environment) (roots : Array Name) : Decision :=
  Id.run do
    for root in roots do
      match check env root with
      | .reject reason => return .reject reason
      | .accept => pure ()
    return .accept

end ProofForge.Profile
