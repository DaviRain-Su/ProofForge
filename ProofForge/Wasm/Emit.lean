import ProofForge.Wasm.IR
import ProofForge.Wasm.Host

/-!
# WASM 家族发射器（链共享）

把一个家族 IR 程序发射成 Rust 源：checked 五则 → `checked_*` + 钉死错误码
（1 overflow/underflow、2 divide-by-zero），guard 算术用显式 `wrapping_*`
（不依赖 cargo debug/release 剖面），`ite` → `if/else`，flat region 语义与
CFG 的成功/溢出/退出形状一致。

链间差异——存储、host function、SDK / 入口 ABI——全部经
`Wasm.Host.Contract` 注入；本模块不含任何链特化文本。
-/

namespace ProofForge.Wasm.Emit

open ProofForge.Wasm.IR (Program Method Val Op Cmp)
open ProofForge.Wasm.Host (Contract)

def rustLit (n : UInt64) : String := s!"{n.toNat}u64"

def cmpSym : Cmp → String
  | .eq => "==" | .ne => "!=" | .lt => "<"
  | .le => "<=" | .gt => ">" | .ge => ">="

def ob : String := "{"
def cb : String := "}"

def indent (n : Nat) (s : String) : String :=
  String.ofList (List.replicate n ' ') ++ s

def paramList (count : Nat) : String :=
  String.intercalate ", " ((List.range count).map (fun i => s!"pf_p{i}: u64"))

variable {ValExt : Type} {OpExt : Type → Type}

/-- Renderer state: fresh temp counter, last materialized value, and the state field the
last checked operation writes into (mirrors the EVM emitter's dest/last contract). -/
private structure EState where
  paramCount : Nat
  fresh : Nat := 0
  last : Option String := none
  pendingDest : Option String := none
  deriving Inhabited

private def fieldOf : Val ValExt → Option String
  | .field (.arg _) name => some name
  | _ => none

private def renderVal (st : EState) (v : Val ValExt) : Except String String :=
  match v with
  | .lit n => .ok (rustLit n)
  | .arg i =>
      if i < st.paramCount then .ok s!"pf_p{i}"
      else .error "extract/unsupported: wasm v0 rejects bare state argument"
  | .field (.arg i) name =>
      if i < st.paramCount then
        .error "extract/unsupported: wasm v0 rejects aggregate parameter projections"
      else .ok s!"{name}_cur"
  | .select cmp lhs rhs thn els => do
      let l ← renderVal st lhs
      let r ← renderVal st rhs
      let t ← renderVal st thn
      let f ← renderVal st els
      return s!"(if {l} {cmpSym cmp} {r} {ob} {t} {cb} else {ob} {f} {cb})"
  | .addU64 lhs rhs => do
      let l ← renderVal st lhs
      let r ← renderVal st rhs
      return s!"({l}).wrapping_add({r})"
  | .subU64 lhs rhs => do
      let l ← renderVal st lhs
      let r ← renderVal st rhs
      return s!"({l}).wrapping_sub({r})"
  | .mulU64 lhs rhs => do
      let l ← renderVal st lhs
      let r ← renderVal st rhs
      return s!"({l}).wrapping_mul({r})"
  | _ => .error "extract/unsupported: wasm v0 value"

/-- Rust method and pinned error code for one checked operation. -/
private def checkedInfo : Op ValExt OpExt → Option (String × Nat)
  | .checkedAddU64 .. => some ("checked_add", 1)
  | .checkedSubU64 .. => some ("checked_sub", 1)
  | .checkedMulU64 .. => some ("checked_mul", 1)
  | .checkedDivU64 .. => some ("checked_div", 2)
  | .checkedModU64 .. => some ("checked_rem", 2)
  | _ => none

private def isExitOp : Op ValExt OpExt → Bool
  | .okState _ | .errorOverflow | .errorNamed _ | .returnU64 _ | .returnState _ => true
  | _ => false

private structure Region where
  lines : Array String := #[]
  st : EState
  terminal : Bool := false

/-- Collect one value plus every directly following `returnU64` into a multi-value return
(mirrors the CFG `returnU64s` grouping), returning the remaining tail. -/
private def collectReturnU64s (first : Val ValExt) (rest : List (Op ValExt OpExt)) :
    Array (Val ValExt) × List (Op ValExt OpExt) :=
  let rec go (acc : Array (Val ValExt)) (rest : List (Op ValExt OpExt)) :
      Array (Val ValExt) × List (Op ValExt OpExt) :=
    match rest with
    | .returnU64 next :: more => go (acc.push next) more
    | _ => (acc, rest)
  go #[first] rest

/-- Render one flat region: ops until the first terminal exit; trailing exits are dead
(the CFG already validated that shape). `defaultSlot` is the fallback destination for
`okState` values that name no field. -/
private partial def emitRegion (host : Contract) (view : Bool) (level : Nat)
    (defaultSlot : String) (ops : List (Op ValExt OpExt)) (st : EState) :
    Except String Region := do
  match ops with
  | [] =>
      if view then
        throw "extract/unsupported: wasm v0 view region must end in a return"
      else
        throw "extract/unsupported: wasm v0 mutating region must end in a state or error exit"
  | op :: tail =>
    match op with
    | .checkedAddU64 lhs rhs | .checkedSubU64 lhs rhs | .checkedMulU64 lhs rhs
    | .checkedDivU64 lhs rhs | .checkedModU64 lhs rhs =>
        match checkedInfo op with
        | some (method, code) =>
            let l ← renderVal st lhs
            let r ← renderVal st rhs
            let temp := s!"pf_r{st.fresh}"
            let line := indent level s!"let {temp} = ({l}).{method}({r}).ok_or({code}i32)?;"
            let dest' := (fieldOf lhs).orElse (fun _ => st.pendingDest)
            let st' := { st with fresh := st.fresh + 1, last := some temp, pendingDest := dest' }
            let region ← emitRegion host view level defaultSlot tail st'
            return { lines := #[line] ++ region.lines, st := region.st, terminal := true }
        | none => throw "extract/unsupported: wasm v0 checked operation"
    | .ite cmp lhs rhs thn els =>
        let l ← renderVal st lhs
        let r ← renderVal st rhs
        let head := indent level s!"if {l} {cmpSym cmp} {r} {ob}"
        let thenRegion ← emitRegion host view (level + 4) defaultSlot thn.toList
          { st with last := none, pendingDest := none }
        unless thenRegion.terminal do
          throw "extract/unsupported: wasm v0 ite branch must end in a terminal"
        let elseRegion ← emitRegion host view (level + 4) defaultSlot els.toList
          { st with fresh := thenRegion.st.fresh, last := none, pendingDest := none }
        unless elseRegion.terminal do
          throw "extract/unsupported: wasm v0 ite branch must end in a terminal"
        if tail.isEmpty || tail.all isExitOp then
          -- Both branches exit and no continuation follows: the CFG continuation is
          -- unreachable, so the ite itself terminates the region.
          return {
            lines := #[head] ++ thenRegion.lines ++ #[indent level "} else {"] ++
              elseRegion.lines ++ #[indent level "}"]
            st := elseRegion.st
            terminal := true
          }
        let region ← emitRegion host view level defaultSlot tail
          { st with fresh := elseRegion.st.fresh, last := none, pendingDest := none }
        return {
          lines := #[head] ++ thenRegion.lines ++ #[indent level "} else {"] ++
            elseRegion.lines ++ #[indent level "}"] ++ region.lines
          st := region.st
          terminal := true
        }
    | .storeField name value =>
        let v ← renderVal st value
        let line := indent level s!"{host.writeSlot}({(host.slotKey name)}, {v})?;"
        let region ← emitRegion host view level defaultSlot tail
          { st with last := some v, pendingDest := some name }
        return { lines := #[line] ++ region.lines, st := region.st, terminal := true }
    | .okState value | .returnState value =>
        if view then throw "extract/unsupported: wasm v0 view cannot write state"
        let dest := st.pendingDest <|> fieldOf value |>.getD defaultSlot
        let v ← match st.last with
          | some e => .ok e
          | none => renderVal st value
        unless tail.all isExitOp do
          throw "extract/unsupported: wasm v0 instructions follow terminal operation"
        return {
          lines := #[indent level s!"{host.writeSlot}({(host.slotKey dest)}, {v})?;",
            indent level "Ok(0)"]
          st, terminal := true
        }
    | .errorOverflow =>
        if view then throw "extract/unsupported: wasm v0 view cannot fail"
        unless tail.all isExitOp do
          throw "extract/unsupported: wasm v0 instructions follow terminal operation"
        return { lines := #[indent level "Err(1i32)"], st, terminal := true }
    | .returnU64 value =>
        unless view do
          throw "extract/unsupported: wasm v0 mutating region cannot return a value"
        let (values, skipped) := collectReturnU64s value tail
        unless skipped.all isExitOp do
          throw "extract/unsupported: wasm v0 instructions follow terminal operation"
        let mut rendered := #[]
        for v in values do
          rendered := rendered.push (← renderVal st v)
        let inner := String.intercalate ", " rendered.toList
        return { lines := #[indent level inner], st, terminal := true }
    | _ => throw "extract/unsupported: wasm v0 op"

/-- State fields read by one method: `.field (.arg i) name` with `i ≥ paramCount`. -/
partial def touchedFields
    (paramCount : Nat) (ops : Array (Op ValExt OpExt)) : Array String :=
  let rec walkVal (acc : Array String) : Val ValExt → Array String
    | .field (.arg i) name => if i ≥ paramCount && !acc.contains name then acc.push name else acc
    | .field base _ => walkVal acc base
    | .select _ lhs rhs thn els =>
        walkVal (walkVal (walkVal (walkVal acc lhs) rhs) thn) els
    | .addU64 lhs rhs | .subU64 lhs rhs | .mulU64 lhs rhs
    | .divU64 lhs rhs | .modU64 lhs rhs => walkVal (walkVal acc lhs) rhs
    | _ => acc
  let rec walkOp (acc : Array String) : Op ValExt OpExt → Array String
    | .checkedAddU64 lhs rhs | .checkedSubU64 lhs rhs | .checkedMulU64 lhs rhs
    | .checkedDivU64 lhs rhs | .checkedModU64 lhs rhs => walkVal (walkVal acc lhs) rhs
    | .ite _ lhs rhs thn els =>
        let acc := walkVal (walkVal acc lhs) rhs
        let acc := (thn.foldl walkOp acc)
        (els.foldl walkOp acc)
    | .storeField _ value | .okState value | .returnState value | .returnU64 value =>
        walkVal acc value
    | _ => acc
  ops.foldl walkOp #[]

private def defaultSlotOf (p : Program ValExt OpExt) : String :=
  (p.slots[0]?).map (·.name) |>.getD "slot0"

private def slotLoads (host : Contract) (paramCount : Nat)
    (ops : Array (Op ValExt OpExt)) : Array String :=
  (touchedFields paramCount ops).map fun field =>
    indent 4 s!"let {field}_cur = {host.readSlot}({(host.slotKey field)});"

private def renderMutatingFn (host : Contract) (p : Program ValExt OpExt)
    (method : Method ValExt OpExt) : Except String (Array String) := do
  let st : EState := { paramCount := method.paramCount }
  let region ← emitRegion host false 8 (defaultSlotOf p) method.ops.toList st
  unless region.terminal do
    throw s!"extract/unsupported: {method.ixName} does not end in a terminal"
  return host.wrapMutating method.ixName (paramList method.paramCount) method.echoDropped
    (slotLoads host method.paramCount method.ops) region.lines

private def renderViewFn (host : Contract) (p : Program ValExt OpExt)
    (method : Method ValExt OpExt) : Except String (Array String) := do
  match method.tupleArity with
  | none => throw s!"extract/unsupported: {method.ixName} view lacks a value ABI"
  | some _arity =>
    let st : EState := { paramCount := method.paramCount }
    let region ← emitRegion host true 4 (defaultSlotOf p) method.ops.toList st
    unless region.terminal do
      throw s!"extract/unsupported: {method.ixName} does not end in a terminal"
    return host.wrapView method.ixName (paramList method.paramCount)
      (slotLoads host method.paramCount method.ops) region.lines

/-- Render one program as a complete Rust source in the chain's dialect. The digest line
pins the canonical IR identity of the artifact; storage, imports, and entry ABI all come
from the chain's host contract. -/
def emit (host : Contract)
    (extValCanon : ValExt → String) (extOpCanon : OpExt (Val ValExt) → String)
    (p : Program ValExt OpExt) : Except String String := do
  let mut lines : Array String := #[]
  lines := lines.push s!"// {host.headerTag}"
  lines := lines.push s!"// digest={IR.digestHex host.digestDomain extValCanon extOpCanon p}"
  for note in host.headerNotes do
    lines := lines.push note
  for prelude in host.prelude do
    lines := lines.push prelude
  lines := lines.push ""
  for slot in p.slots do
    lines := lines.push s!"const {(host.slotKey slot.name)}: &str = \"{slot.name}\";"
  unless p.slots.isEmpty do
    lines := lines.push ""
  lines := lines ++ host.storageHelpers
  lines := lines.push ""
  lines := lines ++ (← renderMutatingFn host p p.initializer)
  lines := lines.push ""
  for method in p.entries do
    lines := lines ++ (←
      if method.tupleArity.isSome then renderViewFn host p method
      else renderMutatingFn host p method)
    lines := lines.push ""
  return String.intercalate "\n" lines.toList ++ "\n"

end ProofForge.Wasm.Emit
