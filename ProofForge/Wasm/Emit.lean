import ProofForge.Wasm.IR
import ProofForge.Wasm.Host

/-!
# WASM 家族发射器（链共享）

Core IR → WAT：checked 五则是显式 `i64` 溢出检查 + 钉死错误码（1 overflow/
underflow、2 divide-by-zero），guard 算术是裸 `i64.add/sub/mul`，`ite` →
`if`。链间差异——host import 表、存储布局——经 `Wasm.Host.Contract` 注入。
-/

namespace ProofForge.Wasm.Emit

open ProofForge.Wasm.IR (Program Method Val Op Cmp)
open ProofForge.Wasm.Host (Contract)

def indent (n : Nat) (s : String) : String :=
  String.ofList (List.replicate n ' ') ++ s

variable {ValExt : Type} {OpExt : Type → Type}

private def cmpInstr : Cmp → String
  | .eq => "i64.eq" | .ne => "i64.ne" | .lt => "i64.lt_u"
  | .le => "i64.le_u" | .gt => "i64.gt_u" | .ge => "i64.ge_u"

private structure EState where
  paramCount : Nat
  fresh : Nat := 0
  last : Option String := none
  pendingDest : Option String := none
  deriving Inhabited

private def fieldOf : Val ValExt → Option String
  | .field (.arg _) name => some name
  | _ => none

private def localOfArg (i : Nat) : String := "$pf_p" ++ toString i

private def localOfSlot (name : String) : String := "$" ++ name

private def localOfTemp (i : Nat) : String := "$pf_r" ++ toString i

private partial def renderVal (st : EState) (v : Val ValExt) : Except String String :=
  match v with
  | .lit n => .ok ("(i64.const " ++ toString n.toNat ++ ")")
  | .arg i =>
      if i < st.paramCount then .ok ("(local.get " ++ localOfArg i ++ ")")
      else .error "extract/unsupported: wasm v0 rejects bare state argument"
  | .field (.arg i) name =>
      if i < st.paramCount then
        .error "extract/unsupported: wasm v0 rejects aggregate parameter projections"
      else .ok ("(local.get " ++ localOfSlot name ++ ")")
  | .select cmp lhs rhs thn els => do
      let l ← renderVal st lhs
      let r ← renderVal st rhs
      let t ← renderVal st thn
      let f ← renderVal st els
      return ("(if (result i64) (" ++ cmpInstr cmp ++ " " ++ l ++ " " ++ r ++
        ") (then " ++ t ++ ") (else " ++ f ++ "))")
  | .addU64 lhs rhs => do
      let l ← renderVal st lhs
      let r ← renderVal st rhs
      return ("(i64.add " ++ l ++ " " ++ r ++ ")")
  | .subU64 lhs rhs => do
      let l ← renderVal st lhs
      let r ← renderVal st rhs
      return ("(i64.sub " ++ l ++ " " ++ r ++ ")")
  | .mulU64 lhs rhs => do
      let l ← renderVal st lhs
      let r ← renderVal st rhs
      return ("(i64.mul " ++ l ++ " " ++ r ++ ")")
  | _ => .error "extract/unsupported: wasm v0 value"

private def isExitOp : Op ValExt OpExt → Bool
  | .okState _ | .errorOverflow | .errorNamed _ | .returnU64 _ | .returnState _ => true
  | _ => false

private def collectReturnU64s (first : Val ValExt) (rest : List (Op ValExt OpExt)) :
    Array (Val ValExt) × List (Op ValExt OpExt) :=
  let rec go (acc : Array (Val ValExt)) (rest : List (Op ValExt OpExt)) :
      Array (Val ValExt) × List (Op ValExt OpExt) :=
    match rest with
    | .returnU64 next :: more => go (acc.push next) more
    | _ => (acc, rest)
  go #[first] rest

private def slotOffset (p : Program ValExt OpExt) (name : String) : Nat :=
  match p.slots.findIdx? (·.name == name) with
  | some i => i * 8
  | none => 0

private def blobLen (p : Program ValExt OpExt) : Nat :=
  p.slots.size * 8

private def storeSlotInstr (p : Program ValExt OpExt) (name expr : String) : String :=
  "(i64.store (i32.const " ++ toString (slotOffset p name) ++ ") " ++ expr ++ ")"

private def dumpSlots (p : Program ValExt OpExt) (level : Nat) : Array String :=
  p.slots.map fun slot =>
    indent level (storeSlotInstr p slot.name ("(local.get " ++ localOfSlot slot.name ++ ")"))

private def hostWrite (host : Contract) (p : Program ValExt OpExt) (level : Nat) :
    Array String :=
  let blob := blobLen p
  #[
    indent level ("(local.set $st (call $" ++ host.setData ++
      " (i32.const 0) (i32.const " ++ toString blob ++ ")))"),
    indent level "(if (i32.lt_s (local.get $st) (i32.const 0))",
    indent (level + 2) "(then (return (local.get $st))))"
  ]

private structure Region where
  lines : Array String := #[]
  st : EState
  terminal : Bool := false

/-- Emit checked unsigned i64 op into `$pf_r{fresh}`; overflow/zero returns the pinned code. -/
private def emitChecked (st : EState) (kind : String) (lhs rhs : String) :
    Except String (Array String × EState) := do
  let temp := localOfTemp st.fresh
  let st' := { st with fresh := st.fresh + 1, last := some temp }
  match kind with
  | "add" =>
      let lines := #[
        "(local.set " ++ temp ++ " (i64.add " ++ lhs ++ " " ++ rhs ++ "))",
        "(if (i64.lt_u (local.get " ++ temp ++ ") " ++ lhs ++ ")",
        "  (then (return (i32.const 1))))"
      ]
      return (lines, st')
  | "sub" =>
      let lines := #[
        "(if (i64.lt_u " ++ lhs ++ " " ++ rhs ++ ")",
        "  (then (return (i32.const 1))))",
        "(local.set " ++ temp ++ " (i64.sub " ++ lhs ++ " " ++ rhs ++ "))"
      ]
      return (lines, st')
  | "mul" =>
      let lines := #[
        "(if (i64.eqz " ++ lhs ++ ")",
        "  (then (local.set " ++ temp ++ " (i64.const 0)))",
        "  (else",
        "    (if (i64.gt_u " ++ rhs ++ " (i64.div_u (i64.const -1) " ++ lhs ++ "))",
        "      (then (return (i32.const 1)))",
        "      (else (local.set " ++ temp ++ " (i64.mul " ++ lhs ++ " " ++ rhs ++ "))))))"
      ]
      return (lines, st')
  | "div" =>
      let lines := #[
        "(if (i64.eqz " ++ rhs ++ ")",
        "  (then (return (i32.const 2))))",
        "(local.set " ++ temp ++ " (i64.div_u " ++ lhs ++ " " ++ rhs ++ "))"
      ]
      return (lines, st')
  | "rem" =>
      let lines := #[
        "(if (i64.eqz " ++ rhs ++ ")",
        "  (then (return (i32.const 2))))",
        "(local.set " ++ temp ++ " (i64.rem_u " ++ lhs ++ " " ++ rhs ++ "))"
      ]
      return (lines, st')
  | _ => throw "extract/unsupported: wasm v0 checked operation"

private def checkedKind : Op ValExt OpExt → Option String
  | .checkedAddU64 .. => some "add"
  | .checkedSubU64 .. => some "sub"
  | .checkedMulU64 .. => some "mul"
  | .checkedDivU64 .. => some "div"
  | .checkedModU64 .. => some "rem"
  | _ => none

private partial def emitRegion (host : Contract) (p : Program ValExt OpExt)
    (view : Bool) (level : Nat) (defaultSlot : String)
    (ops : List (Op ValExt OpExt)) (st : EState) : Except String Region := do
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
        if view then throw "extract/unsupported: wasm v0 view cannot fail"
        match checkedKind op with
        | some kind =>
            let l ← renderVal st lhs
            let r ← renderVal st rhs
            let (raw, st1) ← emitChecked st kind l r
            let dest' := (fieldOf lhs).orElse (fun _ => st.pendingDest)
            let st' := { st1 with pendingDest := dest' }
            let lines := raw.map (indent level)
            let region ← emitRegion host p view level defaultSlot tail st'
            return { lines := lines ++ region.lines, st := region.st, terminal := true }
        | none => throw "extract/unsupported: wasm v0 checked operation"
    | .ite cmp lhs rhs thn els =>
        let l ← renderVal st lhs
        let r ← renderVal st rhs
        let head := indent level ("(if (" ++ cmpInstr cmp ++ " " ++ l ++ " " ++ r ++ ")")
        let thenRegion ← emitRegion host p view (level + 4) defaultSlot thn.toList
          { st with last := none, pendingDest := none }
        unless thenRegion.terminal do
          throw "extract/unsupported: wasm v0 ite branch must end in a terminal"
        let elseRegion ← emitRegion host p view (level + 4) defaultSlot els.toList
          { st with fresh := thenRegion.st.fresh, last := none, pendingDest := none }
        unless elseRegion.terminal do
          throw "extract/unsupported: wasm v0 ite branch must end in a terminal"
        let terminalIte := tail.isEmpty || tail.all isExitOp
        let iteHead :=
          if terminalIte then
            let ty := if view then "i64" else "i32"
            indent level ("(if (result " ++ ty ++ ") (" ++ cmpInstr cmp ++ " " ++ l ++ " " ++ r ++ ")")
          else head
        let iteLines :=
          #[iteHead, indent (level + 2) "(then"] ++ thenRegion.lines ++
          #[indent (level + 2) ")", indent (level + 2) "(else"] ++ elseRegion.lines ++
          #[indent (level + 2) "))"]
        if terminalIte then
          return { lines := iteLines, st := elseRegion.st, terminal := true }
        let region ← emitRegion host p view level defaultSlot tail
          { st with fresh := elseRegion.st.fresh, last := none, pendingDest := none }
        return { lines := iteLines ++ region.lines, st := region.st, terminal := true }
    | .storeField name value =>
        if view then throw "extract/unsupported: wasm v0 view cannot write state"
        let v ← renderVal st value
        let lines :=
          #[indent level ("(local.set " ++ localOfSlot name ++ " " ++ v ++ ")")] ++
          dumpSlots p level ++
          hostWrite host p level
        let region ← emitRegion host p view level defaultSlot tail
          { st with last := some (localOfSlot name), pendingDest := some name }
        return { lines := lines ++ region.lines, st := region.st, terminal := true }
    | .okState value | .returnState value =>
        if view then throw "extract/unsupported: wasm v0 view cannot write state"
        let dest := st.pendingDest <|> fieldOf value |>.getD defaultSlot
        let v ← match st.last with
          | some e => .ok ("(local.get " ++ e ++ ")")
          | none => renderVal st value
        unless tail.all isExitOp do
          throw "extract/unsupported: wasm v0 instructions follow terminal operation"
        let lines :=
          #[indent level ("(local.set " ++ localOfSlot dest ++ " " ++ v ++ ")")] ++
          dumpSlots p level ++
          hostWrite host p level ++
          #[indent level "(i32.const 0)"]
        return { lines, st, terminal := true }
    | .errorOverflow =>
        if view then throw "extract/unsupported: wasm v0 view cannot fail"
        unless tail.all isExitOp do
          throw "extract/unsupported: wasm v0 instructions follow terminal operation"
        return { lines := #[indent level "(i32.const 1)"], st, terminal := true }
    | .returnU64 value =>
        unless view do
          throw "extract/unsupported: wasm v0 mutating region cannot return a value"
        let (values, skipped) := collectReturnU64s value tail
        unless skipped.all isExitOp do
          throw "extract/unsupported: wasm v0 instructions follow terminal operation"
        unless values.size == 1 do
          throw "extract/unsupported: wasm v0 view result count is out of range"
        let v ← renderVal st values[0]!
        return { lines := #[indent level v], st, terminal := true }
    | _ => throw "extract/unsupported: wasm v0 op"

private def defaultSlotOf (p : Program ValExt OpExt) : String :=
  (p.slots[0]?).map (·.name) |>.getD "slot0"

private def paramDecl (count : Nat) : String :=
  String.intercalate " " ((List.range count).map (fun i =>
    "(param " ++ localOfArg i ++ " i64)"))

private def slotLocals (p : Program ValExt OpExt) : Array String :=
  p.slots.map fun slot => "(local " ++ localOfSlot slot.name ++ " i64)"

private def tempLocals (n : Nat) : Array String :=
  (Array.range n).map fun i => "(local " ++ localOfTemp i ++ " i64)"

private def loadSlots (host : Contract) (p : Program ValExt OpExt) (level : Nat)
    (view : Bool) : Array String :=
  let blob := blobLen p
  let header := #[
    indent level ("(local.set $st (call $" ++ host.homeLeField ++
      " (i32.const " ++ toString host.sfieldData ++
      ") (i32.const 0) (i32.const " ++ toString blob ++ ")))")
  ]
  let err :=
    if view then #[]
    else #[
      indent level "(if (i32.lt_s (local.get $st) (i32.const 0))",
      indent (level + 2) "(then (return (local.get $st))))"
    ]
  let loads := p.slots.map fun slot =>
    indent (level + 4) ("(local.set " ++ localOfSlot slot.name ++
      " (i64.load (i32.const " ++ toString (slotOffset p slot.name) ++ ")))")
  let body :=
    if p.slots.isEmpty then #[]
    else
      #[indent level "(if (i32.gt_s (local.get $st) (i32.const 0))",
        indent (level + 2) "(then"] ++ loads ++
      #[indent (level + 2) "))"]
  header ++ err ++ body

private partial def countTemps (ops : Array (Op ValExt OpExt)) : Nat :=
  let rec walk : List (Op ValExt OpExt) → Nat
    | [] => 0
    | .checkedAddU64 .. :: rest | .checkedSubU64 .. :: rest | .checkedMulU64 .. :: rest
    | .checkedDivU64 .. :: rest | .checkedModU64 .. :: rest => 1 + walk rest
    | .ite _ _ _ thn els :: rest => walk thn.toList + walk els.toList + walk rest
    | _ :: rest => walk rest
  walk ops.toList

private def renderFn (host : Contract) (p : Program ValExt OpExt)
    (method : Method ValExt OpExt) : Except String (Array String) := do
  let view := method.tupleArity.isSome
  let st : EState := { paramCount := method.paramCount }
  let region ← emitRegion host p view 4 (defaultSlotOf p) method.ops.toList st
  unless region.terminal do
    throw s!"extract/unsupported: {method.ixName} does not end in a terminal"
  let resultTy := if view then "i64" else "i32"
  let params := paramDecl method.paramCount
  let sig :=
    if params.isEmpty then
      "  (func (export \"" ++ method.ixName ++ "\") (result " ++ resultTy ++ ")"
    else
      "  (func (export \"" ++ method.ixName ++ "\") " ++ params ++
        " (result " ++ resultTy ++ ")"
  let mut lines : Array String := #[]
  if method.echoDropped then
    lines := lines.push s!"  ;; v0 ABI: {method.ixName} returns i32 status; public result elided"
  lines := lines.push sig
  lines := lines.push "    (local $st i32)"
  for loc in slotLocals p do
    lines := lines.push s!"    {loc}"
  for loc in tempLocals (Nat.max (countTemps method.ops) region.st.fresh) do
    lines := lines.push s!"    {loc}"
  lines := lines ++ loadSlots host p 4 view
  lines := lines ++ region.lines
  lines := lines.push "  )"
  return lines

/-- Render one program as WAT. Digest line pins the canonical IR identity. -/
def emit (host : Contract)
    (extValCanon : ValExt → String) (extOpCanon : OpExt (Val ValExt) → String)
    (p : Program ValExt OpExt) : Except String String := do
  let mut lines : Array String := #[]
  lines := lines.push s!";; {host.headerTag}"
  lines := lines.push s!";; digest={IR.digestHex host.digestDomain extValCanon extOpCanon p}"
  for note in host.headerNotes do
    lines := lines.push note
  lines := lines.push "(module"
  lines := lines.push
    ("  (import \"" ++ host.importModule ++ "\" \"" ++ host.homeLeField ++
      "\" (func $" ++ host.homeLeField ++ " (param i32 i32 i32) (result i32)))")
  lines := lines.push
    ("  (import \"" ++ host.importModule ++ "\" \"" ++ host.setData ++
      "\" (func $" ++ host.setData ++ " (param i32 i32) (result i32)))")
  lines := lines.push "  (memory (export \"memory\") 1)"
  lines := lines.push ""
  lines := lines ++ (← renderFn host p p.initializer)
  lines := lines.push ""
  for method in p.entries do
    lines := lines ++ (← renderFn host p method)
    lines := lines.push ""
  lines := lines.push ")"
  return String.intercalate "\n" lines.toList ++ "\n"

end ProofForge.Wasm.Emit
