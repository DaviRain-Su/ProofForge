import ProofForge.Wasm.IR
import ProofForge.Wasm.Near.Ops
import ProofForge.Wasm.Near.IR
import ProofForge.Wasm.Near.Host

/-!
# NEAR target emitter

Core IR → WAT with the NEAR `env` host table (near-wasm-raw-u64-v1).

Family `Wasm.Emit` injects XRPL's Data-blob `host_lib` contract; NEAR storage
and ABI do not fit that shape, so this file owns the env import table, KV
layout, and raw-u64 entry ABI. Control-flow lowering (checked i64, `if`)
mirrors the family emitter. Do not reuse XRPL's `host_lib` /
`home_le_field` / `set_data`.
-/

namespace ProofForge.Wasm.Near.Emit

open ProofForge.Wasm.IR (Program Method Val Op Cmp)
open ProofForge.Wasm.Near.Host
open ProofForge.Wasm.Near.Ops (ValKind OpExt)

private def indent (n : Nat) (s : String) : String :=
  String.ofList (List.replicate n ' ') ++ s

private def cmpInstr : Cmp → String
  | .eq => "i64.eq" | .ne => "i64.ne" | .lt => "i64.lt_u"
  | .le => "i64.le_u" | .gt => "i64.gt_u" | .ge => "i64.ge_u"

private structure EState where
  paramCount : Nat
  fresh : Nat := 0
  last : Option String := none
  pendingDest : Option String := none
  deriving Inhabited

private def fieldOf : Val ValKind → Option String
  | .field (.arg _) name => some name
  | _ => none

private def localOfArg (i : Nat) : String := "$pf_p" ++ toString i

private def localOfSlot (name : String) : String := "$" ++ name

private def localOfTemp (i : Nat) : String := "$pf_r" ++ toString i

/-- Packed ASCII keys start at this linear-memory offset. -/
private def keyBase : Nat := 1024

/-- Historical proof_forge canonicalRegisters: input=0, storage=1, evicted=2. -/
private def inputReg : Nat := 0
private def storageReg : Nat := 1
private def evictedReg : Nat := 2

private def panicOverflowOff : Nat := 2048
private def panicDivOff : Nat := 2057
private def panicInputOff : Nat := 2072
private def panicAccountIdOff : Nat := 2080

/-- Dedicated zero-padded buffers prevent a shorter second account id from
observing bytes left by another register read. -/
private def predecessorAccountOff : Nat := 64
private def currentAccountOff : Nat := 128

private def predecessorWordLocal : Nat → String
  | 0 => "$pf_pred"
  | i => "$pf_pred" ++ toString i

private def currentAccountWordLocal : Nat → String
  | 0 => "$pf_self"
  | i => "$pf_self" ++ toString i

private def keyLayout (p : Program ValKind OpExt) : Array (String × Nat × Nat) :=
  Id.run do
    let mut off := keyBase
    let mut acc : Array (String × Nat × Nat) := #[]
    for slot in p.slots do
      acc := acc.push (slot.name, off, slot.name.length)
      off := off + slot.name.length
    return acc

private def keyOf (p : Program ValKind OpExt) (name : String) : Nat × Nat :=
  match (keyLayout p).find? (fun t => t.1 == name) with
  | some (_, off, len) => (off, len)
  | none => (keyBase, 0)

private def logDataBase : Nat := 4096
private def maxLogDataBytes : Nat := 4096

private partial def logsOfOps (ops : Array (Op ValKind OpExt)) : Array String :=
  ops.foldl (init := #[]) fun messages op =>
    messages ++ match op with
      | .ext (.logUtf8 message) => #[message]
      | .ite _ _ _ thn els => logsOfOps thn ++ logsOfOps els
      | .forBody _ body => logsOfOps body
      | _ => #[]

private def logMessages (p : Program ValKind OpExt) : Array String :=
  let all := logsOfOps p.initializer.ops ++ p.entries.flatMap (logsOfOps ·.ops)
  all.foldl (init := #[]) fun unique message =>
    if unique.contains message then unique else unique.push message

private def logLayout (p : Program ValKind OpExt) : Array (String × Nat × Nat) :=
  (logMessages p).foldl (init := #[]) fun layout message =>
    let next := match layout.back? with
      | some (_, off, len) => off + len
      | none => logDataBase
    layout.push (message, next, message.toUTF8.size)

private def logOf (p : Program ValKind OpExt) (message : String) : Except String (Nat × Nat) :=
  match (logLayout p).find? (fun item => item.1 == message) with
  | some (_, off, len) => pure (off, len)
  | none => throw "extract/unsupported: near log literal is missing from static layout"

private def hexDigit (value : Nat) : Char :=
  if value < 10 then Char.ofNat ('0'.toNat + value)
  else Char.ofNat ('a'.toNat + value - 10)

private def watBytes (message : String) : String :=
  message.toUTF8.data.foldl (init := "") fun encoded byte =>
    encoded ++ "\\" ++ String.singleton (hexDigit (byte.toNat / 16)) ++
      String.singleton (hexDigit (byte.toNat % 16))

private def logDataSection (p : Program ValKind OpExt) : Except String (Array String) := do
  if (keyLayout p).any fun (_, off, len) => logDataBase < off + len then
    throw "extract/unsupported: near static storage keys overlap log data"
  let layout := logLayout p
  let total := match layout.back? with
    | some (_, off, len) => off + len - logDataBase
    | none => 0
  if maxLogDataBytes < total then
    throw s!"extract/unsupported: near static log data {total} exceeds {maxLogDataBytes} bytes"
  return layout.map fun (message, off, _) =>
    "  (data (i32.const " ++ toString off ++ ") \"" ++ watBytes message ++ "\")"

private partial def renderVal (st : EState) (v : Val ValKind) : Except String String :=
  match v with
  | .lit n => .ok ("(i64.const " ++ toString n.toNat ++ ")")
  | .arg i =>
      if i < st.paramCount then .ok ("(local.get " ++ localOfArg i ++ ")")
      else .error "extract/unsupported: near v0 rejects bare state argument"
  | .field (.arg i) name =>
      if i < st.paramCount then
        .error "extract/unsupported: near v0 rejects aggregate parameter projections"
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
  | .ext .blockIndex #[] => .ok "(call $pf_block_index)"
  | .ext .blockTimestamp #[] =>
      .ok "(i64.div_u (call $pf_block_timestamp) (i64.const 1000000000))"
  | .ext .predecessor #[] => .ok "(local.get $pf_pred)"
  | .ext .predecessorLen #[] => .ok "(local.get $pf_pred_len)"
  | .ext .predecessorW1 #[] => .ok "(local.get $pf_pred1)"
  | .ext .predecessorW2 #[] => .ok "(local.get $pf_pred2)"
  | .ext .predecessorW3 #[] => .ok "(local.get $pf_pred3)"
  | .ext .predecessorW4 #[] => .ok "(local.get $pf_pred4)"
  | .ext .predecessorW5 #[] => .ok "(local.get $pf_pred5)"
  | .ext .predecessorW6 #[] => .ok "(local.get $pf_pred6)"
  | .ext .predecessorW7 #[] => .ok "(local.get $pf_pred7)"
  | .ext .attachedDeposit #[] => .ok "(local.get $pf_dep)"
  | .ext .attachedDepositW0 #[] => .ok "(local.get $pf_dep)"
  | .ext .attachedDepositW1 #[] => .ok "(local.get $pf_dep_hi)"
  | .ext .accountBalance #[] => .ok "(local.get $pf_bal)"
  | .ext .accountBalanceW0 #[] => .ok "(local.get $pf_bal)"
  | .ext .accountBalanceW1 #[] => .ok "(local.get $pf_bal_hi)"
  | .ext .currentAccountId #[] => .ok "(local.get $pf_self)"
  | .ext .currentAccountIdLen #[] => .ok "(local.get $pf_self_len)"
  | .ext .currentAccountIdW1 #[] => .ok "(local.get $pf_self1)"
  | .ext .currentAccountIdW2 #[] => .ok "(local.get $pf_self2)"
  | .ext .currentAccountIdW3 #[] => .ok "(local.get $pf_self3)"
  | .ext .currentAccountIdW4 #[] => .ok "(local.get $pf_self4)"
  | .ext .currentAccountIdW5 #[] => .ok "(local.get $pf_self5)"
  | .ext .currentAccountIdW6 #[] => .ok "(local.get $pf_self6)"
  | .ext .currentAccountIdW7 #[] => .ok "(local.get $pf_self7)"
  | _ => .error "extract/unsupported: near v0 value"

private def isExitOp : Op ValKind OpExt → Bool
  | .okState _ | .errorOverflow | .errorNamed _ | .returnU64 _ | .returnState _ => true
  | _ => false

private def collectReturnU64s (first : Val ValKind)
    (rest : List (Op ValKind OpExt)) :
    Array (Val ValKind) × List (Op ValKind OpExt) :=
  let rec go (acc : Array (Val ValKind))
      (rest : List (Op ValKind OpExt)) :=
    match rest with
    | .returnU64 next :: more => go (acc.push next) more
    | _ => (acc, rest)
  go #[first] rest

private def panicOverflow (level : Nat) : String :=
  indent level ("(call $pf_panic_utf8 (i64.const 8) (i64.const " ++
    toString panicOverflowOff ++ "))")

private def panicDiv (level : Nat) : String :=
  indent level ("(call $pf_panic_utf8 (i64.const 14) (i64.const " ++
    toString panicDivOff ++ "))")

private def storeSlot (p : Program ValKind OpExt)
    (name expr : String) (level : Nat) : Array String :=
  let (off, len) := keyOf p name
  #[
    indent level ("(i64.store (i32.const 8) " ++ expr ++ ")"),
    indent level ("(drop (call $pf_storage_write (i64.const " ++ toString len ++
      ") (i64.const " ++ toString off ++ ") (i64.const 8) (i64.const 8) (i64.const " ++
      toString evictedReg ++ ")))")
  ]

private def returnU64Instr (expr : String) (level : Nat) : Array String :=
  #[
    indent level ("(i64.store (i32.const 0) " ++ expr ++ ")"),
    indent level "(call $pf_value_return (i64.const 8) (i64.const 0))"
  ]

private def emitChecked (st : EState) (kind : String) (lhs rhs : String) (level : Nat) :
    Except String (Array String × EState) := do
  let temp := localOfTemp st.fresh
  let st' := { st with fresh := st.fresh + 1, last := some temp }
  match kind with
  | "add" =>
      return (#[
        indent level ("(local.set " ++ temp ++ " (i64.add " ++ lhs ++ " " ++ rhs ++ "))"),
        indent level ("(if (i64.lt_u (local.get " ++ temp ++ ") " ++ lhs ++ ")"),
        indent (level + 2) "(then",
        panicOverflow (level + 4),
        indent (level + 2) "))"
      ], st')
  | "sub" =>
      return (#[
        indent level ("(if (i64.lt_u " ++ lhs ++ " " ++ rhs ++ ")"),
        indent (level + 2) "(then",
        panicOverflow (level + 4),
        indent (level + 2) "))",
        indent level ("(local.set " ++ temp ++ " (i64.sub " ++ lhs ++ " " ++ rhs ++ "))")
      ], st')
  | "mul" =>
      return (#[
        indent level ("(if (i64.eqz " ++ lhs ++ ")"),
        indent (level + 2) ("(then (local.set " ++ temp ++ " (i64.const 0)))"),
        indent (level + 2) "(else",
        indent (level + 4) ("(if (i64.gt_u " ++ rhs ++ " (i64.div_u (i64.const -1) " ++ lhs ++ "))"),
        indent (level + 6) "(then",
        panicOverflow (level + 8),
        indent (level + 6) ")",
        indent (level + 6) ("(else (local.set " ++ temp ++ " (i64.mul " ++ lhs ++ " " ++ rhs ++ "))))"),
        indent (level + 2) "))"
      ], st')
  | "div" =>
      return (#[
        indent level ("(if (i64.eqz " ++ rhs ++ ")"),
        indent (level + 2) "(then",
        panicDiv (level + 4),
        indent (level + 2) "))",
        indent level ("(local.set " ++ temp ++ " (i64.div_u " ++ lhs ++ " " ++ rhs ++ "))")
      ], st')
  | "rem" =>
      return (#[
        indent level ("(if (i64.eqz " ++ rhs ++ ")"),
        indent (level + 2) "(then",
        panicDiv (level + 4),
        indent (level + 2) "))",
        indent level ("(local.set " ++ temp ++ " (i64.rem_u " ++ lhs ++ " " ++ rhs ++ "))")
      ], st')
  | _ => throw "extract/unsupported: near v0 checked operation"

private def checkedKind : Op ValKind OpExt → Option String
  | .checkedAddU64 .. => some "add"
  | .checkedSubU64 .. => some "sub"
  | .checkedMulU64 .. => some "mul"
  | .checkedDivU64 .. => some "div"
  | .checkedModU64 .. => some "rem"
  | _ => none

private structure Region where
  lines : Array String := #[]
  st : EState
  terminal : Bool := false

private partial def emitRegion (p : Program ValKind OpExt)
    (view : Bool) (echo : Bool) (level : Nat) (defaultSlot : String)
    (ops : List (Op ValKind OpExt)) (st : EState) : Except String Region := do
  match ops with
  | [] =>
      if view then
        throw "extract/unsupported: near v0 view region must end in a return"
      else
        throw "extract/unsupported: near v0 mutating region must end in a state or error exit"
  | op :: tail =>
    match op with
    | .checkedAddU64 lhs rhs | .checkedSubU64 lhs rhs | .checkedMulU64 lhs rhs
    | .checkedDivU64 lhs rhs | .checkedModU64 lhs rhs =>
        if view then throw "extract/unsupported: near v0 view cannot fail"
        match checkedKind op with
        | some kind =>
            let l ← renderVal st lhs
            let r ← renderVal st rhs
            let (lines, st1) ← emitChecked st kind l r level
            let dest' := (fieldOf lhs).orElse (fun _ => st.pendingDest)
            let st' := { st1 with pendingDest := dest' }
            let region ← emitRegion p view echo level defaultSlot tail st'
            return { lines := lines ++ region.lines, st := region.st, terminal := true }
        | none => throw "extract/unsupported: near v0 checked operation"
    | .ite cmp lhs rhs thn els =>
        let l ← renderVal st lhs
        let r ← renderVal st rhs
        let thenRegion ← emitRegion p view echo (level + 4) defaultSlot thn.toList
          { st with last := none, pendingDest := none }
        unless thenRegion.terminal do
          throw "extract/unsupported: near v0 ite branch must end in a terminal"
        let elseRegion ← emitRegion p view echo (level + 4) defaultSlot els.toList
          { st with fresh := thenRegion.st.fresh, last := none, pendingDest := none }
        unless elseRegion.terminal do
          throw "extract/unsupported: near v0 ite branch must end in a terminal"
        let head := indent level ("(if (" ++ cmpInstr cmp ++ " " ++ l ++ " " ++ r ++ ")")
        let iteLines :=
          #[head, indent (level + 2) "(then"] ++ thenRegion.lines ++
          #[indent (level + 2) ")", indent (level + 2) "(else"] ++ elseRegion.lines ++
          #[indent (level + 2) "))"]
        if tail.isEmpty || tail.all isExitOp then
          return { lines := iteLines, st := elseRegion.st, terminal := true }
        let region ← emitRegion p view echo level defaultSlot tail
          { st with fresh := elseRegion.st.fresh, last := none, pendingDest := none }
        return { lines := iteLines ++ region.lines, st := region.st, terminal := true }
    | .storeField name value =>
        if view then throw "extract/unsupported: near v0 view cannot write state"
        let v ← renderVal st value
        let lines :=
          #[indent level ("(local.set " ++ localOfSlot name ++ " " ++ v ++ ")")] ++
          storeSlot p name ("(local.get " ++ localOfSlot name ++ ")") level
        let region ← emitRegion p view echo level defaultSlot tail
          { st with last := some (localOfSlot name), pendingDest := some name }
        return { lines := lines ++ region.lines, st := region.st, terminal := true }
    | .okState value | .returnState value =>
        if view then throw "extract/unsupported: near v0 view cannot write state"
        let dest := st.pendingDest <|> fieldOf value |>.getD defaultSlot
        let v ← match st.last with
          | some e => .ok ("(local.get " ++ e ++ ")")
          | none => renderVal st value
        unless tail.all isExitOp do
          throw "extract/unsupported: near v0 instructions follow terminal operation"
        let mut lines :=
          #[indent level ("(local.set " ++ localOfSlot dest ++ " " ++ v ++ ")")] ++
          storeSlot p dest ("(local.get " ++ localOfSlot dest ++ ")") level
        if echo then
          lines := lines ++ returnU64Instr ("(local.get " ++ localOfSlot dest ++ ")") level
        return { lines, st, terminal := true }
    | .errorOverflow =>
        if view then throw "extract/unsupported: near v0 view cannot fail"
        unless tail.all isExitOp do
          throw "extract/unsupported: near v0 instructions follow terminal operation"
        return { lines := #[panicOverflow level], st, terminal := true }
    | .ext (.logUtf8 message) =>
        let (off, len) ← logOf p message
        let region ← emitRegion p view echo level defaultSlot tail st
        return {
          lines := #[indent level ("(call $pf_log_utf8 (i64.const " ++ toString len ++
            ") (i64.const " ++ toString off ++ "))")] ++ region.lines
          st := region.st
          terminal := region.terminal }
    | .returnU64 value =>
        unless view do
          throw "extract/unsupported: near v0 mutating region cannot return a value"
        let (values, skipped) := collectReturnU64s value tail
        unless skipped.all isExitOp do
          throw "extract/unsupported: near v0 instructions follow terminal operation"
        unless values.size == 1 do
          throw "extract/unsupported: near v0 view wants exactly one UInt64"
        let v ← renderVal st values[0]!
        return { lines := returnU64Instr v level, st, terminal := true }
    | _ => throw "extract/unsupported: near v0 op"

private def defaultSlotOf (p : Program ValKind OpExt) : String :=
  (p.slots[0]?).map (·.name) |>.getD "slot0"

private partial def countTemps (ops : Array (Op ValKind OpExt)) : Nat :=
  let rec walk : List (Op ValKind OpExt) → Nat
    | [] => 0
    | .checkedAddU64 .. :: rest | .checkedSubU64 .. :: rest | .checkedMulU64 .. :: rest
    | .checkedDivU64 .. :: rest | .checkedModU64 .. :: rest => 1 + walk rest
    | .ite _ _ _ thn els :: rest => walk thn.toList + walk els.toList + walk rest
    | _ :: rest => walk rest
  walk ops.toList

private partial def usesKind (kind : ValKind) : Op ValKind OpExt → Bool
  | .checkedAddU64 lhs rhs | .checkedSubU64 lhs rhs | .checkedMulU64 lhs rhs
  | .checkedDivU64 lhs rhs | .checkedModU64 lhs rhs =>
      valHas lhs || valHas rhs
  | .ite _ lhs rhs thn els =>
      valHas lhs || valHas rhs || thn.any (usesKind kind) || els.any (usesKind kind)
  | .storeField _ value | .okState value | .returnState value | .returnU64 value =>
      valHas value
  | _ => false
where
  valHas : Val ValKind → Bool
    | .ext k _ => k == kind
    | .select _ l r t f => valHas l || valHas r || valHas t || valHas f
    | .addU64 l r | .subU64 l r | .mulU64 l r | .divU64 l r | .modU64 l r =>
        valHas l || valHas r
    | .field base _ | .bitNot base => valHas base
    | .bitAnd l r | .bitOr l r | .bitXor l r | .shiftL l r | .shiftR l r =>
        valHas l || valHas r
    | _ => false

private def methodUses (kind : ValKind) (method : Method ValKind OpExt) : Bool :=
  method.ops.any (usesKind kind)

private def predecessorKinds : Array ValKind := #[
  .predecessor, .predecessorLen, .predecessorW1, .predecessorW2,
  .predecessorW3, .predecessorW4, .predecessorW5, .predecessorW6, .predecessorW7
]

private def currentAccountKinds : Array ValKind := #[
  .currentAccountId, .currentAccountIdLen, .currentAccountIdW1, .currentAccountIdW2,
  .currentAccountIdW3, .currentAccountIdW4, .currentAccountIdW5,
  .currentAccountIdW6, .currentAccountIdW7
]

private def attachedDepositKinds : Array ValKind := #[
  .attachedDeposit, .attachedDepositW0, .attachedDepositW1
]

private def accountBalanceKinds : Array ValKind := #[
  .accountBalance, .accountBalanceW0, .accountBalanceW1
]

private def methodUsesAny (kinds : Array ValKind) (method : Method ValKind OpExt) : Bool :=
  kinds.any (methodUses · method)

private def clearAccountBuffer (off level : Nat) : Array String :=
  (List.range 8).toArray.map fun i =>
    indent level ("(i64.store (i32.const " ++ toString (off + i * 8) ++
      ") (i64.const 0))")

private def loadAccountId (hostCall lenLocal : String) (register off level : Nat)
    (wordLocal : Nat → String) : Array String :=
  #[
    indent level ("(call " ++ hostCall ++ " (i64.const " ++ toString register ++ "))"),
    indent level ("(local.set " ++ lenLocal ++ " (call $pf_register_len (i64.const " ++
      toString register ++ ")) )"),
    indent level ("(if (i64.gt_u (local.get " ++ lenLocal ++ ") (i64.const 64))"),
    indent (level + 2) "(then",
    indent (level + 4) ("(call $pf_panic_utf8 (i64.const 10) (i64.const " ++
      toString panicAccountIdOff ++ "))"),
    indent (level + 2) "))"
  ] ++ clearAccountBuffer off level ++ #[
    indent level ("(call $pf_read_register (i64.const " ++ toString register ++
      ") (i64.const " ++ toString off ++ "))")
  ] ++ (List.range 8).toArray.map fun i =>
    indent level ("(local.set " ++ wordLocal i ++ " (i64.load (i32.const " ++
      toString (off + i * 8) ++ ")))")

private def loadHostPrelude (method : Method ValKind OpExt) (view : Bool) (level : Nat) :
    Except String (Array String) := do
  if view && methodUsesAny predecessorKinds method then
    throw s!"extract/unsupported: {method.ixName} view cannot read predecessor"
  if view && methodUsesAny attachedDepositKinds method then
    throw s!"extract/unsupported: {method.ixName} view cannot read attachedDeposit"
  let mut lines : Array String := #[]
  if methodUsesAny predecessorKinds method then
    lines := lines ++ loadAccountId "$pf_predecessor_account_id" "$pf_pred_len"
      0 predecessorAccountOff level predecessorWordLocal
  if methodUsesAny attachedDepositKinds method then
    lines := lines.push (indent level "(call $pf_attached_deposit (i64.const 24))")
    if methodUses .attachedDeposit method then
      lines := lines ++ #[
        indent level "(if (i64.ne (i64.load (i32.const 32)) (i64.const 0))",
        indent (level + 2) "(then",
        indent (level + 4) ("(call $pf_panic_utf8 (i64.const 8) (i64.const " ++
          toString panicOverflowOff ++ "))"),
        indent (level + 2) "))"
      ]
    lines := lines ++ #[
      indent level "(local.set $pf_dep (i64.load (i32.const 24)))",
      indent level "(local.set $pf_dep_hi (i64.load (i32.const 32)))"
    ]
  if methodUsesAny accountBalanceKinds method then
    lines := lines.push (indent level "(call $pf_account_balance (i64.const 40))")
    if methodUses .accountBalance method then
      lines := lines ++ #[
        indent level "(if (i64.ne (i64.load (i32.const 48)) (i64.const 0))",
        indent (level + 2) "(then",
        indent (level + 4) ("(call $pf_panic_utf8 (i64.const 8) (i64.const " ++
          toString panicOverflowOff ++ "))"),
        indent (level + 2) "))"
      ]
    lines := lines ++ #[
      indent level "(local.set $pf_bal (i64.load (i32.const 40)))",
      indent level "(local.set $pf_bal_hi (i64.load (i32.const 48)))"
    ]
  if methodUsesAny currentAccountKinds method then
    lines := lines ++ loadAccountId "$pf_current_account_id" "$pf_self_len"
      3 currentAccountOff level currentAccountWordLocal
  return lines

private def loadArg (count : Nat) (level : Nat) : Array String :=
  if count == 0 then
    #[
      indent level ("(call $pf_input (i64.const " ++ toString inputReg ++ "))"),
      indent level ("(if (i64.ne (call $pf_register_len (i64.const " ++
        toString inputReg ++ ")) (i64.const 0))"),
      indent (level + 2) "(then",
      indent (level + 4) ("(call $pf_panic_utf8 (i64.const 5) (i64.const " ++
        toString panicInputOff ++ "))"),
      indent (level + 2) "))"
    ]
  else if count == 1 then
    #[
      indent level ("(call $pf_input (i64.const " ++ toString inputReg ++ "))"),
      indent level ("(if (i64.ne (call $pf_register_len (i64.const " ++
        toString inputReg ++ ")) (i64.const 8))"),
      indent (level + 2) "(then",
      indent (level + 4) ("(call $pf_panic_utf8 (i64.const 5) (i64.const " ++
        toString panicInputOff ++ "))"),
      indent (level + 2) "))",
      indent level ("(call $pf_read_register (i64.const " ++ toString inputReg ++
        ") (i64.const 0))"),
      indent level ("(local.set " ++ localOfArg 0 ++ " (i64.load (i32.const 0)))")
    ]
  else
    #[]

private def loadSlots (p : Program ValKind OpExt) (level : Nat) : Array String :=
  p.slots.foldl (init := #[]) fun acc slot =>
    let (off, len) := keyOf p slot.name
    acc ++ #[
      indent level ("(if (i64.eq (call $pf_storage_read (i64.const " ++ toString len ++
        ") (i64.const " ++ toString off ++ ") (i64.const " ++ toString storageReg ++
        ")) (i64.const 1))"),
      indent (level + 2) "(then",
      indent (level + 4) ("(call $pf_read_register (i64.const " ++ toString storageReg ++
        ") (i64.const 8))"),
      indent (level + 4) ("(local.set " ++ localOfSlot slot.name ++
        " (i64.load (i32.const 8)))"),
      indent (level + 2) ")",
      indent (level + 2) ("(else (local.set " ++ localOfSlot slot.name ++ " (i64.const 0))))")
    ]

private def renderFn (p : Program ValKind OpExt)
    (method : Method ValKind OpExt) : Except String (Array String) := do
  unless method.paramCount ≤ 1 do
    throw s!"extract/unsupported: {method.ixName} wants at most one UInt64 parameter for near v0"
  let view := method.tupleArity.isSome
  let echo := method.echoDropped
  let st : EState := { paramCount := method.paramCount }
  let region ← emitRegion p view echo 4 (defaultSlotOf p) method.ops.toList st
  unless region.terminal do
    throw s!"extract/unsupported: {method.ixName} does not end in a terminal"
  let mut lines : Array String := #[]
  if method.echoDropped then
    lines := lines.push s!"  ;; v0 ABI: {method.ixName} value_returns 8-byte LE after store"
  lines := lines.push ("  (func (export \"" ++ method.ixName ++ "\")")
  if method.paramCount == 1 then
    lines := lines.push ("    (local " ++ localOfArg 0 ++ " i64)")
  if methodUsesAny predecessorKinds method then
    lines := lines.push "    (local $pf_pred_len i64)"
    for i in List.range 8 do
      lines := lines.push ("    (local " ++ predecessorWordLocal i ++ " i64)")
  if methodUsesAny attachedDepositKinds method then
    lines := lines.push "    (local $pf_dep i64)"
    lines := lines.push "    (local $pf_dep_hi i64)"
  if methodUsesAny accountBalanceKinds method then
    lines := lines.push "    (local $pf_bal i64)"
    lines := lines.push "    (local $pf_bal_hi i64)"
  if methodUsesAny currentAccountKinds method then
    lines := lines.push "    (local $pf_self_len i64)"
    for i in List.range 8 do
      lines := lines.push ("    (local " ++ currentAccountWordLocal i ++ " i64)")
  for slot in p.slots do
    lines := lines.push ("    (local " ++ localOfSlot slot.name ++ " i64)")
  for i in List.range (Nat.max (countTemps method.ops) region.st.fresh) do
    lines := lines.push ("    (local " ++ localOfTemp i ++ " i64)")
  lines := lines ++ loadArg method.paramCount 4
  lines := lines ++ (← loadHostPrelude method view 4)
  lines := lines ++ loadSlots p 4
  lines := lines ++ region.lines
  lines := lines.push "  )"
  return lines

private def programUses (kind : ValKind) (p : IR.Program) : Bool :=
  methodUses kind p.initializer || p.entries.any (methodUses kind)

private def dataSection (p : Program ValKind OpExt) : Array String :=
  let keys := (keyLayout p).map fun (name, off, _) =>
    "  (data (i32.const " ++ toString off ++ ") \"" ++ name ++ "\")"
  let base := #[
    "  (data (i32.const " ++ toString panicOverflowOff ++ ") \"overflow\")",
    "  (data (i32.const " ++ toString panicDivOff ++ ") \"divide-by-zero\")",
    "  (data (i32.const " ++ toString panicInputOff ++ ") \"input\")"
  ]
  let account :=
    if predecessorKinds.any (programUses · p) || currentAccountKinds.any (programUses · p) then
      #["  (data (i32.const " ++ toString panicAccountIdOff ++ ") \"account-id\")"]
    else #[]
  keys ++ base ++ account

def emit (p : IR.Program) : Except String String := do
  let logData ← logDataSection p
  let mut lines : Array String := #[]
  lines := lines.push s!";; {Host.headerTag}"
  lines := lines.push s!";; digest={IR.digestHex p}"
  for note in Host.headerNotes do
    lines := lines.push note
  lines := lines.push "(module"
  lines := lines.push "  (import \"env\" \"input\" (func $pf_input (param i64)))"
  lines := lines.push
    "  (import \"env\" \"register_len\" (func $pf_register_len (param i64) (result i64)))"
  lines := lines.push
    "  (import \"env\" \"read_register\" (func $pf_read_register (param i64 i64)))"
  lines := lines.push
    "  (import \"env\" \"storage_read\" (func $pf_storage_read (param i64 i64 i64) (result i64)))"
  lines := lines.push
    "  (import \"env\" \"storage_write\" (func $pf_storage_write (param i64 i64 i64 i64 i64) (result i64)))"
  lines := lines.push
    "  (import \"env\" \"value_return\" (func $pf_value_return (param i64 i64)))"
  lines := lines.push
    "  (import \"env\" \"panic_utf8\" (func $pf_panic_utf8 (param i64 i64)))"
  if !(logMessages p).isEmpty then
    lines := lines.push
      "  (import \"env\" \"log_utf8\" (func $pf_log_utf8 (param i64 i64)))"
  if programUses .blockIndex p then
    lines := lines.push
      "  (import \"env\" \"block_index\" (func $pf_block_index (result i64)))"
  if programUses .blockTimestamp p then
    lines := lines.push
      "  (import \"env\" \"block_timestamp\" (func $pf_block_timestamp (result i64)))"
  if predecessorKinds.any (programUses · p) then
    lines := lines.push
      "  (import \"env\" \"predecessor_account_id\" (func $pf_predecessor_account_id (param i64)))"
  if attachedDepositKinds.any (programUses · p) then
    lines := lines.push
      "  (import \"env\" \"attached_deposit\" (func $pf_attached_deposit (param i64)))"
  if accountBalanceKinds.any (programUses · p) then
    lines := lines.push
      "  (import \"env\" \"account_balance\" (func $pf_account_balance (param i64)))"
  if currentAccountKinds.any (programUses · p) then
    lines := lines.push
      "  (import \"env\" \"current_account_id\" (func $pf_current_account_id (param i64)))"
  lines := lines.push "  (memory (export \"memory\") 1)"
  lines := lines ++ dataSection p
  lines := lines ++ logData
  lines := lines.push ""
  lines := lines ++ (← renderFn p p.initializer)
  lines := lines.push ""
  for method in p.entries do
    lines := lines ++ (← renderFn p method)
    lines := lines.push ""
  lines := lines.push ")"
  return String.intercalate "\n" lines.toList ++ "\n"

end ProofForge.Wasm.Near.Emit
