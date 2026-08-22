import SolanaLean.Ops
import SolanaLean.Evm.IR
import SolanaLean.Evm.Keccak

namespace SolanaLean.Evm.Emit

open SolanaLean
open SolanaLean.Evm

private def u64MaxYul : String := "0xffffffffffffffff"

private def returnStateCount (ops : Array Ops.Op) : Nat :=
  ops.foldl (init := 0) fun acc op =>
    match op with
    | .returnState _ => acc + 1
    | _ => acc

private def destHint (p : IR.Program) (ops : Array Ops.Op) : String :=
  match ops.findSome? (fun
    | .checkedAddU64 l _ =>
        match l with | .field _ n => some n | _ => none
    | .checkedSubU64 l _ =>
        match l with | .field _ n => some n | _ => none
    | .checkedMulU64 l _ =>
        match l with | .field _ n => some n | _ => none
    | .checkedDivU64 l _ =>
        match l with | .field _ n => some n | _ => none
    | .checkedModU64 l _ =>
        match l with | .field _ n => some n | _ => none
    | _ => none) with
  | some n => n
  | none => (p.slots[0]?.map (·.name)).getD "slot0"

/-- 与 sBPF 发射器同一 dest：算术结果写 lhs 槽；无算术的 `field name_i` 写该槽。 -/
private def destForOk (p : IR.Program) (ops : Array Ops.Op) (v : Ops.Val) : String :=
  match v with
  | .field _ fname =>
      if Ops.hasCheckedArith ops then destHint p ops
      else if fname.contains '_' && (IR.slotIndex p fname).isSome then fname
      else destHint p ops
  | _ => destHint p ops

private def slotOf (p : IR.Program) (name : String) : Except String Nat :=
  match IR.slotIndex p name with
  | some i => .ok i
  | none => .error s!"extract/unsupported: unknown field {name}"

private def nl : String := "\n"

private def yulLit (n : UInt64) : String :=
  if n == 0 then "0"
  else s!"0x{SolanaLean.IR.u64Hex n}"

/-- Addr20 小端三叶：word i 收 `src` 的字节 0..19 中第 8i ..。`src` 是 `caller()` / `address()`。 -/
private def packAddrWord (src : String) (word : Nat) : String :=
  let rec orBytes (i : Nat) (n : Nat) (acc : String) : String :=
    match n with
    | 0 => acc
    | n' + 1 =>
      let b := "byte(" ++ toString (12 + 8 * word + i) ++ ", " ++ src ++ ")"
      let next :=
        if i == 0 then b
        else "or(" ++ acc ++ ", shl(" ++ toString (8 * i) ++ ", " ++ b ++ "))"
      orBytes (i + 1) n' next
  let count := if word == 2 then 4 else 8
  orBytes 0 count "0"

/-- 把三叶小端 Addr20 写到 memory[12..31]，高 12 字节已清零。 -/
private def packAddrMstore8 (indent w0 w1 w2 : String) : String :=
  Id.run do
    let mut out := ""
    for i in [0:8] do
      out := out ++ indent ++ "mstore8(" ++ toString (12 + i) ++ ", and(shr(" ++
        toString (8 * i) ++ ", " ++ w0 ++ "), 0xff))" ++ nl
    for i in [0:8] do
      out := out ++ indent ++ "mstore8(" ++ toString (20 + i) ++ ", and(shr(" ++
        toString (8 * i) ++ ", " ++ w1 ++ "), 0xff))" ++ nl
    for i in [0:4] do
      out := out ++ indent ++ "mstore8(" ++ toString (28 + i) ++ ", and(shr(" ++
        toString (8 * i) ++ ", " ++ w2 ++ "), 0xff))" ++ nl
    return out

private def widthMask (width : Nat) : String :=
  match width with
  | 1 => "0xff"
  | 2 => "0xffff"
  | 4 => "0xffffffff"
  | _ => u64MaxYul

private def maskExpr (width : Nat) (value : String) : String :=
  if width == 8 then value else "and(" ++ value ++ ", " ++ widthMask width ++ ")"

private def loadVal (p : IR.Program) (paramPrefix : String) (paramCount : Nat)
    (v : Ops.Val) : Except String String :=
  match v with
  | .lit n => .ok (yulLit n)
  | .arg i =>
      if i < paramCount then
        .ok s!"{paramPrefix}{i}"
      else
        .error "extract/unsupported: evm arg is implicit state"
  | .field _ name => do
      let slot ← slotOf p name
      let w := (IR.slotWidth p name).getD 8
      return maskExpr w s!"sload({slot})"
  | .clockSlot => .error "extract/unsupported: evm rejects clockSlot"
  | .signerKey0 => .error "extract/unsupported: evm rejects signerKey0"
  | .evmCaller => .ok "and(caller(), 0xffffffffffffffff)"
  | .evmBlockNumber => .ok "number()"
  | .evmTimestamp => .ok "timestamp()"
  | .evmChainId => .ok "chainid()"
  | .evmSelf => .ok "and(address(), 0xffffffffffffffff)"
  | .evmCallValue => .ok "callvalue()"
  | .evmSelfBalance => .ok "selfbalance()"
  | .evmCallerW0 => .ok (packAddrWord "caller()" 0)
  | .evmCallerW1 => .ok (packAddrWord "caller()" 1)
  | .evmCallerW2 => .ok (packAddrWord "caller()" 2)
  | .evmSelfW0 => .ok (packAddrWord "address()" 0)
  | .evmSelfW1 => .ok (packAddrWord "address()" 1)
  | .evmSelfW2 => .ok (packAddrWord "address()" 2)

private def cmpYul (c : Ops.Cmp) (l r : String) : String :=
  match c with
  | .eq => s!"eq({l}, {r})"
  | .ne => s!"iszero(eq({l}, {r}))"
  | .lt => s!"lt({l}, {r})"
  | .le => s!"iszero(gt({l}, {r}))"
  | .gt => s!"gt({l}, {r})"
  | .ge => s!"iszero(lt({l}, {r}))"

private def revert0 : String := "revert(0, 0)"

private def returnWord (indent value : String) : String :=
  indent ++ "mstore(0, " ++ value ++ ")" ++ nl ++
    indent ++ "return(0, 32)" ++ nl

private def storeSlot (indent : String) (slot : Nat) (value : String) : String :=
  indent ++ "sstore(" ++ toString slot ++ ", " ++ value ++ ")" ++ nl

private def storeNamed (p : IR.Program) (indent name value : String) : Except String String := do
  let slot ← slotOf p name
  let w := (IR.slotWidth p name).getD 8
  return storeSlot indent slot (maskExpr w value)

private def optionTagName (p : IR.Program) : String :=
  match p.slots.find? (fun s => s.name.endsWith "_tag") with
  | some s => s.name
  | none => "slot_tag"

private def optionPayName (p : IR.Program) : String :=
  match p.slots.find? (fun s => s.name.endsWith "_p0") with
  | some s => s.name
  | none => "slot_p0"

private structure Render where
  last : Option String := none
  next : Nat := 0

private def fresh (r : Render) : String × Render :=
  (s!"v{r.next}", { r with next := r.next + 1 })

private def bindChecked (indent name expr : String) : String :=
  indent ++ "let " ++ name ++ " := " ++ expr ++ nl ++
    indent ++ "if gt(" ++ name ++ ", " ++ u64MaxYul ++ ") { " ++ revert0 ++ " }" ++ nl

/-- 环境 opcode 必须先 range-check 再当值用。 -/
private def materializeVal (p : IR.Program) (indent paramPrefix : String)
    (paramCount : Nat) (v : Ops.Val) (st : Render) :
    Except String (String × String × Render) := do
  let checked? : Option String :=
    match v with
    | .evmBlockNumber => some "number()"
    | .evmTimestamp => some "timestamp()"
    | .evmChainId => some "chainid()"
    | .evmCallValue => some "callvalue()"
    | .evmSelfBalance => some "selfbalance()"
    | _ => none
  match checked? with
  | some expr =>
      let (nm, st') := fresh st
      return (bindChecked indent nm expr, nm, st')
  | none =>
      let e ← loadVal p paramPrefix paramCount v
      return ("", e, st)

private def brace (inner : String) : String :=
  "{" ++ nl ++ inner ++ "}"

private partial def emitOps (p : IR.Program) (indent paramPrefix : String)
    (paramCount : Nat) (ops : Array Ops.Op) (st : Render) :
    Except String (String × Render) := do
  let destSlot0 ← slotOf p (destHint p ops)
  let nStates := returnStateCount ops
  let mut acc := ""
  let mut st := st
  let mut returnStateIdx : Nat := 0
  for op in ops do
    match op with
    | .checkedAddU64 l r =>
        let lv ← loadVal p paramPrefix paramCount l
        let rv ← loadVal p paramPrefix paramCount r
        let (nm, st') := fresh st
        st := st'
        acc := acc ++
          indent ++ "if gt(" ++ lv ++ ", sub(" ++ u64MaxYul ++ ", " ++ rv ++ ")) { " ++
            revert0 ++ " }" ++ nl ++
          indent ++ "let " ++ nm ++ " := add(" ++ lv ++ ", " ++ rv ++ ")" ++ nl
        st := { st with last := some nm }
    | .checkedSubU64 l r =>
        let lv ← loadVal p paramPrefix paramCount l
        let rv ← loadVal p paramPrefix paramCount r
        let (nm, st') := fresh st
        st := st'
        acc := acc ++
          indent ++ "if lt(" ++ lv ++ ", " ++ rv ++ ") { " ++ revert0 ++ " }" ++ nl ++
          indent ++ "let " ++ nm ++ " := sub(" ++ lv ++ ", " ++ rv ++ ")" ++ nl
        st := { st with last := some nm }
    | .checkedMulU64 l r =>
        let lv ← loadVal p paramPrefix paramCount l
        let rv ← loadVal p paramPrefix paramCount r
        let (nm, st') := fresh st
        st := st'
        acc := acc ++
          indent ++ "let " ++ nm ++ " := mul(" ++ lv ++ ", " ++ rv ++ ")" ++ nl ++
          indent ++ "if gt(" ++ nm ++ ", " ++ u64MaxYul ++ ") { " ++ revert0 ++ " }" ++ nl
        st := { st with last := some nm }
    | .checkedDivU64 l r =>
        let lv ← loadVal p paramPrefix paramCount l
        let rv ← loadVal p paramPrefix paramCount r
        let (nm, st') := fresh st
        st := st'
        acc := acc ++
          indent ++ "if iszero(" ++ rv ++ ") { " ++ revert0 ++ " }" ++ nl ++
          indent ++ "let " ++ nm ++ " := div(" ++ lv ++ ", " ++ rv ++ ")" ++ nl
        st := { st with last := some nm }
    | .checkedModU64 l r =>
        let lv ← loadVal p paramPrefix paramCount l
        let rv ← loadVal p paramPrefix paramCount r
        let (nm, st') := fresh st
        st := st'
        acc := acc ++
          indent ++ "if iszero(" ++ rv ++ ") { " ++ revert0 ++ " }" ++ nl ++
          indent ++ "let " ++ nm ++ " := mod(" ++ lv ++ ", " ++ rv ++ ")" ++ nl
        st := { st with last := some nm }
    | .ite c l r thn els =>
        let lv ← loadVal p paramPrefix paramCount l
        let rv ← loadVal p paramPrefix paramCount r
        let (nm, st') := fresh st
        st := st'
        let (thenTxt, st1) ← emitOps p (indent ++ "  ") paramPrefix paramCount thn st
        let (elseTxt, st2) ← emitOps p (indent ++ "  ") paramPrefix paramCount els st1
        st := { st2 with last := none }
        acc := acc ++
          indent ++ "let " ++ nm ++ " := " ++ cmpYul c lv rv ++ nl ++
          indent ++ "if " ++ nm ++ " " ++ brace thenTxt ++ nl ++
          indent ++ "if iszero(" ++ nm ++ ") " ++ brace elseTxt ++ nl
    | .systemTransfer _ =>
        throw "extract/unsupported: evm rejects systemTransfer"
    | .evmDeposit amount =>
        let (pre, amt, st') ← materializeVal p indent paramPrefix paramCount amount st
        st := st'
        acc := acc ++ pre ++
          indent ++ "if iszero(eq(callvalue(), " ++ amt ++ ")) { " ++ revert0 ++ " }" ++ nl
        st := { st with last := some amt }
    | .evmSendEth w0 w1 w2 amount =>
        let (p0, a0, st0) ← materializeVal p indent paramPrefix paramCount w0 st
        let (p1, a1, st1) ← materializeVal p indent paramPrefix paramCount w1 st0
        let (p2, a2, st2) ← materializeVal p indent paramPrefix paramCount w2 st1
        let (p3, amt, st3) ← materializeVal p indent paramPrefix paramCount amount st2
        st := st3
        let (ok, st') := fresh st
        st := st'
        acc := acc ++ p0 ++ p1 ++ p2 ++ p3 ++
          indent ++ "if shr(32, " ++ a2 ++ ") { " ++ revert0 ++ " }" ++ nl ++
          indent ++ "mstore(0, 0)" ++ nl ++
          packAddrMstore8 indent a0 a1 a2 ++
          indent ++ "let " ++ ok ++ " := call(gas(), mload(0), " ++ amt ++
            ", 0, 0, 0, 0)" ++ nl ++
          indent ++ "if iszero(" ++ ok ++ ") { " ++ revert0 ++ " }" ++ nl
        st := { st with last := some amt }
    | .evmLogTipped amount =>
        let (pre, amt, st') ← materializeVal p indent paramPrefix paramCount amount st
        st := st'
        acc := acc ++ pre ++
          indent ++ "mstore(0, " ++ amt ++ ")" ++ nl ++
          indent ++ "log1(0, 32, 0x" ++ Keccak.keccak256HexOfString "Tipped(uint64)" ++ ")" ++ nl
        st := { st with last := some amt }
    | .okState v =>
        if IR.hasOptionLeaves p then
          let tagN := optionTagName p
          let payN := optionPayName p
          match v with
          | .lit 0 =>
              acc := acc ++ (← storeNamed p indent tagN "0")
              acc := acc ++ (← storeNamed p indent payN "0")
              acc := acc ++ returnWord indent "0"
          | .lit k =>
              acc := acc ++ (← storeNamed p indent tagN "1")
              acc := acc ++ (← storeNamed p indent payN (yulLit k))
              acc := acc ++ returnWord indent (yulLit k)
          | _ =>
              let (pre, payload, st') ← materializeVal p indent paramPrefix paramCount v st
              st := st'
              acc := acc ++ pre
              acc := acc ++ (← storeNamed p indent tagN "1")
              acc := acc ++ (← storeNamed p indent payN payload)
              acc := acc ++ returnWord indent payload
        else
          let destName := destForOk p ops v
          let destS ← slotOf p destName
          let value ←
            match st.last with
            | some nm => pure nm
            | none =>
                match v with
                | .field _ fname =>
                    if fname.contains '_' && (IR.slotIndex p fname).isSome then
                      loadVal p paramPrefix paramCount (.arg 0)
                    else if Ops.hasCheckedArith ops then
                      loadVal p paramPrefix paramCount v
                    else
                      loadVal p paramPrefix paramCount (.arg 0)
                | _ =>
                    let (pre, e, st') ← materializeVal p indent paramPrefix paramCount v st
                    st := st'
                    acc := acc ++ pre
                    pure e
          let w := (IR.slotWidth p destName).getD 8
          acc := acc ++ storeSlot indent destS (maskExpr w value) ++ returnWord indent value
        st := { st with last := none }
    | .errorOverflow =>
        -- 抽出序列在 checked 算术后仍带 overflow 叶；Yul 已在运算前 revert。
        unless Ops.hasCheckedArith ops do
          acc := acc ++ indent ++ revert0 ++ nl
    | .returnU64 v =>
        let (pre, value, st') ← materializeVal p indent paramPrefix paramCount v st
        st := st'
        acc := acc ++ pre ++ returnWord indent value
    | .returnState v =>
        let (pre, value, st') ← materializeVal p indent paramPrefix paramCount v st
        st := st'
        acc := acc ++ pre
        if nStates > 1 then
          match p.slots[returnStateIdx]? with
          | none => throw "extract/unsupported: returnState exceeds slots"
          | some slot =>
              acc := acc ++ storeSlot indent slot.index (maskExpr slot.width value)
              if returnStateIdx + 1 == nStates then
                acc := acc ++ returnWord indent value
              returnStateIdx := returnStateIdx + 1
        else
          let destName := destHint p ops
          let w := (IR.slotWidth p destName).getD 8
          acc := acc ++ storeSlot indent destSlot0 (maskExpr w value) ++ returnWord indent value
  return (acc, st)

private def q (s : String) : String :=
  "\"" ++ s ++ "\""

private def emitConstructorStores (p : IR.Program) : Except String String := do
  let vs := p.constructor.ops.filterMap (fun | .returnState v => some v | _ => none)
  if vs.isEmpty then
    throw "extract/unsupported: init missing returnState"
  let mut body := ""
  let mut i : Nat := 0
  for s in p.slots do
    if h : i < vs.size then
      let v ← loadVal p "ctor_arg" p.constructor.paramCount vs[i]
      unless v == "0" do
        body := body ++ storeSlot "    " s.index (maskExpr s.width v)
    i := i + 1
  return body

private def renderCtorPrelude (objectName : String) (paramCount : Nat) : String :=
  Id.run do
    let argumentBytes := paramCount * 32
    let mut out :=
      "    if callvalue() { " ++ revert0 ++ " }" ++ nl ++
      "    let programSize := datasize(" ++ q objectName ++ ")" ++ nl ++
      "    if iszero(eq(codesize(), add(programSize, " ++ toString argumentBytes ++
        "))) { " ++ revert0 ++ " }" ++ nl
    if argumentBytes > 0 then
      out := out ++ "    codecopy(0, programSize, " ++ toString argumentBytes ++ ")" ++ nl
    for i in [0:paramCount] do
      out := out ++
        "    let ctor_arg" ++ toString i ++ " := mload(" ++ toString (i * 32) ++ ")" ++ nl ++
        "    if gt(ctor_arg" ++ toString i ++ ", " ++ u64MaxYul ++ ") { " ++
          revert0 ++ " }" ++ nl
    return out

private def renderRuntimeCopy (runtimeName : String) : String :=
  "    datacopy(0, dataoffset(" ++ q runtimeName ++ "), datasize(" ++ q runtimeName ++ "))" ++ nl ++
  "    return(0, datasize(" ++ q runtimeName ++ "))" ++ nl

private def hasPayableEntry (p : IR.Program) : Bool :=
  p.entries.any (·.payable)

private def renderEntry (p : IR.Program) (m : IR.Method) (localValueGuard : Bool) :
    Except String String := do
  let calldataBytes := 4 + m.paramCount * 32
  let mut head :=
    "      case 0x" ++ m.selector ++ " {" ++ nl ++
    "        if iszero(eq(calldatasize(), " ++ toString calldataBytes ++ ")) { " ++
      revert0 ++ " }" ++ nl
  if localValueGuard && !m.payable then
    head := head ++ "        if callvalue() { " ++ revert0 ++ " }" ++ nl
  for i in [0:m.paramCount] do
    let off := 4 + i * 32
    head := head ++
      "        let arg" ++ toString i ++ " := calldataload(" ++ toString off ++ ")" ++ nl ++
      "        if gt(arg" ++ toString i ++ ", " ++ u64MaxYul ++ ") { " ++
        revert0 ++ " }" ++ nl
  let (body, _) ← emitOps p "        " "arg" m.paramCount m.ops {}
  if body == "" then
    throw s!"extract/unsupported: empty ops {m.ixName}"
  return head ++ body ++ "      }" ++ nl

def emitYul (p : IR.Program) : Except String String := do
  if p.entries.isEmpty then
    throw "extract/unsupported: evm wants at least one entry"
  let runtimeName := p.name ++ "_runtime"
  let ctorHead := renderCtorPrelude p.name p.constructor.paramCount
  let ctorStores ← emitConstructorStores p
  let anyPay := hasPayableEntry p
  let mut entries := ""
  for m in p.entries do
    entries := entries ++ (← renderEntry p m anyPay)
  let globalGuard :=
    if anyPay then ""
    else "      if callvalue() { " ++ revert0 ++ " }" ++ nl
  let yul :=
    "// SOLANA-LEAN-EVM-YUL v0" ++ nl ++
    "// digest=" ++ IR.digestHex p ++ nl ++
    "object " ++ q p.name ++ " {" ++ nl ++
    "  code {" ++ nl ++
    ctorHead ++ ctorStores ++ renderRuntimeCopy runtimeName ++
    "  }" ++ nl ++
    "  object " ++ q runtimeName ++ " {" ++ nl ++
    "    code {" ++ nl ++
    globalGuard ++
    "      if lt(calldatasize(), 4) { " ++ revert0 ++ " }" ++ nl ++
    "      switch shr(224, calldataload(0))" ++ nl ++
    entries ++
    "      default { " ++ revert0 ++ " }" ++ nl ++
    "    }" ++ nl ++
    "  }" ++ nl ++
    "}" ++ nl
  return yul

private def escapeJson (s : String) : String :=
  s.replace "\\" "\\\\" |>.replace "\"" "\\\""

private def paramJson (i : Nat) : String :=
  "{\"name\":\"arg" ++ toString i ++ "\",\"type\":\"uint64\"}"

private def paramsJson (n : Nat) : String :=
  String.intercalate "," ((List.range n).map paramJson)

private def ctorAbi (p : IR.Program) : String :=
  "{\"type\":\"constructor\",\"stateMutability\":\"nonpayable\",\"inputs\":[" ++
    paramsJson p.constructor.paramCount ++ "]}"

private def entryAbi (m : IR.Method) : String :=
  let mutab := if m.view then "view" else if m.payable then "payable" else "nonpayable"
  "{\"type\":\"function\",\"name\":\"" ++ escapeJson m.ixName ++
    "\",\"stateMutability\":\"" ++ mutab ++ "\",\"inputs\":[" ++
    paramsJson m.paramCount ++
    "],\"outputs\":[{\"name\":\"\",\"type\":\"uint64\"}]}"

def emitAbi (p : IR.Program) : String :=
  let items := #[ctorAbi p] ++ p.entries.map entryAbi
  "[\n  " ++ String.intercalate ",\n  " items.toList ++ "\n]\n"

def emit (p : IR.Program) : Except String (String × String) := do
  let yul ← emitYul p
  return (yul, emitAbi p)

end SolanaLean.Evm.Emit
