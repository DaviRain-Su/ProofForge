import ProofForge.Evm.Ops
import ProofForge.Evm.IR
import ProofForge.Crypto.Keccak

namespace ProofForge.Evm.Emit

open ProofForge
open ProofForge.Evm
open ProofForge.Crypto

private def u64MaxYul : String := "0xffffffffffffffff"

private def returnStateCount (ops : Array IR.Op) : Nat :=
  ops.foldl (init := 0) fun acc op =>
    match op with
    | .returnState _ => acc + 1
    | _ => acc

private def destHint (p : IR.Program) (ops : Array IR.Op) : String :=
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
private def destForOk (p : IR.Program) (ops : Array IR.Op) (v : Ops.Val) : String :=
  match v with
  | .field _ fname =>
      if IR.hasCheckedArith ops then destHint p ops
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
  else s!"0x{Core.IR.u64Hex n}"

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

/-- 调用 runtime helper，把三叶小端 Addr20 写成 memory[0..31] 的 ABI address word。 -/
private def packAddrMstore8 (indent w0 w1 w2 : String) : String :=
  indent ++ "pf_store_addr20(0, " ++ w0 ++ ", " ++ w1 ++ ", " ++ w2 ++ ")" ++ nl

/-- 把三叶 Addr20 写到 calldata 的 `off..off+19`（transfer 的 dest 从 16 起）。 -/
private def packAddrAt (indent : String) (off : Nat) (w0 w1 w2 : String) : String :=
  indent ++ "pf_store_addr20(" ++ toString (off - 12) ++ ", " ++ w0 ++ ", " ++ w1 ++
    ", " ++ w2 ++ ")" ++ nl

/-- Runtime address encoder. Keeping the byte shuffle behind a Yul function prevents the
optimizer from carrying twenty expanded `mstore8` expressions across CFG dispatcher cases. -/
private def renderAddr20Helper : String :=
  Id.run do
    let mut out := "      function pf_store_addr20(off, w0, w1, w2) {" ++ nl ++
      "        mstore(off, 0)" ++ nl
    for i in [0:8] do
      out := out ++ "        mstore8(add(off, " ++ toString (12 + i) ++ "), and(shr(" ++
        toString (8 * i) ++ ", w0), 0xff))" ++ nl
    for i in [0:8] do
      out := out ++ "        mstore8(add(off, " ++ toString (20 + i) ++ "), and(shr(" ++
        toString (8 * i) ++ ", w1), 0xff))" ++ nl
    for i in [0:4] do
      out := out ++ "        mstore8(add(off, " ++ toString (28 + i) ++ "), and(shr(" ++
        toString (8 * i) ++ ", w2), 0xff))" ++ nl
    return out ++ "      }" ++ nl

private def widthMask (width : Nat) : String :=
  match width with
  | 1 => "0xff"
  | 2 => "0xffff"
  | 4 => "0xffffffff"
  | 20 => "0xffffffffffffffffffffffffffffffffffffffff"
  | 32 => "0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff"
  | _ => u64MaxYul

private def addrLeafOff : String → Option Nat
  | "w0" => some 0
  | "w1" => some 1
  | "w2" => some 2
  | _ => none

private def uint256LeafOff : String → Option Nat
  | "w0" => some 0
  | "w1" => some 1
  | "w2" => some 2
  | "w3" => some 3
  | _ => none

/-- Little-endian 64-bit limb `word` of a 256-bit ABI/storage word. -/
private def packU256Word (src : String) (word : Nat) : String :=
  "and(shr(" ++ toString (64 * word) ++ ", " ++ src ++ "), " ++ u64MaxYul ++ ")"

private def packU256 (w0 w1 w2 w3 : String) : String :=
  "or(or(" ++ w0 ++ ", shl(64, " ++ w1 ++ ")), or(shl(128, " ++ w2 ++ "), shl(192, " ++ w3 ++ ")))"

private def maskExpr (width : Nat) (value : String) : String :=
  if width == 8 then value else "and(" ++ value ++ ", " ++ widthMask width ++ ")"

private def cmpYul (c : Ops.Cmp) (l r : String) : String :=
  match c with
  | .eq => s!"eq({l}, {r})"
  | .ne => s!"iszero(eq({l}, {r}))"
  | .lt => s!"lt({l}, {r})"
  | .le => s!"iszero(gt({l}, {r}))"
  | .gt => s!"gt({l}, {r})"
  | .ge => s!"iszero(lt({l}, {r}))"

private def loadVal (p : IR.Program) (paramPrefix : String) (paramCount : Nat)
    (paramWidths : Array Nat) (v : Ops.Val) : Except String String :=
  match v with
  | .lit n => .ok (yulLit n)
  | .arg i =>
      if i < paramCount then
        .ok s!"{paramPrefix}{i}"
      else
        .error "extract/unsupported: evm arg is implicit state"
  | .local i => .ok s!"l{i}"
  | .field (.arg i) name =>
      if i < paramCount then
        match uint256LeafOff name, (paramWidths[i]?).getD 8 with
        | some off, 32 => .ok (packU256Word s!"{paramPrefix}{i}" off)
        | some off, 33 => .ok (packU256Word s!"{paramPrefix}{i}" off)
        | _, _ =>
          match addrLeafOff name with
          | some off => .ok (packAddrWord s!"{paramPrefix}{i}" off)
          | none => do
              let slot ← slotOf p name
              let w := (IR.slotWidth p name).getD 8
              return maskExpr w s!"sload({slot})"
      else do
        let slot ← slotOf p name
        let w := (IR.slotWidth p name).getD 8
        return maskExpr w s!"sload({slot})"
  | .field _ name => do
      let slot ← slotOf p name
      let w := (IR.slotWidth p name).getD 8
      return maskExpr w s!"sload({slot})"
  | .ext .caller #[] => .ok "and(caller(), 0xffffffffffffffff)"
  | .ext .blockNumber #[] => .ok "number()"
  | .ext .timestamp #[] => .ok "timestamp()"
  | .ext .chainId #[] => .ok "chainid()"
  | .ext .self #[] => .ok "and(address(), 0xffffffffffffffff)"
  | .ext .callValue #[] => .ok "callvalue()"
  | .ext .selfBalance #[] => .ok "selfbalance()"
  | .ext .callerW0 #[] => .ok (packAddrWord "caller()" 0)
  | .ext .callerW1 #[] => .ok (packAddrWord "caller()" 1)
  | .ext .callerW2 #[] => .ok (packAddrWord "caller()" 2)
  | .ext .selfW0 #[] => .ok (packAddrWord "address()" 0)
  | .ext .selfW1 #[] => .ok (packAddrWord "address()" 1)
  | .ext .selfW2 #[] => .ok (packAddrWord "address()" 2)
  | .ext .immU64 #[] => .ok "loadimmutable(\"imm0\")"
  | .ext .immU64b #[] => .ok "loadimmutable(\"imm1\")"
  | .ext .immW0 #[] => .ok (packAddrWord "loadimmutable(\"immAddr\")" 0)
  | .ext .immW1 #[] => .ok (packAddrWord "loadimmutable(\"immAddr\")" 1)
  | .ext .immW2 #[] => .ok (packAddrWord "loadimmutable(\"immAddr\")" 2)
  | .ext .immX0 #[] => .ok (packAddrWord "loadimmutable(\"immAddr2\")" 0)
  | .ext .immX1 #[] => .ok (packAddrWord "loadimmutable(\"immAddr2\")" 1)
  | .ext .immX2 #[] => .ok (packAddrWord "loadimmutable(\"immAddr2\")" 2)
  | .bitAnd l r => do
      let lv ← loadVal p paramPrefix paramCount paramWidths l
      let rv ← loadVal p paramPrefix paramCount paramWidths r
      return "and(" ++ lv ++ ", " ++ rv ++ ")"
  | .bitOr l r => do
      let lv ← loadVal p paramPrefix paramCount paramWidths l
      let rv ← loadVal p paramPrefix paramCount paramWidths r
      return "or(" ++ lv ++ ", " ++ rv ++ ")"
  | .bitXor l r => do
      let lv ← loadVal p paramPrefix paramCount paramWidths l
      let rv ← loadVal p paramPrefix paramCount paramWidths r
      return "xor(" ++ lv ++ ", " ++ rv ++ ")"
  | .bitNot v => do
      let ev ← loadVal p paramPrefix paramCount paramWidths v
      return "and(not(" ++ ev ++ "), " ++ u64MaxYul ++ ")"
  | .shiftL l r => do
      let lv ← loadVal p paramPrefix paramCount paramWidths l
      let rv ← loadVal p paramPrefix paramCount paramWidths r
      return "and(shl(and(" ++ rv ++ ", 63), " ++ lv ++ "), " ++ u64MaxYul ++ ")"
  | .shiftR l r => do
      let lv ← loadVal p paramPrefix paramCount paramWidths l
      let rv ← loadVal p paramPrefix paramCount paramWidths r
      return "shr(and(" ++ rv ++ ", 63), " ++ lv ++ ")"
  | .indexGet _ name idx _len off => do
      let iv ← loadVal p paramPrefix paramCount paramWidths idx
      let some base := IR.vectorBaseSlot p name
        | throw s!"extract/unsupported: unknown vector {name}"
      let some width := IR.vectorLeafWidth p name off
        | throw s!"extract/unsupported: unknown vector leaf {name}+{off}"
      let stride := IR.vectorStrideSlots p name
      let leaf := IR.vectorLeafSlotOffset p name off
      return maskExpr width ("sload(add(" ++ toString (base + leaf) ++ ", mul(" ++ iv ++
        ", " ++ toString stride ++ ")))")
  | .loopIx => .ok "i"
  | .select .. => .error "extract/unsupported: evm select needs materialize"
  | .addU64 .. | .subU64 .. | .mulU64 .. | .divU64 .. | .modU64 .. |
    .ext .mapGetU64 _ | .ext .mapGetAddr _ | .ext .mapGetPair _ |
    .ext (.mapGetAddr256 _) _ | .ext (.mapGetPair256 _) _ |
    .ext (.tokenBalance256 _) _ | .ext (.tokenAllowance256 _) _ |
    .ext (.callValue256 _) _ | .ext (.selfBalance256 _) _ | .ext (.domainSep256 _) _ |
    .ext .ge256 _ | .ext .eq20 _ =>
      .error "extract/unsupported: evm map/arith val needs materialize"
  | .ext _ _ => .error "extract/ir: malformed EVM value operands"

private def revert0 : String := "revert(0, 0)"

private def returnWord (indent value : String) : String :=
  indent ++ "mstore(0, " ++ value ++ ")" ++ nl ++
    indent ++ "return(0, 32)" ++ nl

private def revertNamed (indent name : String) : String :=
  let sel := Keccak.selector name #[]
  indent ++ "mstore(0, shl(224, 0x" ++ sel ++ "))" ++ nl ++
    indent ++ "revert(0, 4)" ++ nl

private def returnU64Count (ops : Array IR.Op) : Nat :=
  ops.foldl (init := 0) fun acc op =>
    match op with
    | .returnU64 _ => acc + 1
    | _ => acc

private def storeSlot (indent : String) (slot : Nat) (value : String) : String :=
  indent ++ "sstore(" ++ toString slot ++ ", " ++ value ++ ")" ++ nl

private def storeNamed (p : IR.Program) (indent name value : String) : Except String String := do
  let slot ← slotOf p name
  let w := (IR.slotWidth p name).getD 8
  return storeSlot indent slot (maskExpr w value)

private structure WideCache where
  key : String
  packed : String
  deriving Inhabited

private structure Render where
  last : Option String := none
  next : Nat := 0
  loopIx : Option String := none
  predeclaredLocals : Bool := false
  wide : Array WideCache := #[]

private def fresh (r : Render) : String × Render :=
  (s!"v{r.next}", { r with next := r.next + 1 })

private def rememberWide (st : Render) (key packed : String) : Render :=
  { st with wide := st.wide.push { key, packed } }

private def lookupWide (st : Render) (key : String) : Option String :=
  (st.wide.find? (·.key == key)).map (·.packed)

private partial def valKey : Ops.Val → String
  | .arg i => s!"a{i}"
  | .local i => s!"v{i}"
  | .lit n => s!"l{n.toNat}"
  | .field b n => s!"f.{n}({valKey b})"
  | .ext kind ops =>
      s!"e.{repr kind}({String.intercalate "," (ops.map valKey).toList})"
  | .bitAnd l r => s!"and({valKey l},{valKey r})"
  | .bitOr l r => s!"or({valKey l},{valKey r})"
  | .bitXor l r => s!"xor({valKey l},{valKey r})"
  | .bitNot v => s!"not({valKey v})"
  | .shiftL l r => s!"shl({valKey l},{valKey r})"
  | .shiftR l r => s!"shr({valKey l},{valKey r})"
  | .addU64 l r => s!"add({valKey l},{valKey r})"
  | .subU64 l r => s!"sub({valKey l},{valKey r})"
  | .mulU64 l r => s!"mul({valKey l},{valKey r})"
  | .divU64 l r => s!"div({valKey l},{valKey r})"
  | .modU64 l r => s!"mod({valKey l},{valKey r})"
  | .indexGet b n i k off => s!"idx.{n}+{off}[{valKey i}/{k}]({valKey b})"
  | .loopIx => "ix"
  | .select c l r t f =>
      s!"sel.{repr c}({valKey l},{valKey r},{valKey t},{valKey f})"

private def eip712DomainTypeHash : String :=
  Keccak.keccak256HexOfString
    "EIP712Domain(string name,string version,uint256 chainId,address verifyingContract)"

private def eip712PermitTypeHash : String :=
  Keccak.keccak256HexOfString
    "Permit(address owner,address spender,uint256 value,uint256 nonce,uint256 deadline)"

private def eip712NameHash : String := Keccak.keccak256HexOfString "Token"

private def eip712VersionHash : String := Keccak.keccak256HexOfString "1"

/-- Closed Token/1 domain hash. Cached on `Render` so permit and DOMAIN_SEPARATOR share it. -/
private def emitDomainSeparator (indent : String) (st : Render) : String × String × Render :=
  match lookupWide st "domsep" with
  | some ret => ("", ret, st)
  | none =>
    let (nameH, st1) := fresh st
    let (verH, st2) := fresh st1
    let (domainH, st3) := fresh st2
    let txt :=
      indent ++ "let " ++ nameH ++ " := 0x" ++ eip712NameHash ++ nl ++
      indent ++ "let " ++ verH ++ " := 0x" ++ eip712VersionHash ++ nl ++
      indent ++ "mstore(0, 0x" ++ eip712DomainTypeHash ++ ")" ++ nl ++
      indent ++ "mstore(32, " ++ nameH ++ ")" ++ nl ++
      indent ++ "mstore(64, " ++ verH ++ ")" ++ nl ++
      indent ++ "mstore(96, chainid())" ++ nl ++
      indent ++ "mstore(128, address())" ++ nl ++
      indent ++ "let " ++ domainH ++ " := keccak256(0, 160)" ++ nl
    (txt, domainH, rememberWide st3 "domsep" domainH)

private def bindChecked (indent name expr : String) : String :=
  indent ++ "let " ++ name ++ " := " ++ expr ++ nl ++
    indent ++ "if gt(" ++ name ++ ", " ++ u64MaxYul ++ ") { " ++ revert0 ++ " }" ++ nl

/-- 环境 opcode / 移位 / 下标必须先检查再当值用。 -/
private def materializeVal (p : IR.Program) (indent paramPrefix : String)
    (paramCount : Nat) (paramWidths : Array Nat) (v : Ops.Val) (st : Render) :
    Except String (String × String × Render) := do
  let checked? : Option String :=
    match v with
    | .ext .blockNumber #[] => some "number()"
    | .ext .timestamp #[] => some "timestamp()"
    | .ext .chainId #[] => some "chainid()"
    | .ext .callValue #[] => some "callvalue()"
    | .ext .selfBalance #[] => some "selfbalance()"
    | _ => none
  match checked? with
  | some expr =>
      let (nm, st') := fresh st
      return (bindChecked indent nm expr, nm, st')
  | none =>
    match v with
    | .bitAnd l r | .bitOr l r | .bitXor l r =>
        let (preL, lv, st1) ← materializeVal p indent paramPrefix paramCount paramWidths l st
        let (preR, rv, st2) ← materializeVal p indent paramPrefix paramCount paramWidths r st1
        let (nm, st3) := fresh st2
        let op :=
          match v with
          | .bitAnd .. => "and"
          | .bitOr .. => "or"
          | _ => "xor"
        let txt := preL ++ preR ++
          indent ++ "let " ++ nm ++ " := " ++ op ++ "(" ++ lv ++ ", " ++ rv ++ ")" ++ nl
        return (txt, nm, st3)
    | .bitNot value =>
        let (pre, valueExpr, st1) ←
          materializeVal p indent paramPrefix paramCount paramWidths value st
        let (nm, st2) := fresh st1
        let txt := pre ++ indent ++ "let " ++ nm ++ " := and(not(" ++ valueExpr ++
          "), " ++ u64MaxYul ++ ")" ++ nl
        return (txt, nm, st2)
    | .shiftL l r | .shiftR l r =>
        let (preR, rv, st1) ← materializeVal p indent paramPrefix paramCount paramWidths r st
        let (preL, lv, st2) ← materializeVal p indent paramPrefix paramCount paramWidths l st1
        let (nm, st3) := fresh st2
        let op := if match v with | .shiftL .. => true | _ => false then "shl" else "shr"
        let shifted := op ++ "(and(" ++ rv ++ ", 63), " ++ lv ++ ")"
        let value :=
          if op == "shl" then "and(" ++ shifted ++ ", " ++ u64MaxYul ++ ")" else shifted
        let txt := preR ++ preL ++
          indent ++ "let " ++ nm ++ " := " ++ value ++ nl
        return (txt, nm, st3)
    | .select c l r t f =>
        let (preL, lv, st1) ← materializeVal p indent paramPrefix paramCount paramWidths l st
        let (preR, rv, st2) ← materializeVal p indent paramPrefix paramCount paramWidths r st1
        let (nm, st3) := fresh st2
        let (preT, tv, st4) ← materializeVal p (indent ++ "  ") paramPrefix paramCount paramWidths t st3
        let (preF, fv, st5) ← materializeVal p (indent ++ "  ") paramPrefix paramCount paramWidths f st4
        let cond := cmpYul c lv rv
        let txt := preL ++ preR ++
          indent ++ "let " ++ nm ++ " := 0" ++ nl ++
          indent ++ "if " ++ cond ++ " {" ++ nl ++ preT ++
          indent ++ "  " ++ nm ++ " := " ++ tv ++ nl ++ indent ++ "}" ++ nl ++
          indent ++ "if iszero(" ++ cond ++ ") {" ++ nl ++ preF ++
          indent ++ "  " ++ nm ++ " := " ++ fv ++ nl ++ indent ++ "}" ++ nl
        return (txt, nm, { st5 with last := some nm })
    | .indexGet _ name idx len off =>
        let (pre, iv, st1) ←
          match idx with
          | .loopIx =>
              pure ("", st.loopIx.getD "i", st)
          | _ => materializeVal p indent paramPrefix paramCount paramWidths idx st
        let some base := IR.vectorBaseSlot p name
          | throw s!"extract/unsupported: unknown vector {name}"
        let some width := IR.vectorLeafWidth p name off
          | throw s!"extract/unsupported: unknown vector leaf {name}+{off}"
        let (nm, st2) := fresh st1
        let bound := toString (IR.vectorLenOf p name len)
        let stride := IR.vectorStrideSlots p name
        let leaf := IR.vectorLeafSlotOffset p name off
        let txt := pre ++
          indent ++ "if iszero(lt(" ++ iv ++ ", " ++ bound ++ ")) { " ++ revert0 ++ " }" ++ nl ++
          indent ++ "let " ++ nm ++ " := " ++ maskExpr width ("sload(add(" ++
            toString (base + leaf) ++ ", mul(" ++ iv ++ ", " ++ toString stride ++ ")))") ++ nl
        return (txt, nm, st2)
    | .loopIx =>
        return ("", st.loopIx.getD "i", st)
    | .addU64 l r =>
        let (preL, lv, st1) ← materializeVal p indent paramPrefix paramCount paramWidths l st
        let (preR, rv, st2) ← materializeVal p indent paramPrefix paramCount paramWidths r st1
        let (nm, st3) := fresh st2
        let txt := preL ++ preR ++
          indent ++ "if gt(" ++ lv ++ ", sub(" ++ u64MaxYul ++ ", " ++ rv ++
            ")) { " ++ revert0 ++ " }" ++ nl ++
          indent ++ "let " ++ nm ++ " := add(" ++ lv ++ ", " ++ rv ++ ")" ++ nl
        return (txt, nm, st3)
    | .subU64 l r =>
        let (preL, lv, st1) ← materializeVal p indent paramPrefix paramCount paramWidths l st
        let (preR, rv, st2) ← materializeVal p indent paramPrefix paramCount paramWidths r st1
        let (nm, st3) := fresh st2
        let txt := preL ++ preR ++
          indent ++ "if lt(" ++ lv ++ ", " ++ rv ++ ") { " ++ revert0 ++ " }" ++ nl ++
          indent ++ "let " ++ nm ++ " := sub(" ++ lv ++ ", " ++ rv ++ ")" ++ nl
        return (txt, nm, st3)
    | .mulU64 l r =>
        let (preL, lv, st1) ← materializeVal p indent paramPrefix paramCount paramWidths l st
        let (preR, rv, st2) ← materializeVal p indent paramPrefix paramCount paramWidths r st1
        let (nm, st3) := fresh st2
        let txt := preL ++ preR ++
          indent ++ "if and(" ++ rv ++ ", gt(" ++ lv ++ ", div(" ++ u64MaxYul ++
            ", " ++ rv ++ "))) { " ++ revert0 ++ " }" ++ nl ++
          indent ++ "let " ++ nm ++ " := mul(" ++ lv ++ ", " ++ rv ++ ")" ++ nl
        return (txt, nm, st3)
    | .divU64 l r =>
        let (preL, lv, st1) ← materializeVal p indent paramPrefix paramCount paramWidths l st
        let (preR, rv, st2) ← materializeVal p indent paramPrefix paramCount paramWidths r st1
        let (nm, st3) := fresh st2
        let txt := preL ++ preR ++
          indent ++ "if iszero(" ++ rv ++ ") { " ++ revert0 ++ " }" ++ nl ++
          indent ++ "let " ++ nm ++ " := div(" ++ lv ++ ", " ++ rv ++ ")" ++ nl
        return (txt, nm, st3)
    | .modU64 l r =>
        let (preL, lv, st1) ← materializeVal p indent paramPrefix paramCount paramWidths l st
        let (preR, rv, st2) ← materializeVal p indent paramPrefix paramCount paramWidths r st1
        let (nm, st3) := fresh st2
        let txt := preL ++ preR ++
          indent ++ "if iszero(" ++ rv ++ ") { " ++ revert0 ++ " }" ++ nl ++
          indent ++ "let " ++ nm ++ " := mod(" ++ lv ++ ", " ++ rv ++ ")" ++ nl
        return (txt, nm, st3)
    | .ext .mapGetU64 #[base, key] =>
        let (pb, b, st1) ← materializeVal p indent paramPrefix paramCount paramWidths base st
        let (pk, k, st2) ← materializeVal p indent paramPrefix paramCount paramWidths key st1
        let (slot, st3) := fresh st2
        let (tag, st4) := fresh st3
        let (pay, st5) := fresh st4
        let txt := pb ++ pk ++
          indent ++ "mstore(0, " ++ k ++ ")" ++ nl ++
          indent ++ "mstore(32, " ++ b ++ ")" ++ nl ++
          indent ++ "let " ++ slot ++ " := keccak256(0, 64)" ++ nl ++
          indent ++ "let " ++ tag ++ " := sload(" ++ slot ++ ")" ++ nl ++
          indent ++ "if gt(" ++ tag ++ ", " ++ u64MaxYul ++ ") { " ++ revert0 ++ " }" ++ nl ++
          indent ++ "let " ++ pay ++ " := 0" ++ nl ++
          indent ++ "if " ++ tag ++ " {" ++ nl ++
          indent ++ "  " ++ pay ++ " := sload(add(" ++ slot ++ ", 1))" ++ nl ++
          indent ++ "  if gt(" ++ pay ++ ", " ++ u64MaxYul ++ ") { " ++ revert0 ++ " }" ++ nl ++
          indent ++ "}" ++ nl
        return (txt, pay, st5)
    | .ext .mapGetAddr #[base, w0, w1, w2] =>
        let (pb, b, st1) ← materializeVal p indent paramPrefix paramCount paramWidths base st
        let (p0, a0, st2) ← materializeVal p indent paramPrefix paramCount paramWidths w0 st1
        let (p1, a1, st3) ← materializeVal p indent paramPrefix paramCount paramWidths w1 st2
        let (p2, a2, st4) ← materializeVal p indent paramPrefix paramCount paramWidths w2 st3
        let (slot, st5) := fresh st4
        let (tag, st6) := fresh st5
        let (pay, st7) := fresh st6
        let txt := pb ++ p0 ++ p1 ++ p2 ++
          indent ++ "mstore(0, " ++ a0 ++ ")" ++ nl ++
          indent ++ "mstore(32, " ++ a1 ++ ")" ++ nl ++
          indent ++ "mstore(64, " ++ a2 ++ ")" ++ nl ++
          indent ++ "mstore(96, " ++ b ++ ")" ++ nl ++
          indent ++ "let " ++ slot ++ " := keccak256(0, 128)" ++ nl ++
          indent ++ "let " ++ tag ++ " := sload(" ++ slot ++ ")" ++ nl ++
          indent ++ "if gt(" ++ tag ++ ", " ++ u64MaxYul ++ ") { " ++ revert0 ++ " }" ++ nl ++
          indent ++ "let " ++ pay ++ " := 0" ++ nl ++
          indent ++ "if " ++ tag ++ " {" ++ nl ++
          indent ++ "  " ++ pay ++ " := sload(add(" ++ slot ++ ", 1))" ++ nl ++
          indent ++ "  if gt(" ++ pay ++ ", " ++ u64MaxYul ++ ") { " ++ revert0 ++ " }" ++ nl ++
          indent ++ "}" ++ nl
        return (txt, pay, st7)
    | .ext .mapGetPair #[base, o0, o1, o2, s0, s1, s2] =>
        let (pb, b, st1) ← materializeVal p indent paramPrefix paramCount paramWidths base st
        let (p0, a0, st2) ← materializeVal p indent paramPrefix paramCount paramWidths o0 st1
        let (p1, a1, st3) ← materializeVal p indent paramPrefix paramCount paramWidths o1 st2
        let (p2, a2, st4) ← materializeVal p indent paramPrefix paramCount paramWidths o2 st3
        let (q0, b0, st5) ← materializeVal p indent paramPrefix paramCount paramWidths s0 st4
        let (q1, b1, st6) ← materializeVal p indent paramPrefix paramCount paramWidths s1 st5
        let (q2, b2, st7) ← materializeVal p indent paramPrefix paramCount paramWidths s2 st6
        let (slot, st8) := fresh st7
        let (tag, st9) := fresh st8
        let (pay, st10) := fresh st9
        let txt := pb ++ p0 ++ p1 ++ p2 ++ q0 ++ q1 ++ q2 ++
          indent ++ "mstore(0, " ++ a0 ++ ")" ++ nl ++
          indent ++ "mstore(32, " ++ a1 ++ ")" ++ nl ++
          indent ++ "mstore(64, " ++ a2 ++ ")" ++ nl ++
          indent ++ "mstore(96, " ++ b0 ++ ")" ++ nl ++
          indent ++ "mstore(128, " ++ b1 ++ ")" ++ nl ++
          indent ++ "mstore(160, " ++ b2 ++ ")" ++ nl ++
          indent ++ "mstore(192, " ++ b ++ ")" ++ nl ++
          indent ++ "let " ++ slot ++ " := keccak256(0, 224)" ++ nl ++
          indent ++ "let " ++ tag ++ " := sload(" ++ slot ++ ")" ++ nl ++
          indent ++ "if gt(" ++ tag ++ ", " ++ u64MaxYul ++ ") { " ++ revert0 ++ " }" ++ nl ++
          indent ++ "let " ++ pay ++ " := 0" ++ nl ++
          indent ++ "if " ++ tag ++ " {" ++ nl ++
          indent ++ "  " ++ pay ++ " := sload(add(" ++ slot ++ ", 1))" ++ nl ++
          indent ++ "  if gt(" ++ pay ++ ", " ++ u64MaxYul ++ ") { " ++ revert0 ++ " }" ++ nl ++
          indent ++ "}" ++ nl
        return (txt, pay, st10)
    | .ext (.mapGetAddr256 limb) #[base, w0, w1, w2] =>
        let (pb, b, st1) ← materializeVal p indent paramPrefix paramCount paramWidths base st
        let (p0, a0, st2) ← materializeVal p indent paramPrefix paramCount paramWidths w0 st1
        let (p1, a1, st3) ← materializeVal p indent paramPrefix paramCount paramWidths w1 st2
        let (p2, a2, st4) ← materializeVal p indent paramPrefix paramCount paramWidths w2 st3
        let cacheKey :=
          "mga256|" ++ valKey base ++ "|" ++ valKey w0 ++ "|" ++ valKey w1 ++ "|" ++ valKey w2
        match lookupWide st4 cacheKey with
        | some pay =>
          let (nm, st5) := fresh st4
          return (pb ++ p0 ++ p1 ++ p2 ++
            indent ++ "let " ++ nm ++ " := " ++ packU256Word pay limb ++ nl, nm, st5)
        | none =>
          let (slot, st5) := fresh st4
          let (tag, st6) := fresh st5
          let (pay, st7) := fresh st6
          let (nm, st8) := fresh (rememberWide st7 cacheKey pay)
          let txt := pb ++ p0 ++ p1 ++ p2 ++
            indent ++ "mstore(0, " ++ a0 ++ ")" ++ nl ++
            indent ++ "mstore(32, " ++ a1 ++ ")" ++ nl ++
            indent ++ "mstore(64, " ++ a2 ++ ")" ++ nl ++
            indent ++ "mstore(96, " ++ b ++ ")" ++ nl ++
            indent ++ "let " ++ slot ++ " := keccak256(0, 128)" ++ nl ++
            indent ++ "let " ++ tag ++ " := sload(" ++ slot ++ ")" ++ nl ++
            indent ++ "if gt(" ++ tag ++ ", " ++ u64MaxYul ++ ") { " ++ revert0 ++ " }" ++ nl ++
            indent ++ "let " ++ pay ++ " := 0" ++ nl ++
            indent ++ "if " ++ tag ++ " {" ++ nl ++
            indent ++ "  " ++ pay ++ " := sload(add(" ++ slot ++ ", 1))" ++ nl ++
            indent ++ "}" ++ nl ++
            indent ++ "let " ++ nm ++ " := " ++ packU256Word pay limb ++ nl
          return (txt, nm, st8)
    | .ext (.mapGetPair256 limb) #[base, o0, o1, o2, s0, s1, s2] =>
        let (pb, b, st1) ← materializeVal p indent paramPrefix paramCount paramWidths base st
        let (p0, a0, st2) ← materializeVal p indent paramPrefix paramCount paramWidths o0 st1
        let (p1, a1, st3) ← materializeVal p indent paramPrefix paramCount paramWidths o1 st2
        let (p2, a2, st4) ← materializeVal p indent paramPrefix paramCount paramWidths o2 st3
        let (q0, b0, st5) ← materializeVal p indent paramPrefix paramCount paramWidths s0 st4
        let (q1, b1, st6) ← materializeVal p indent paramPrefix paramCount paramWidths s1 st5
        let (q2, b2, st7) ← materializeVal p indent paramPrefix paramCount paramWidths s2 st6
        let cacheKey :=
          "mgp256|" ++ valKey base ++ "|" ++ valKey o0 ++ "|" ++ valKey o1 ++ "|" ++ valKey o2 ++
            "|" ++ valKey s0 ++ "|" ++ valKey s1 ++ "|" ++ valKey s2
        match lookupWide st7 cacheKey with
        | some pay =>
          let (nm, st8) := fresh st7
          return (pb ++ p0 ++ p1 ++ p2 ++ q0 ++ q1 ++ q2 ++
            indent ++ "let " ++ nm ++ " := " ++ packU256Word pay limb ++ nl, nm, st8)
        | none =>
          let (slot, st8) := fresh st7
          let (tag, st9) := fresh st8
          let (pay, st10) := fresh st9
          let (nm, st11) := fresh (rememberWide st10 cacheKey pay)
          let txt := pb ++ p0 ++ p1 ++ p2 ++ q0 ++ q1 ++ q2 ++
            indent ++ "mstore(0, " ++ a0 ++ ")" ++ nl ++
            indent ++ "mstore(32, " ++ a1 ++ ")" ++ nl ++
            indent ++ "mstore(64, " ++ a2 ++ ")" ++ nl ++
            indent ++ "mstore(96, " ++ b0 ++ ")" ++ nl ++
            indent ++ "mstore(128, " ++ b1 ++ ")" ++ nl ++
            indent ++ "mstore(160, " ++ b2 ++ ")" ++ nl ++
            indent ++ "mstore(192, " ++ b ++ ")" ++ nl ++
            indent ++ "let " ++ slot ++ " := keccak256(0, 224)" ++ nl ++
            indent ++ "let " ++ tag ++ " := sload(" ++ slot ++ ")" ++ nl ++
            indent ++ "if gt(" ++ tag ++ ", " ++ u64MaxYul ++ ") { " ++ revert0 ++ " }" ++ nl ++
            indent ++ "let " ++ pay ++ " := 0" ++ nl ++
            indent ++ "if " ++ tag ++ " {" ++ nl ++
            indent ++ "  " ++ pay ++ " := sload(add(" ++ slot ++ ", 1))" ++ nl ++
            indent ++ "}" ++ nl ++
            indent ++ "let " ++ nm ++ " := " ++ packU256Word pay limb ++ nl
          return (txt, nm, st11)
    | .ext (.tokenBalance256 limb) #[tw0, tw1, tw2] =>
        let (p0, a0, s0) ← materializeVal p indent paramPrefix paramCount paramWidths tw0 st
        let (p1, a1, s1) ← materializeVal p indent paramPrefix paramCount paramWidths tw1 s0
        let (p2, a2, s2) ← materializeVal p indent paramPrefix paramCount paramWidths tw2 s1
        let cacheKey := "tbal256|" ++ valKey tw0 ++ "|" ++ valKey tw1 ++ "|" ++ valKey tw2
        match lookupWide s2 cacheKey with
        | some ret =>
          let (nm, s3) := fresh s2
          return (p0 ++ p1 ++ p2 ++
            indent ++ "let " ++ nm ++ " := " ++ packU256Word ret limb ++ nl, nm, s3)
        | none =>
          let (tok, s3) := fresh s2
          let (ok, s4) := fresh s3
          let (ret, s5) := fresh s4
          let (nm, s6) := fresh (rememberWide s5 cacheKey ret)
          let txt := p0 ++ p1 ++ p2 ++
            indent ++ "if shr(32, " ++ a2 ++ ") { " ++ revert0 ++ " }" ++ nl ++
            indent ++ "mstore(0, 0)" ++ nl ++
            packAddrMstore8 indent a0 a1 a2 ++
            indent ++ "let " ++ tok ++ " := mload(0)" ++ nl ++
            indent ++ "mstore(0, 0x70a0823100000000000000000000000000000000000000000000000000000000)" ++ nl ++
            indent ++ "mstore(4, address())" ++ nl ++
            indent ++ "let " ++ ok ++ " := staticcall(gas(), " ++ tok ++ ", 0, 36, 0, 32)" ++ nl ++
            indent ++ "if iszero(" ++ ok ++ ") { " ++ revert0 ++ " }" ++ nl ++
            indent ++ "if iszero(eq(returndatasize(), 32)) { " ++ revert0 ++ " }" ++ nl ++
            indent ++ "let " ++ ret ++ " := mload(0)" ++ nl ++
            indent ++ "let " ++ nm ++ " := " ++ packU256Word ret limb ++ nl
          return (txt, nm, s6)
    | .ext (.callValue256 limb) #[] =>
        let cacheKey := "cval256"
        match lookupWide st cacheKey with
        | some ret =>
          let (nm, st') := fresh st
          return (indent ++ "let " ++ nm ++ " := " ++ packU256Word ret limb ++ nl, nm, st')
        | none =>
          let (ret, st1) := fresh st
          let (nm, st2) := fresh (rememberWide st1 cacheKey ret)
          let txt :=
            indent ++ "let " ++ ret ++ " := callvalue()" ++ nl ++
            indent ++ "let " ++ nm ++ " := " ++ packU256Word ret limb ++ nl
          return (txt, nm, st2)
    | .ext (.selfBalance256 limb) #[] =>
        let cacheKey := "sbal256"
        match lookupWide st cacheKey with
        | some ret =>
          let (nm, st') := fresh st
          return (indent ++ "let " ++ nm ++ " := " ++ packU256Word ret limb ++ nl, nm, st')
        | none =>
          let (ret, st1) := fresh st
          let (nm, st2) := fresh (rememberWide st1 cacheKey ret)
          let txt :=
            indent ++ "let " ++ ret ++ " := selfbalance()" ++ nl ++
            indent ++ "let " ++ nm ++ " := " ++ packU256Word ret limb ++ nl
          return (txt, nm, st2)
    | .ext (.domainSep256 limb) #[] =>
        let (pre, ret, st1) := emitDomainSeparator indent st
        let (nm, st2) := fresh st1
        return (pre ++ indent ++ "let " ++ nm ++ " := " ++ packU256Word ret limb ++ nl, nm, st2)
    | .ext (.tokenAllowance256 limb) #[tw0, tw1, tw2, o0, o1, o2, s0, s1, s2] =>
        let (p0, a0, st0) ← materializeVal p indent paramPrefix paramCount paramWidths tw0 st
        let (p1, a1, st1) ← materializeVal p indent paramPrefix paramCount paramWidths tw1 st0
        let (p2, a2, st2) ← materializeVal p indent paramPrefix paramCount paramWidths tw2 st1
        let (q0, b0, st3) ← materializeVal p indent paramPrefix paramCount paramWidths o0 st2
        let (q1, b1, st4) ← materializeVal p indent paramPrefix paramCount paramWidths o1 st3
        let (q2, b2, st5) ← materializeVal p indent paramPrefix paramCount paramWidths o2 st4
        let (r0, c0, st6) ← materializeVal p indent paramPrefix paramCount paramWidths s0 st5
        let (r1, c1, st7) ← materializeVal p indent paramPrefix paramCount paramWidths s1 st6
        let (r2, c2, st8) ← materializeVal p indent paramPrefix paramCount paramWidths s2 st7
        let cacheKey :=
          "tallow256|" ++ valKey tw0 ++ "|" ++ valKey tw1 ++ "|" ++ valKey tw2 ++ "|" ++
            valKey o0 ++ "|" ++ valKey o1 ++ "|" ++ valKey o2 ++ "|" ++
            valKey s0 ++ "|" ++ valKey s1 ++ "|" ++ valKey s2
        match lookupWide st8 cacheKey with
        | some ret =>
          let (nm, st9) := fresh st8
          return (p0 ++ p1 ++ p2 ++ q0 ++ q1 ++ q2 ++ r0 ++ r1 ++ r2 ++
            indent ++ "let " ++ nm ++ " := " ++ packU256Word ret limb ++ nl, nm, st9)
        | none =>
          let (tok, st9) := fresh st8
          let (ok, st10) := fresh st9
          let (ret, st11) := fresh st10
          let (nm, st12) := fresh (rememberWide st11 cacheKey ret)
          let txt := p0 ++ p1 ++ p2 ++ q0 ++ q1 ++ q2 ++ r0 ++ r1 ++ r2 ++
            indent ++ "if shr(32, " ++ a2 ++ ") { " ++ revert0 ++ " }" ++ nl ++
            indent ++ "if shr(32, " ++ b2 ++ ") { " ++ revert0 ++ " }" ++ nl ++
            indent ++ "if shr(32, " ++ c2 ++ ") { " ++ revert0 ++ " }" ++ nl ++
            indent ++ "mstore(0, 0)" ++ nl ++
            packAddrMstore8 indent a0 a1 a2 ++
            indent ++ "let " ++ tok ++ " := mload(0)" ++ nl ++
            indent ++ "mstore(0, 0xdd62ed3e00000000000000000000000000000000000000000000000000000000)" ++ nl ++
            packAddrAt indent 16 b0 b1 b2 ++
            packAddrAt indent 48 c0 c1 c2 ++
            indent ++ "let " ++ ok ++ " := staticcall(gas(), " ++ tok ++ ", 0, 68, 0, 32)" ++ nl ++
            indent ++ "if iszero(" ++ ok ++ ") { " ++ revert0 ++ " }" ++ nl ++
            indent ++ "if iszero(eq(returndatasize(), 32)) { " ++ revert0 ++ " }" ++ nl ++
            indent ++ "let " ++ ret ++ " := mload(0)" ++ nl ++
            indent ++ "let " ++ nm ++ " := " ++ packU256Word ret limb ++ nl
          return (txt, nm, st12)
    | .ext .ge256 #[a0, a1, a2, a3, b0, b1, b2, b3] =>
        let (p0, x0, s0) ← materializeVal p indent paramPrefix paramCount paramWidths a0 st
        let (p1, x1, s1) ← materializeVal p indent paramPrefix paramCount paramWidths a1 s0
        let (p2, x2, s2) ← materializeVal p indent paramPrefix paramCount paramWidths a2 s1
        let (p3, x3, s3) ← materializeVal p indent paramPrefix paramCount paramWidths a3 s2
        let (q0, y0, t0) ← materializeVal p indent paramPrefix paramCount paramWidths b0 s3
        let (q1, y1, t1) ← materializeVal p indent paramPrefix paramCount paramWidths b1 t0
        let (q2, y2, t2) ← materializeVal p indent paramPrefix paramCount paramWidths b2 t1
        let (q3, y3, t3) ← materializeVal p indent paramPrefix paramCount paramWidths b3 t2
        let (av, t4) := fresh t3
        let (bv, t5) := fresh t4
        let (nm, t6) := fresh t5
        let txt := p0 ++ p1 ++ p2 ++ p3 ++ q0 ++ q1 ++ q2 ++ q3 ++
          indent ++ "let " ++ av ++ " := " ++ packU256 x0 x1 x2 x3 ++ nl ++
          indent ++ "let " ++ bv ++ " := " ++ packU256 y0 y1 y2 y3 ++ nl ++
          indent ++ "let " ++ nm ++ " := iszero(lt(" ++ av ++ ", " ++ bv ++ "))" ++ nl
        return (txt, nm, t6)
    | .ext .eq20 #[a0, a1, a2, b0, b1, b2] =>
        let (p0, x0, s0) ← materializeVal p indent paramPrefix paramCount paramWidths a0 st
        let (p1, x1, s1) ← materializeVal p indent paramPrefix paramCount paramWidths a1 s0
        let (p2, x2, s2) ← materializeVal p indent paramPrefix paramCount paramWidths a2 s1
        let (q0, y0, t0) ← materializeVal p indent paramPrefix paramCount paramWidths b0 s2
        let (q1, y1, t1) ← materializeVal p indent paramPrefix paramCount paramWidths b1 t0
        let (q2, y2, t2) ← materializeVal p indent paramPrefix paramCount paramWidths b2 t1
        let (av, t3) := fresh t2
        let (bv, t4) := fresh t3
        let (nm, t5) := fresh t4
        let txt := p0 ++ p1 ++ p2 ++ q0 ++ q1 ++ q2 ++
          indent ++ "mstore(0, 0)" ++ nl ++
          packAddrMstore8 indent x0 x1 x2 ++
          indent ++ "let " ++ av ++ " := mload(0)" ++ nl ++
          indent ++ "mstore(0, 0)" ++ nl ++
          packAddrMstore8 indent y0 y1 y2 ++
          indent ++ "let " ++ bv ++ " := mload(0)" ++ nl ++
          indent ++ "let " ++ nm ++ " := eq(" ++ av ++ ", " ++ bv ++ ")" ++ nl
        return (txt, nm, t5)
    | .ext (.arith256 op limb) #[a0, a1, a2, a3, b0, b1, b2, b3] =>
        let (p0, x0, s0) ← materializeVal p indent paramPrefix paramCount paramWidths a0 st
        let (p1, x1, s1) ← materializeVal p indent paramPrefix paramCount paramWidths a1 s0
        let (p2, x2, s2) ← materializeVal p indent paramPrefix paramCount paramWidths a2 s1
        let (p3, x3, s3) ← materializeVal p indent paramPrefix paramCount paramWidths a3 s2
        let (q0, y0, t0) ← materializeVal p indent paramPrefix paramCount paramWidths b0 s3
        let (q1, y1, t1) ← materializeVal p indent paramPrefix paramCount paramWidths b1 t0
        let (q2, y2, t2) ← materializeVal p indent paramPrefix paramCount paramWidths b2 t1
        let (q3, y3, t3) ← materializeVal p indent paramPrefix paramCount paramWidths b3 t2
        let cacheKey :=
          "arith256|" ++ toString op ++ "|" ++ valKey a0 ++ "|" ++ valKey a1 ++ "|" ++
            valKey a2 ++ "|" ++ valKey a3 ++ "|" ++ valKey b0 ++ "|" ++ valKey b1 ++ "|" ++
            valKey b2 ++ "|" ++ valKey b3
        match lookupWide t3 cacheKey with
        | some rv =>
          let (nm, t4) := fresh t3
          return (p0 ++ p1 ++ p2 ++ p3 ++ q0 ++ q1 ++ q2 ++ q3 ++
            indent ++ "let " ++ nm ++ " := " ++ packU256Word rv limb ++ nl, nm, t4)
        | none =>
          let (av, t4) := fresh t3
          let (bv, t5) := fresh t4
          let (rv, t6) := fresh t5
          let (nm, t7) := fresh (rememberWide t6 cacheKey rv)
          let packedA := packU256 x0 x1 x2 x3
          let packedB := packU256 y0 y1 y2 y3
          let overflow :=
            match op with
            | 0 => "lt(" ++ rv ++ ", " ++ av ++ ")"
            | 1 => "gt(" ++ bv ++ ", " ++ av ++ ")"
            | _ => "and(iszero(iszero(" ++ bv ++ ")), iszero(eq(" ++ av ++ ", div(" ++ rv ++ ", " ++ bv ++ "))))"
          let arith :=
            match op with
            | 0 => "add(" ++ av ++ ", " ++ bv ++ ")"
            | 1 => "sub(" ++ av ++ ", " ++ bv ++ ")"
            | _ => "mul(" ++ av ++ ", " ++ bv ++ ")"
          let txt := p0 ++ p1 ++ p2 ++ p3 ++ q0 ++ q1 ++ q2 ++ q3 ++
            indent ++ "let " ++ av ++ " := " ++ packedA ++ nl ++
            indent ++ "let " ++ bv ++ " := " ++ packedB ++ nl ++
            indent ++ "let " ++ rv ++ " := " ++ arith ++ nl ++
            indent ++ "if " ++ overflow ++ " { " ++ revert0 ++ " }" ++ nl ++
            indent ++ "let " ++ nm ++ " := " ++ packU256Word rv limb ++ nl
          return (txt, nm, t7)
    | _ =>
        let e ← loadVal p paramPrefix paramCount paramWidths v
        return ("", e, st)

private def brace (inner : String) : String :=
  "{" ++ nl ++ inner ++ "}"

private def emitPermit (p : IR.Program) (indent paramPrefix : String)
    (paramCount : Nat) (paramWidths : Array Nat)
    (o0 o1 o2 sA0 sA1 sA2 v0 v1 v2 v3 d0 d1 d2 d3 vv r0 r1 r2 r3 z0 z1 z2 z3 : Ops.Val)
    (st : Render) : Except String (String × Render) := do
  let mut st := st
  let (p0, ow0, st0) ← materializeVal p indent paramPrefix paramCount paramWidths o0 st
  let (p1, ow1, st1) ← materializeVal p indent paramPrefix paramCount paramWidths o1 st0
  let (p2, ow2, st2) ← materializeVal p indent paramPrefix paramCount paramWidths o2 st1
  let (q0, sp0, st3) ← materializeVal p indent paramPrefix paramCount paramWidths sA0 st2
  let (q1, sp1, st4) ← materializeVal p indent paramPrefix paramCount paramWidths sA1 st3
  let (q2, sp2, st5) ← materializeVal p indent paramPrefix paramCount paramWidths sA2 st4
  let (u0, n0, st6) ← materializeVal p indent paramPrefix paramCount paramWidths v0 st5
  let (u1, n1, st7) ← materializeVal p indent paramPrefix paramCount paramWidths v1 st6
  let (u2, n2, st8) ← materializeVal p indent paramPrefix paramCount paramWidths v2 st7
  let (u3, n3, st9) ← materializeVal p indent paramPrefix paramCount paramWidths v3 st8
  let (t0, k0, st10) ← materializeVal p indent paramPrefix paramCount paramWidths d0 st9
  let (t1, k1, st11) ← materializeVal p indent paramPrefix paramCount paramWidths d1 st10
  let (t2, k2, st12) ← materializeVal p indent paramPrefix paramCount paramWidths d2 st11
  let (t3, k3, st13) ← materializeVal p indent paramPrefix paramCount paramWidths d3 st12
  let (pv, vbyte, st14) ← materializeVal p indent paramPrefix paramCount paramWidths vv st13
  let (x0, hr0, st15) ← materializeVal p indent paramPrefix paramCount paramWidths r0 st14
  let (x1, hr1, st16) ← materializeVal p indent paramPrefix paramCount paramWidths r1 st15
  let (x2, hr2, st17) ← materializeVal p indent paramPrefix paramCount paramWidths r2 st16
  let (x3, hr3, st18) ← materializeVal p indent paramPrefix paramCount paramWidths r3 st17
  let (y0, hs0, st19) ← materializeVal p indent paramPrefix paramCount paramWidths z0 st18
  let (y1, hs1, st20) ← materializeVal p indent paramPrefix paramCount paramWidths z1 st19
  let (y2, hs2, st21) ← materializeVal p indent paramPrefix paramCount paramWidths z2 st20
  let (y3, hs3, st22) ← materializeVal p indent paramPrefix paramCount paramWidths z3 st21
  let (own, st23) := fresh st22
  let (spd, st24) := fresh st23
  let (amt, st25) := fresh st24
  let (dead, st26) := fresh st25
  let (rword, st27) := fresh st26
  let (sword, st28) := fresh st27
  let (nslot, st29) := fresh st28
  let (ntag, st30) := fresh st29
  let (nonce, st31) := fresh st30
  let (structH, st32) := fresh st31
  let (domPre, domainH, st33) := emitDomainSeparator indent st32
  let (digest, st34) := fresh st33
  let (signer, st35) := fresh st34
  let (aslot, st36) := fresh st35
  st := st36
  let expiredSel := Keccak.selector "Expired" #[]
  let mut acc := ""
  acc := acc ++ p0 ++ p1 ++ p2 ++ q0 ++ q1 ++ q2 ++
  u0 ++ u1 ++ u2 ++ u3 ++ t0 ++ t1 ++ t2 ++ t3 ++ pv ++
  x0 ++ x1 ++ x2 ++ x3 ++ y0 ++ y1 ++ y2 ++ y3 ++
  indent ++ "if shr(32, " ++ ow2 ++ ") { " ++ revert0 ++ " }" ++ nl ++
  indent ++ "if shr(32, " ++ sp2 ++ ") { " ++ revert0 ++ " }" ++ nl ++
  indent ++ "mstore(0, 0)" ++ nl ++
  packAddrMstore8 indent ow0 ow1 ow2 ++
  indent ++ "let " ++ own ++ " := mload(0)" ++ nl ++
  indent ++ "mstore(0, 0)" ++ nl ++
  packAddrMstore8 indent sp0 sp1 sp2 ++
  indent ++ "let " ++ spd ++ " := mload(0)" ++ nl ++
  indent ++ "let " ++ amt ++ " := " ++ packU256 n0 n1 n2 n3 ++ nl ++
  indent ++ "let " ++ dead ++ " := " ++ packU256 k0 k1 k2 k3 ++ nl ++
  indent ++ "let " ++ rword ++ " := " ++ packU256 hr0 hr1 hr2 hr3 ++ nl ++
  indent ++ "let " ++ sword ++ " := " ++ packU256 hs0 hs1 hs2 hs3 ++ nl ++
  indent ++ "if lt(" ++ dead ++ ", timestamp()) {" ++ nl ++
  indent ++ "  mstore(0, shl(224, 0x" ++ expiredSel ++ "))" ++ nl ++
  indent ++ "  revert(0, 4)" ++ nl ++
  indent ++ "}" ++ nl ++
  indent ++ "mstore(0, " ++ ow0 ++ ")" ++ nl ++
  indent ++ "mstore(32, " ++ ow1 ++ ")" ++ nl ++
  indent ++ "mstore(64, " ++ ow2 ++ ")" ++ nl ++
  indent ++ "mstore(96, 2)" ++ nl ++
  indent ++ "let " ++ nslot ++ " := keccak256(0, 128)" ++ nl ++
  indent ++ "let " ++ ntag ++ " := sload(" ++ nslot ++ ")" ++ nl ++
  indent ++ "if gt(" ++ ntag ++ ", " ++ u64MaxYul ++ ") { " ++ revert0 ++ " }" ++ nl ++
  indent ++ "let " ++ nonce ++ " := 0" ++ nl ++
  indent ++ "if " ++ ntag ++ " { " ++ nonce ++ " := sload(add(" ++ nslot ++ ", 1)) }" ++ nl ++
  indent ++ "mstore(0, 0x" ++ eip712PermitTypeHash ++ ")" ++ nl ++
  indent ++ "mstore(32, " ++ own ++ ")" ++ nl ++
  indent ++ "mstore(64, " ++ spd ++ ")" ++ nl ++
  indent ++ "mstore(96, " ++ amt ++ ")" ++ nl ++
  indent ++ "mstore(128, " ++ nonce ++ ")" ++ nl ++
  indent ++ "mstore(160, " ++ dead ++ ")" ++ nl ++
  indent ++ "let " ++ structH ++ " := keccak256(0, 192)" ++ nl ++
  domPre ++
  indent ++ "mstore(0, 0x1901000000000000000000000000000000000000000000000000000000000000)" ++ nl ++
  indent ++ "mstore(2, " ++ domainH ++ ")" ++ nl ++
  indent ++ "mstore(34, " ++ structH ++ ")" ++ nl ++
  indent ++ "let " ++ digest ++ " := keccak256(0, 66)" ++ nl ++
  indent ++ "mstore(0, " ++ digest ++ ")" ++ nl ++
  indent ++ "mstore(32, " ++ vbyte ++ ")" ++ nl ++
  indent ++ "mstore(64, " ++ rword ++ ")" ++ nl ++
  indent ++ "mstore(96, " ++ sword ++ ")" ++ nl ++
  indent ++ "if iszero(staticcall(gas(), 1, 0, 128, 0, 32)) { " ++ revert0 ++ " }" ++ nl ++
  indent ++ "let " ++ signer ++ " := mload(0)" ++ nl
  acc := acc ++
  indent ++ "if iszero(" ++ signer ++ ") { " ++ revert0 ++ " }" ++ nl ++
  indent ++ "if iszero(eq(" ++ signer ++ ", " ++ own ++ ")) {" ++ nl ++
  indent ++ "  mstore(0, shl(224, 0x" ++
    Keccak.selector "Unauthorized" #["address"] ++ "))" ++ nl ++
  indent ++ "  mstore(4, " ++ signer ++ ")" ++ nl ++
  indent ++ "  revert(0, 36)" ++ nl ++
  indent ++ "}" ++ nl ++
  indent ++ "sstore(" ++ nslot ++ ", 1)" ++ nl ++
  indent ++ "sstore(add(" ++ nslot ++ ", 1), add(" ++ nonce ++ ", 1))" ++ nl ++
  indent ++ "mstore(0, " ++ ow0 ++ ")" ++ nl ++
  indent ++ "mstore(32, " ++ ow1 ++ ")" ++ nl ++
  indent ++ "mstore(64, " ++ ow2 ++ ")" ++ nl ++
  indent ++ "mstore(96, " ++ sp0 ++ ")" ++ nl ++
  indent ++ "mstore(128, " ++ sp1 ++ ")" ++ nl ++
  indent ++ "mstore(160, " ++ sp2 ++ ")" ++ nl ++
  indent ++ "mstore(192, 1)" ++ nl ++
  indent ++ "let " ++ aslot ++ " := keccak256(0, 224)" ++ nl ++
  indent ++ "sstore(" ++ aslot ++ ", 1)" ++ nl ++
  indent ++ "sstore(add(" ++ aslot ++ ", 1), " ++ amt ++ ")" ++ nl ++
  indent ++ "mstore(0, " ++ amt ++ ")" ++ nl ++
  indent ++ "log3(0, 32, 0x" ++
    Keccak.keccak256HexOfString "Approval(address,address,uint256)" ++
    ", " ++ own ++ ", " ++ spd ++ ")" ++ nl
  st := { st with last := some n0 }
  return (acc, st)

private def emitTokenPermit (p : IR.Program) (indent paramPrefix : String)
    (paramCount : Nat) (paramWidths : Array Nat)
    (tw0 tw1 tw2 ow0 ow1 ow2 sw0 sw1 sw2 v0 v1 v2 v3 d0 d1 d2 d3 vv r0 r1 r2 r3 z0 z1 z2 z3 : Ops.Val)
    (st : Render) : Except String (String × Render) := do
  let (p0, t0, s0) ← materializeVal p indent paramPrefix paramCount paramWidths tw0 st
  let (p1, t1, s1) ← materializeVal p indent paramPrefix paramCount paramWidths tw1 s0
  let (p2, t2, s2) ← materializeVal p indent paramPrefix paramCount paramWidths tw2 s1
  let (q0, o0, s3) ← materializeVal p indent paramPrefix paramCount paramWidths ow0 s2
  let (q1, o1, s4) ← materializeVal p indent paramPrefix paramCount paramWidths ow1 s3
  let (q2, o2, s5) ← materializeVal p indent paramPrefix paramCount paramWidths ow2 s4
  let (rA0, a0, s6) ← materializeVal p indent paramPrefix paramCount paramWidths sw0 s5
  let (rA1, a1, s7) ← materializeVal p indent paramPrefix paramCount paramWidths sw1 s6
  let (rA2, a2, s8) ← materializeVal p indent paramPrefix paramCount paramWidths sw2 s7
  let (u0, n0, s9) ← materializeVal p indent paramPrefix paramCount paramWidths v0 s8
  let (u1, n1, s10) ← materializeVal p indent paramPrefix paramCount paramWidths v1 s9
  let (u2, n2, s11) ← materializeVal p indent paramPrefix paramCount paramWidths v2 s10
  let (u3, n3, s12) ← materializeVal p indent paramPrefix paramCount paramWidths v3 s11
  let (k0p, k0, s13) ← materializeVal p indent paramPrefix paramCount paramWidths d0 s12
  let (k1p, k1, s14) ← materializeVal p indent paramPrefix paramCount paramWidths d1 s13
  let (k2p, k2, s15) ← materializeVal p indent paramPrefix paramCount paramWidths d2 s14
  let (k3p, k3, s16) ← materializeVal p indent paramPrefix paramCount paramWidths d3 s15
  let (pv, vbyte, s17) ← materializeVal p indent paramPrefix paramCount paramWidths vv s16
  let (x0, hr0, s18) ← materializeVal p indent paramPrefix paramCount paramWidths r0 s17
  let (x1, hr1, s19) ← materializeVal p indent paramPrefix paramCount paramWidths r1 s18
  let (x2, hr2, s20) ← materializeVal p indent paramPrefix paramCount paramWidths r2 s19
  let (x3, hr3, s21) ← materializeVal p indent paramPrefix paramCount paramWidths r3 s20
  let (y0, hs0, s22) ← materializeVal p indent paramPrefix paramCount paramWidths z0 s21
  let (y1, hs1, s23) ← materializeVal p indent paramPrefix paramCount paramWidths z1 s22
  let (y2, hs2, s24) ← materializeVal p indent paramPrefix paramCount paramWidths z2 s23
  let (y3, hs3, s25) ← materializeVal p indent paramPrefix paramCount paramWidths z3 s24
  let (tok, s26) := fresh s25
  let (amt, s27) := fresh s26
  let (dead, s28) := fresh s27
  let (rword, s29) := fresh s28
  let (sword, s30) := fresh s29
  let (ok, s31) := fresh s30
  let (rds, s32) := fresh s31
  let acc :=
    p0 ++ p1 ++ p2 ++ q0 ++ q1 ++ q2 ++ rA0 ++ rA1 ++ rA2 ++
    u0 ++ u1 ++ u2 ++ u3 ++ k0p ++ k1p ++ k2p ++ k3p ++ pv ++
    x0 ++ x1 ++ x2 ++ x3 ++ y0 ++ y1 ++ y2 ++ y3 ++
    indent ++ "if shr(32, " ++ t2 ++ ") { " ++ revert0 ++ " }" ++ nl ++
    indent ++ "if shr(32, " ++ o2 ++ ") { " ++ revert0 ++ " }" ++ nl ++
    indent ++ "if shr(32, " ++ a2 ++ ") { " ++ revert0 ++ " }" ++ nl ++
    indent ++ "mstore(0, 0)" ++ nl ++
    packAddrMstore8 indent t0 t1 t2 ++
    indent ++ "let " ++ tok ++ " := mload(0)" ++ nl ++
    indent ++ "mstore(0, 0xd505accf00000000000000000000000000000000000000000000000000000000)" ++ nl ++
    packAddrAt indent 16 o0 o1 o2 ++
    packAddrAt indent 48 a0 a1 a2 ++
    indent ++ "let " ++ amt ++ " := " ++ packU256 n0 n1 n2 n3 ++ nl ++
    indent ++ "mstore(68, " ++ amt ++ ")" ++ nl ++
    indent ++ "let " ++ dead ++ " := " ++ packU256 k0 k1 k2 k3 ++ nl ++
    indent ++ "mstore(100, " ++ dead ++ ")" ++ nl ++
    indent ++ "mstore(132, " ++ vbyte ++ ")" ++ nl ++
    indent ++ "let " ++ rword ++ " := " ++ packU256 hr0 hr1 hr2 hr3 ++ nl ++
    indent ++ "mstore(164, " ++ rword ++ ")" ++ nl ++
    indent ++ "let " ++ sword ++ " := " ++ packU256 hs0 hs1 hs2 hs3 ++ nl ++
    indent ++ "mstore(196, " ++ sword ++ ")" ++ nl ++
    indent ++ "let " ++ ok ++ " := call(gas(), " ++ tok ++ ", 0, 0, 228, 0, 32)" ++ nl ++
    indent ++ "if iszero(" ++ ok ++ ") { " ++ revert0 ++ " }" ++ nl ++
    indent ++ "let " ++ rds ++ " := returndatasize()" ++ nl ++
    indent ++ "if and(iszero(eq(" ++ rds ++ ", 0)), iszero(eq(" ++ rds ++
      ", 32))) { " ++ revert0 ++ " }" ++ nl ++
    indent ++ "if eq(" ++ rds ++ ", 32) { if iszero(mload(0)) { " ++ revert0 ++ " } }" ++ nl
  return (acc, { s32 with last := some n0 })

private partial def emitOps (p : IR.Program) (indent paramPrefix : String)
    (paramCount : Nat) (paramWidths : Array Nat) (ops : Array IR.Op) (st : Render) :
    Except String (String × Render) := do
  let destSlot0 ← slotOf p (destHint p ops)
  let nStates := returnStateCount ops
  let nRets := returnU64Count ops
  let mut acc := ""
  let mut st := st
  let mut returnStateIdx : Nat := 0
  let mut returnU64Idx : Nat := 0
  for op in ops do
    match op with
    | .letLocal i value =>
        let (pre, valueExpr, st') ← materializeVal p indent paramPrefix paramCount paramWidths value st
        st := { st' with last := some s!"l{i}" }
        let binding := if st.predeclaredLocals then s!"l{i} := " else s!"let l{i} := "
        acc := acc ++ pre ++ indent ++ binding ++ valueExpr ++ nl
    | .joinLocal i =>
        st := { st with last := none }
        let binding := if st.predeclaredLocals then s!"l{i} := 0" else s!"let l{i} := 0"
        acc := acc ++ indent ++ binding ++ nl
    | .setLocal i value =>
        let (pre, valueExpr, st') ← materializeVal p indent paramPrefix paramCount paramWidths value st
        st := { st' with last := some s!"l{i}" }
        acc := acc ++ pre ++ indent ++ s!"l{i} := {valueExpr}" ++ nl
    | .checkedAddU64 l r =>
        let lv ← loadVal p paramPrefix paramCount paramWidths l
        let rv ← loadVal p paramPrefix paramCount paramWidths r
        let (nm, st') := fresh st
        st := st'
        acc := acc ++
          indent ++ "if gt(" ++ lv ++ ", sub(" ++ u64MaxYul ++ ", " ++ rv ++ ")) { " ++
            revert0 ++ " }" ++ nl ++
          indent ++ "let " ++ nm ++ " := add(" ++ lv ++ ", " ++ rv ++ ")" ++ nl
        st := { st with last := some nm }
    | .checkedSubU64 l r =>
        let lv ← loadVal p paramPrefix paramCount paramWidths l
        let rv ← loadVal p paramPrefix paramCount paramWidths r
        let (nm, st') := fresh st
        st := st'
        acc := acc ++
          indent ++ "if lt(" ++ lv ++ ", " ++ rv ++ ") { " ++ revert0 ++ " }" ++ nl ++
          indent ++ "let " ++ nm ++ " := sub(" ++ lv ++ ", " ++ rv ++ ")" ++ nl
        st := { st with last := some nm }
    | .checkedMulU64 l r =>
        let lv ← loadVal p paramPrefix paramCount paramWidths l
        let rv ← loadVal p paramPrefix paramCount paramWidths r
        let (nm, st') := fresh st
        st := st'
        acc := acc ++
          indent ++ "let " ++ nm ++ " := mul(" ++ lv ++ ", " ++ rv ++ ")" ++ nl ++
          indent ++ "if gt(" ++ nm ++ ", " ++ u64MaxYul ++ ") { " ++ revert0 ++ " }" ++ nl
        st := { st with last := some nm }
    | .checkedDivU64 l r =>
        let lv ← loadVal p paramPrefix paramCount paramWidths l
        let rv ← loadVal p paramPrefix paramCount paramWidths r
        let (nm, st') := fresh st
        st := st'
        acc := acc ++
          indent ++ "if iszero(" ++ rv ++ ") { " ++ revert0 ++ " }" ++ nl ++
          indent ++ "let " ++ nm ++ " := div(" ++ lv ++ ", " ++ rv ++ ")" ++ nl
        st := { st with last := some nm }
    | .checkedModU64 l r =>
        let lv ← loadVal p paramPrefix paramCount paramWidths l
        let rv ← loadVal p paramPrefix paramCount paramWidths r
        let (nm, st') := fresh st
        st := st'
        acc := acc ++
          indent ++ "if iszero(" ++ rv ++ ") { " ++ revert0 ++ " }" ++ nl ++
          indent ++ "let " ++ nm ++ " := mod(" ++ lv ++ ", " ++ rv ++ ")" ++ nl
        st := { st with last := some nm }
    | .ite c l r thn els =>
        let (preL, lv, stL) ← materializeVal p indent paramPrefix paramCount paramWidths l st
        let (preR, rv, stR) ← materializeVal p indent paramPrefix paramCount paramWidths r stL
        let (nm, st') := fresh stR
        st := { st' with wide := #[] }
        let (thenTxt, st1) ← emitOps p (indent ++ "  ") paramPrefix paramCount paramWidths thn st
        let (elseTxt, st2) ←
          emitOps p (indent ++ "  ") paramPrefix paramCount paramWidths els { st1 with wide := #[] }
        st := { st2 with last := none, wide := #[] }
        acc := acc ++ preL ++ preR ++
          indent ++ "let " ++ nm ++ " := " ++ cmpYul c lv rv ++ nl ++
          indent ++ "if " ++ nm ++ " " ++ brace thenTxt ++ nl ++
          indent ++ "if iszero(" ++ nm ++ ") " ++ brace elseTxt ++ nl
    | .evmDeposit amount =>
        let (pre, amt, st') ← materializeVal p indent paramPrefix paramCount paramWidths amount st
        st := st'
        acc := acc ++ pre ++
          indent ++ "if iszero(eq(callvalue(), " ++ amt ++ ")) { " ++ revert0 ++ " }" ++ nl
        st := { st with last := some amt }
    | .evmDeposit256 a0 a1 a2 a3 =>
        let (p0, x0, s0) ← materializeVal p indent paramPrefix paramCount paramWidths a0 st
        let (p1, x1, s1) ← materializeVal p indent paramPrefix paramCount paramWidths a1 s0
        let (p2, x2, s2) ← materializeVal p indent paramPrefix paramCount paramWidths a2 s1
        let (p3, x3, s3) ← materializeVal p indent paramPrefix paramCount paramWidths a3 s2
        let (amt, s4) := fresh s3
        st := s4
        acc := acc ++ p0 ++ p1 ++ p2 ++ p3 ++
          indent ++ "let " ++ amt ++ " := " ++ packU256 x0 x1 x2 x3 ++ nl ++
          indent ++ "if iszero(eq(callvalue(), " ++ amt ++ ")) { " ++ revert0 ++ " }" ++ nl
        st := { st with last := some x0 }
    | .evmSendEth w0 w1 w2 amount =>
        let (p0, a0, st0) ← materializeVal p indent paramPrefix paramCount paramWidths w0 st
        let (p1, a1, st1) ← materializeVal p indent paramPrefix paramCount paramWidths w1 st0
        let (p2, a2, st2) ← materializeVal p indent paramPrefix paramCount paramWidths w2 st1
        let (p3, amt, st3) ← materializeVal p indent paramPrefix paramCount paramWidths amount st2
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
    | .evmSendEth256 w0 w1 w2 a0 a1 a2 a3 =>
        let (p0, d0, s0) ← materializeVal p indent paramPrefix paramCount paramWidths w0 st
        let (p1, d1, s1) ← materializeVal p indent paramPrefix paramCount paramWidths w1 s0
        let (p2, d2, s2) ← materializeVal p indent paramPrefix paramCount paramWidths w2 s1
        let (q0, x0, s3) ← materializeVal p indent paramPrefix paramCount paramWidths a0 s2
        let (q1, x1, s4) ← materializeVal p indent paramPrefix paramCount paramWidths a1 s3
        let (q2, x2, s5) ← materializeVal p indent paramPrefix paramCount paramWidths a2 s4
        let (q3, x3, s6) ← materializeVal p indent paramPrefix paramCount paramWidths a3 s5
        let (amt, s7) := fresh s6
        let (ok, s8) := fresh s7
        st := s8
        acc := acc ++ p0 ++ p1 ++ p2 ++ q0 ++ q1 ++ q2 ++ q3 ++
          indent ++ "if shr(32, " ++ d2 ++ ") { " ++ revert0 ++ " }" ++ nl ++
          indent ++ "mstore(0, 0)" ++ nl ++
          packAddrMstore8 indent d0 d1 d2 ++
          indent ++ "let " ++ amt ++ " := " ++ packU256 x0 x1 x2 x3 ++ nl ++
          indent ++ "let " ++ ok ++ " := call(gas(), mload(0), " ++ amt ++
            ", 0, 0, 0, 0)" ++ nl ++
          indent ++ "if iszero(" ++ ok ++ ") { " ++ revert0 ++ " }" ++ nl
        st := { st with last := some x0 }
    | .evmLog name amount =>
        let (pre, amt, st') ← materializeVal p indent paramPrefix paramCount paramWidths amount st
        st := st'
        acc := acc ++ pre ++
          indent ++ "mstore(0, " ++ amt ++ ")" ++ nl ++
          indent ++ "log1(0, 32, 0x" ++
            Keccak.keccak256HexOfString (name ++ "(uint64)") ++ ")" ++ nl
        st := { st with last := some amt }
    | .evmLogTransfer256 f0 f1 f2 t0 t1 t2 a0 a1 a2 a3 =>
        let (p0, x0, s0) ← materializeVal p indent paramPrefix paramCount paramWidths f0 st
        let (p1, x1, s1) ← materializeVal p indent paramPrefix paramCount paramWidths f1 s0
        let (p2, x2, s2) ← materializeVal p indent paramPrefix paramCount paramWidths f2 s1
        let (q0, y0, s3) ← materializeVal p indent paramPrefix paramCount paramWidths t0 s2
        let (q1, y1, s4) ← materializeVal p indent paramPrefix paramCount paramWidths t1 s3
        let (q2, y2, s5) ← materializeVal p indent paramPrefix paramCount paramWidths t2 s4
        let (r0, z0, s6) ← materializeVal p indent paramPrefix paramCount paramWidths a0 s5
        let (r1, z1, s7) ← materializeVal p indent paramPrefix paramCount paramWidths a1 s6
        let (r2, z2, s8) ← materializeVal p indent paramPrefix paramCount paramWidths a2 s7
        let (r3, z3, s9) ← materializeVal p indent paramPrefix paramCount paramWidths a3 s8
        let (fromT, s10) := fresh s9
        let (toT, s11) := fresh s10
        let (amt, s12) := fresh s11
        st := s12
        acc := acc ++ p0 ++ p1 ++ p2 ++ q0 ++ q1 ++ q2 ++ r0 ++ r1 ++ r2 ++ r3 ++
          indent ++ "mstore(0, 0)" ++ nl ++
          packAddrMstore8 indent x0 x1 x2 ++
          indent ++ "let " ++ fromT ++ " := mload(0)" ++ nl ++
          indent ++ "mstore(0, 0)" ++ nl ++
          packAddrMstore8 indent y0 y1 y2 ++
          indent ++ "let " ++ toT ++ " := mload(0)" ++ nl ++
          indent ++ "let " ++ amt ++ " := " ++ packU256 z0 z1 z2 z3 ++ nl ++
          indent ++ "mstore(0, " ++ amt ++ ")" ++ nl ++
          indent ++ "log3(0, 32, 0x" ++
            Keccak.keccak256HexOfString "Transfer(address,address,uint256)" ++
            ", " ++ fromT ++ ", " ++ toT ++ ")" ++ nl
        st := { st with last := some z0 }
    | .evmLogApproval256 o0 o1 o2 sp0 sp1 sp2 a0 a1 a2 a3 =>
        let (p0, x0, s0) ← materializeVal p indent paramPrefix paramCount paramWidths o0 st
        let (p1, x1, s1) ← materializeVal p indent paramPrefix paramCount paramWidths o1 s0
        let (p2, x2, s2) ← materializeVal p indent paramPrefix paramCount paramWidths o2 s1
        let (q0, y0, s3) ← materializeVal p indent paramPrefix paramCount paramWidths sp0 s2
        let (q1, y1, s4) ← materializeVal p indent paramPrefix paramCount paramWidths sp1 s3
        let (q2, y2, s5) ← materializeVal p indent paramPrefix paramCount paramWidths sp2 s4
        let (r0, z0, s6) ← materializeVal p indent paramPrefix paramCount paramWidths a0 s5
        let (r1, z1, s7) ← materializeVal p indent paramPrefix paramCount paramWidths a1 s6
        let (r2, z2, s8) ← materializeVal p indent paramPrefix paramCount paramWidths a2 s7
        let (r3, z3, s9) ← materializeVal p indent paramPrefix paramCount paramWidths a3 s8
        let (ownT, s10) := fresh s9
        let (spdT, s11) := fresh s10
        let (amt, s12) := fresh s11
        st := s12
        acc := acc ++ p0 ++ p1 ++ p2 ++ q0 ++ q1 ++ q2 ++ r0 ++ r1 ++ r2 ++ r3 ++
          indent ++ "mstore(0, 0)" ++ nl ++
          packAddrMstore8 indent x0 x1 x2 ++
          indent ++ "let " ++ ownT ++ " := mload(0)" ++ nl ++
          indent ++ "mstore(0, 0)" ++ nl ++
          packAddrMstore8 indent y0 y1 y2 ++
          indent ++ "let " ++ spdT ++ " := mload(0)" ++ nl ++
          indent ++ "let " ++ amt ++ " := " ++ packU256 z0 z1 z2 z3 ++ nl ++
          indent ++ "mstore(0, " ++ amt ++ ")" ++ nl ++
          indent ++ "log3(0, 32, 0x" ++
            Keccak.keccak256HexOfString "Approval(address,address,uint256)" ++
            ", " ++ ownT ++ ", " ++ spdT ++ ")" ++ nl
        st := { st with last := some z0 }
    | .evmRevertInsufficient h0 h1 h2 h3 w0 w1 w2 w3 =>
        let (p0, x0, s0) ← materializeVal p indent paramPrefix paramCount paramWidths h0 st
        let (p1, x1, s1) ← materializeVal p indent paramPrefix paramCount paramWidths h1 s0
        let (p2, x2, s2) ← materializeVal p indent paramPrefix paramCount paramWidths h2 s1
        let (p3, x3, s3) ← materializeVal p indent paramPrefix paramCount paramWidths h3 s2
        let (q0, y0, s4) ← materializeVal p indent paramPrefix paramCount paramWidths w0 s3
        let (q1, y1, s5) ← materializeVal p indent paramPrefix paramCount paramWidths w1 s4
        let (q2, y2, s6) ← materializeVal p indent paramPrefix paramCount paramWidths w2 s5
        let (q3, y3, s7) ← materializeVal p indent paramPrefix paramCount paramWidths w3 s6
        st := s7
        let sel := Keccak.selector "Insufficient" #["uint256", "uint256"]
        acc := acc ++ p0 ++ p1 ++ p2 ++ p3 ++ q0 ++ q1 ++ q2 ++ q3 ++
          indent ++ "mstore(0, shl(224, 0x" ++ sel ++ "))" ++ nl ++
          indent ++ "mstore(4, " ++ packU256 x0 x1 x2 x3 ++ ")" ++ nl ++
          indent ++ "mstore(36, " ++ packU256 y0 y1 y2 y3 ++ ")" ++ nl ++
          indent ++ "revert(0, 68)" ++ nl
        st := { st with last := some x0 }
    | .evmRevertUnauthorized w0 w1 w2 =>
        let (p0, a0, s0) ← materializeVal p indent paramPrefix paramCount paramWidths w0 st
        let (p1, a1, s1) ← materializeVal p indent paramPrefix paramCount paramWidths w1 s0
        let (p2, a2, s2) ← materializeVal p indent paramPrefix paramCount paramWidths w2 s1
        let sel := Keccak.selector "Unauthorized" #["address"]
        st := s2
        acc := acc ++ p0 ++ p1 ++ p2 ++
          indent ++ "mstore(0, 0)" ++ nl ++
          packAddrMstore8 indent a0 a1 a2 ++
          indent ++ "let pf_who := mload(0)" ++ nl ++
          indent ++ "mstore(0, shl(224, 0x" ++ sel ++ "))" ++ nl ++
          indent ++ "mstore(4, pf_who)" ++ nl ++
          indent ++ "revert(0, 36)" ++ nl
        st := { st with last := some a0 }
    | .evmRevertZeroAddress =>
        let sel := Keccak.selector "ZeroAddress" #[]
        acc := acc ++
          indent ++ "mstore(0, shl(224, 0x" ++ sel ++ "))" ++ nl ++
          indent ++ "revert(0, 4)" ++ nl
        st := { st with last := some "0" }
    | .evmReceive =>
        acc := acc ++ indent ++ "let pf_recv := callvalue()" ++ nl
        st := { st with last := some "pf_recv" }
    | .forAccum n addend resultLocal =>
        let accN := s!"l{resultLocal}"
        let (iN, st2) := fresh st
        let innerSt := { st2 with loopIx := some iN }
        let (pre, addE, st3) ←
          materializeVal p (indent ++ "  ") paramPrefix paramCount paramWidths addend innerSt
        st := { st3 with loopIx := none }
        acc := acc ++
          indent ++ "let " ++ accN ++ " := 0" ++ nl ++
          indent ++ "for { let " ++ iN ++ " := 0 } lt(" ++ iN ++ ", " ++ toString n ++
            ") { " ++ iN ++ " := add(" ++ iN ++ ", 1) } {" ++ nl ++
          pre ++
          indent ++ "  if gt(" ++ accN ++ ", sub(" ++ u64MaxYul ++ ", " ++ addE ++
            ")) { " ++ revert0 ++ " }" ++ nl ++
          indent ++ "  " ++ accN ++ " := add(" ++ accN ++ ", " ++ addE ++ ")" ++ nl ++
          indent ++ "}" ++ nl
        st := { st with last := some accN }
    | .forBody n body =>
        let (iN, st1) := fresh st
        let innerSt := { st1 with loopIx := some iN }
        let (bodyTxt, st2) ←
          emitOps p (indent ++ "  ") paramPrefix paramCount paramWidths body innerSt
        st := { st2 with loopIx := none }
        acc := acc ++
          indent ++ "for { let " ++ iN ++ " := 0 } lt(" ++ iN ++ ", " ++ toString n ++
            ") { " ++ iN ++ " := add(" ++ iN ++ ", 1) } {" ++ nl ++
          bodyTxt ++
          indent ++ "}" ++ nl
    | .indexSet name idx value len elemOff =>
        let (preI, iv, st1) ← materializeVal p indent paramPrefix paramCount paramWidths idx st
        let (preV, vv, st2) ← materializeVal p indent paramPrefix paramCount paramWidths value st1
        st := st2
        let some base := IR.vectorBaseSlot p name
          | throw s!"extract/unsupported: unknown vector {name}"
        let some width := IR.vectorLeafWidth p name elemOff
          | throw s!"extract/unsupported: unknown vector leaf {name}+{elemOff}"
        let bound := toString (IR.vectorLenOf p name len)
        let stride := IR.vectorStrideSlots p name
        let leaf := IR.vectorLeafSlotOffset p name elemOff
        let stored := maskExpr width vv
        acc := acc ++ preI ++ preV ++
          indent ++ "if iszero(lt(" ++ iv ++ ", " ++ bound ++ ")) { " ++ revert0 ++ " }" ++ nl ++
          indent ++ "sstore(add(" ++ toString (base + leaf) ++ ", mul(" ++ iv ++ ", " ++
            toString stride ++ ")), " ++ stored ++ ")" ++ nl
        st := { st with last := some stored }
    | .mapGetU64 base key =>
        let (pb, b, st1) ← materializeVal p indent paramPrefix paramCount paramWidths base st
        let (pk, k, st2) ← materializeVal p indent paramPrefix paramCount paramWidths key st1
        let (slot, st3) := fresh st2
        let (tag, st4) := fresh st3
        let (pay, st5) := fresh st4
        st := st5
        acc := acc ++ pb ++ pk ++
          indent ++ "mstore(0, " ++ k ++ ")" ++ nl ++
          indent ++ "mstore(32, " ++ b ++ ")" ++ nl ++
          indent ++ "let " ++ slot ++ " := keccak256(0, 64)" ++ nl ++
          indent ++ "let " ++ tag ++ " := sload(" ++ slot ++ ")" ++ nl ++
          indent ++ "if gt(" ++ tag ++ ", " ++ u64MaxYul ++ ") { " ++ revert0 ++ " }" ++ nl ++
          indent ++ "let " ++ pay ++ " := 0" ++ nl ++
          indent ++ "if " ++ tag ++ " {" ++ nl ++
          indent ++ "  " ++ pay ++ " := sload(add(" ++ slot ++ ", 1))" ++ nl ++
          indent ++ "  if gt(" ++ pay ++ ", " ++ u64MaxYul ++ ") { " ++ revert0 ++ " }" ++ nl ++
          indent ++ "}" ++ nl
        st := { st with last := some pay }
    | .mapSetU64 base key value =>
        let (pb, b, st1) ← materializeVal p indent paramPrefix paramCount paramWidths base st
        let (pk, k, st2) ← materializeVal p indent paramPrefix paramCount paramWidths key st1
        let (pv, v, st3) ← materializeVal p indent paramPrefix paramCount paramWidths value st2
        let (slot, st4) := fresh st3
        st := st4
        acc := acc ++ pb ++ pk ++ pv ++
          indent ++ "mstore(0, " ++ k ++ ")" ++ nl ++
          indent ++ "mstore(32, " ++ b ++ ")" ++ nl ++
          indent ++ "let " ++ slot ++ " := keccak256(0, 64)" ++ nl ++
          indent ++ "sstore(" ++ slot ++ ", 1)" ++ nl ++
          indent ++ "sstore(add(" ++ slot ++ ", 1), " ++ v ++ ")" ++ nl
        st := { st with last := some v }
    | .mapGetAddr base w0 w1 w2 =>
        let (pb, b, st1) ← materializeVal p indent paramPrefix paramCount paramWidths base st
        let (p0, a0, st2) ← materializeVal p indent paramPrefix paramCount paramWidths w0 st1
        let (p1, a1, st3) ← materializeVal p indent paramPrefix paramCount paramWidths w1 st2
        let (p2, a2, st4) ← materializeVal p indent paramPrefix paramCount paramWidths w2 st3
        let (slot, st5) := fresh st4
        let (tag, st6) := fresh st5
        let (pay, st7) := fresh st6
        st := st7
        acc := acc ++ pb ++ p0 ++ p1 ++ p2 ++
          indent ++ "mstore(0, " ++ a0 ++ ")" ++ nl ++
          indent ++ "mstore(32, " ++ a1 ++ ")" ++ nl ++
          indent ++ "mstore(64, " ++ a2 ++ ")" ++ nl ++
          indent ++ "mstore(96, " ++ b ++ ")" ++ nl ++
          indent ++ "let " ++ slot ++ " := keccak256(0, 128)" ++ nl ++
          indent ++ "let " ++ tag ++ " := sload(" ++ slot ++ ")" ++ nl ++
          indent ++ "if gt(" ++ tag ++ ", " ++ u64MaxYul ++ ") { " ++ revert0 ++ " }" ++ nl ++
          indent ++ "let " ++ pay ++ " := 0" ++ nl ++
          indent ++ "if " ++ tag ++ " {" ++ nl ++
          indent ++ "  " ++ pay ++ " := sload(add(" ++ slot ++ ", 1))" ++ nl ++
          indent ++ "  if gt(" ++ pay ++ ", " ++ u64MaxYul ++ ") { " ++ revert0 ++ " }" ++ nl ++
          indent ++ "}" ++ nl
        st := { st with last := some pay }
    | .mapSetAddr base w0 w1 w2 value =>
        let (pb, b, st1) ← materializeVal p indent paramPrefix paramCount paramWidths base st
        let (p0, a0, st2) ← materializeVal p indent paramPrefix paramCount paramWidths w0 st1
        let (p1, a1, st3) ← materializeVal p indent paramPrefix paramCount paramWidths w1 st2
        let (p2, a2, st4) ← materializeVal p indent paramPrefix paramCount paramWidths w2 st3
        let (pv, v, st5) ← materializeVal p indent paramPrefix paramCount paramWidths value st4
        let (slot, st6) := fresh st5
        st := st6
        acc := acc ++ pb ++ p0 ++ p1 ++ p2 ++ pv ++
          indent ++ "mstore(0, " ++ a0 ++ ")" ++ nl ++
          indent ++ "mstore(32, " ++ a1 ++ ")" ++ nl ++
          indent ++ "mstore(64, " ++ a2 ++ ")" ++ nl ++
          indent ++ "mstore(96, " ++ b ++ ")" ++ nl ++
          indent ++ "let " ++ slot ++ " := keccak256(0, 128)" ++ nl ++
          indent ++ "sstore(" ++ slot ++ ", 1)" ++ nl ++
          indent ++ "sstore(add(" ++ slot ++ ", 1), " ++ v ++ ")" ++ nl
        st := { st with last := some v }
    | .mapGetPair base o0 o1 o2 s0 s1 s2 =>
        let (pb, b, st1) ← materializeVal p indent paramPrefix paramCount paramWidths base st
        let (p0, a0, st2) ← materializeVal p indent paramPrefix paramCount paramWidths o0 st1
        let (p1, a1, st3) ← materializeVal p indent paramPrefix paramCount paramWidths o1 st2
        let (p2, a2, st4) ← materializeVal p indent paramPrefix paramCount paramWidths o2 st3
        let (q0, b0, st5) ← materializeVal p indent paramPrefix paramCount paramWidths s0 st4
        let (q1, b1, st6) ← materializeVal p indent paramPrefix paramCount paramWidths s1 st5
        let (q2, b2, st7) ← materializeVal p indent paramPrefix paramCount paramWidths s2 st6
        let (slot, st8) := fresh st7
        let (tag, st9) := fresh st8
        let (pay, st10) := fresh st9
        st := st10
        acc := acc ++ pb ++ p0 ++ p1 ++ p2 ++ q0 ++ q1 ++ q2 ++
          indent ++ "mstore(0, " ++ a0 ++ ")" ++ nl ++
          indent ++ "mstore(32, " ++ a1 ++ ")" ++ nl ++
          indent ++ "mstore(64, " ++ a2 ++ ")" ++ nl ++
          indent ++ "mstore(96, " ++ b0 ++ ")" ++ nl ++
          indent ++ "mstore(128, " ++ b1 ++ ")" ++ nl ++
          indent ++ "mstore(160, " ++ b2 ++ ")" ++ nl ++
          indent ++ "mstore(192, " ++ b ++ ")" ++ nl ++
          indent ++ "let " ++ slot ++ " := keccak256(0, 224)" ++ nl ++
          indent ++ "let " ++ tag ++ " := sload(" ++ slot ++ ")" ++ nl ++
          indent ++ "if gt(" ++ tag ++ ", " ++ u64MaxYul ++ ") { " ++ revert0 ++ " }" ++ nl ++
          indent ++ "let " ++ pay ++ " := 0" ++ nl ++
          indent ++ "if " ++ tag ++ " {" ++ nl ++
          indent ++ "  " ++ pay ++ " := sload(add(" ++ slot ++ ", 1))" ++ nl ++
          indent ++ "  if gt(" ++ pay ++ ", " ++ u64MaxYul ++ ") { " ++ revert0 ++ " }" ++ nl ++
          indent ++ "}" ++ nl
        st := { st with last := some pay }
    | .mapSetPair base o0 o1 o2 s0 s1 s2 value =>
        let (pb, b, st1) ← materializeVal p indent paramPrefix paramCount paramWidths base st
        let (p0, a0, st2) ← materializeVal p indent paramPrefix paramCount paramWidths o0 st1
        let (p1, a1, st3) ← materializeVal p indent paramPrefix paramCount paramWidths o1 st2
        let (p2, a2, st4) ← materializeVal p indent paramPrefix paramCount paramWidths o2 st3
        let (q0, b0, st5) ← materializeVal p indent paramPrefix paramCount paramWidths s0 st4
        let (q1, b1, st6) ← materializeVal p indent paramPrefix paramCount paramWidths s1 st5
        let (q2, b2, st7) ← materializeVal p indent paramPrefix paramCount paramWidths s2 st6
        let (pv, v, st8) ← materializeVal p indent paramPrefix paramCount paramWidths value st7
        let (slot, st9) := fresh st8
        st := st9
        acc := acc ++ pb ++ p0 ++ p1 ++ p2 ++ q0 ++ q1 ++ q2 ++ pv ++
          indent ++ "mstore(0, " ++ a0 ++ ")" ++ nl ++
          indent ++ "mstore(32, " ++ a1 ++ ")" ++ nl ++
          indent ++ "mstore(64, " ++ a2 ++ ")" ++ nl ++
          indent ++ "mstore(96, " ++ b0 ++ ")" ++ nl ++
          indent ++ "mstore(128, " ++ b1 ++ ")" ++ nl ++
          indent ++ "mstore(160, " ++ b2 ++ ")" ++ nl ++
          indent ++ "mstore(192, " ++ b ++ ")" ++ nl ++
          indent ++ "let " ++ slot ++ " := keccak256(0, 224)" ++ nl ++
          indent ++ "sstore(" ++ slot ++ ", 1)" ++ nl ++
          indent ++ "sstore(add(" ++ slot ++ ", 1), " ++ v ++ ")" ++ nl
        st := { st with last := some v }
    | .mapSetAddr256 base w0 w1 w2 v0 v1 v2 v3 =>
        let (pb, b, st1) ← materializeVal p indent paramPrefix paramCount paramWidths base st
        let (p0, a0, st2) ← materializeVal p indent paramPrefix paramCount paramWidths w0 st1
        let (p1, a1, st3) ← materializeVal p indent paramPrefix paramCount paramWidths w1 st2
        let (p2, a2, st4) ← materializeVal p indent paramPrefix paramCount paramWidths w2 st3
        let (q0, x0, st5) ← materializeVal p indent paramPrefix paramCount paramWidths v0 st4
        let (q1, x1, st6) ← materializeVal p indent paramPrefix paramCount paramWidths v1 st5
        let (q2, x2, st7) ← materializeVal p indent paramPrefix paramCount paramWidths v2 st6
        let (q3, x3, st8) ← materializeVal p indent paramPrefix paramCount paramWidths v3 st7
        let (slot, st9) := fresh st8
        let (pay, st10) := fresh st9
        st := st10
        acc := acc ++ pb ++ p0 ++ p1 ++ p2 ++ q0 ++ q1 ++ q2 ++ q3 ++
          indent ++ "mstore(0, " ++ a0 ++ ")" ++ nl ++
          indent ++ "mstore(32, " ++ a1 ++ ")" ++ nl ++
          indent ++ "mstore(64, " ++ a2 ++ ")" ++ nl ++
          indent ++ "mstore(96, " ++ b ++ ")" ++ nl ++
          indent ++ "let " ++ slot ++ " := keccak256(0, 128)" ++ nl ++
          indent ++ "let " ++ pay ++ " := " ++ packU256 x0 x1 x2 x3 ++ nl ++
          indent ++ "sstore(" ++ slot ++ ", 1)" ++ nl ++
          indent ++ "sstore(add(" ++ slot ++ ", 1), " ++ pay ++ ")" ++ nl
        st := { st with last := some x0 }
    | .mapSetPair256 base o0 o1 o2 s0 s1 s2 v0 v1 v2 v3 =>
        let (pb, b, st1) ← materializeVal p indent paramPrefix paramCount paramWidths base st
        let (p0, a0, st2) ← materializeVal p indent paramPrefix paramCount paramWidths o0 st1
        let (p1, a1, st3) ← materializeVal p indent paramPrefix paramCount paramWidths o1 st2
        let (p2, a2, st4) ← materializeVal p indent paramPrefix paramCount paramWidths o2 st3
        let (q0, b0, st5) ← materializeVal p indent paramPrefix paramCount paramWidths s0 st4
        let (q1, b1, st6) ← materializeVal p indent paramPrefix paramCount paramWidths s1 st5
        let (q2, b2, st7) ← materializeVal p indent paramPrefix paramCount paramWidths s2 st6
        let (r0, x0, st8) ← materializeVal p indent paramPrefix paramCount paramWidths v0 st7
        let (r1, x1, st9) ← materializeVal p indent paramPrefix paramCount paramWidths v1 st8
        let (r2, x2, st10) ← materializeVal p indent paramPrefix paramCount paramWidths v2 st9
        let (r3, x3, st11) ← materializeVal p indent paramPrefix paramCount paramWidths v3 st10
        let (slot, st12) := fresh st11
        let (pay, st13) := fresh st12
        st := st13
        acc := acc ++ pb ++ p0 ++ p1 ++ p2 ++ q0 ++ q1 ++ q2 ++ r0 ++ r1 ++ r2 ++ r3 ++
          indent ++ "mstore(0, " ++ a0 ++ ")" ++ nl ++
          indent ++ "mstore(32, " ++ a1 ++ ")" ++ nl ++
          indent ++ "mstore(64, " ++ a2 ++ ")" ++ nl ++
          indent ++ "mstore(96, " ++ b0 ++ ")" ++ nl ++
          indent ++ "mstore(128, " ++ b1 ++ ")" ++ nl ++
          indent ++ "mstore(160, " ++ b2 ++ ")" ++ nl ++
          indent ++ "mstore(192, " ++ b ++ ")" ++ nl ++
          indent ++ "let " ++ slot ++ " := keccak256(0, 224)" ++ nl ++
          indent ++ "let " ++ pay ++ " := " ++ packU256 x0 x1 x2 x3 ++ nl ++
          indent ++ "sstore(" ++ slot ++ ", 1)" ++ nl ++
          indent ++ "sstore(add(" ++ slot ++ ", 1), " ++ pay ++ ")" ++ nl
        st := { st with last := some x0 }
    | .evmTokenTransfer tw0 tw1 tw2 dw0 dw1 dw2 amount =>
        let (p0, a0, s0) ← materializeVal p indent paramPrefix paramCount paramWidths tw0 st
        let (p1, a1, s1) ← materializeVal p indent paramPrefix paramCount paramWidths tw1 s0
        let (p2, a2, s2) ← materializeVal p indent paramPrefix paramCount paramWidths tw2 s1
        let (q0, d0, s3) ← materializeVal p indent paramPrefix paramCount paramWidths dw0 s2
        let (q1, d1, s4) ← materializeVal p indent paramPrefix paramCount paramWidths dw1 s3
        let (q2, d2, s5) ← materializeVal p indent paramPrefix paramCount paramWidths dw2 s4
        let (pa, amt, s6) ← materializeVal p indent paramPrefix paramCount paramWidths amount s5
        let (tok, s7) := fresh s6
        let (ok, s8) := fresh s7
        let (rds, s9) := fresh s8
        st := s9
        acc := acc ++ p0 ++ p1 ++ p2 ++ q0 ++ q1 ++ q2 ++ pa ++
          indent ++ "if shr(32, " ++ a2 ++ ") { " ++ revert0 ++ " }" ++ nl ++
          indent ++ "if shr(32, " ++ d2 ++ ") { " ++ revert0 ++ " }" ++ nl ++
          indent ++ "mstore(0, 0)" ++ nl ++
          packAddrMstore8 indent a0 a1 a2 ++
          indent ++ "let " ++ tok ++ " := mload(0)" ++ nl ++
          indent ++ "mstore(0, 0xa9059cbb00000000000000000000000000000000000000000000000000000000)" ++ nl ++
          packAddrAt indent 16 d0 d1 d2 ++
          indent ++ "mstore(36, " ++ amt ++ ")" ++ nl ++
          indent ++ "let " ++ ok ++ " := call(gas(), " ++ tok ++ ", 0, 0, 68, 0, 32)" ++ nl ++
          indent ++ "if iszero(" ++ ok ++ ") { " ++ revert0 ++ " }" ++ nl ++
          indent ++ "let " ++ rds ++ " := returndatasize()" ++ nl ++
          indent ++ "if and(iszero(eq(" ++ rds ++ ", 0)), iszero(eq(" ++ rds ++
            ", 32))) { " ++ revert0 ++ " }" ++ nl ++
          indent ++ "if eq(" ++ rds ++ ", 32) { if iszero(mload(0)) { " ++ revert0 ++ " } }" ++ nl
        st := { st with last := some amt }
    | .evmTokenTransfer256 tw0 tw1 tw2 dw0 dw1 dw2 a0 a1 a2 a3 =>
        let (p0, t0, s0) ← materializeVal p indent paramPrefix paramCount paramWidths tw0 st
        let (p1, t1, s1) ← materializeVal p indent paramPrefix paramCount paramWidths tw1 s0
        let (p2, t2, s2) ← materializeVal p indent paramPrefix paramCount paramWidths tw2 s1
        let (q0, d0, s3) ← materializeVal p indent paramPrefix paramCount paramWidths dw0 s2
        let (q1, d1, s4) ← materializeVal p indent paramPrefix paramCount paramWidths dw1 s3
        let (q2, d2, s5) ← materializeVal p indent paramPrefix paramCount paramWidths dw2 s4
        let (r0, x0, s6) ← materializeVal p indent paramPrefix paramCount paramWidths a0 s5
        let (r1, x1, s7) ← materializeVal p indent paramPrefix paramCount paramWidths a1 s6
        let (r2, x2, s8) ← materializeVal p indent paramPrefix paramCount paramWidths a2 s7
        let (r3, x3, s9) ← materializeVal p indent paramPrefix paramCount paramWidths a3 s8
        let (tok, s10) := fresh s9
        let (amt, s11) := fresh s10
        let (ok, s12) := fresh s11
        let (rds, s13) := fresh s12
        st := s13
        acc := acc ++ p0 ++ p1 ++ p2 ++ q0 ++ q1 ++ q2 ++ r0 ++ r1 ++ r2 ++ r3 ++
          indent ++ "if shr(32, " ++ t2 ++ ") { " ++ revert0 ++ " }" ++ nl ++
          indent ++ "if shr(32, " ++ d2 ++ ") { " ++ revert0 ++ " }" ++ nl ++
          indent ++ "mstore(0, 0)" ++ nl ++
          packAddrMstore8 indent t0 t1 t2 ++
          indent ++ "let " ++ tok ++ " := mload(0)" ++ nl ++
          indent ++ "mstore(0, 0xa9059cbb00000000000000000000000000000000000000000000000000000000)" ++ nl ++
          packAddrAt indent 16 d0 d1 d2 ++
          indent ++ "let " ++ amt ++ " := " ++ packU256 x0 x1 x2 x3 ++ nl ++
          indent ++ "mstore(36, " ++ amt ++ ")" ++ nl ++
          indent ++ "let " ++ ok ++ " := call(gas(), " ++ tok ++ ", 0, 0, 68, 0, 32)" ++ nl ++
          indent ++ "if iszero(" ++ ok ++ ") { " ++ revert0 ++ " }" ++ nl ++
          indent ++ "let " ++ rds ++ " := returndatasize()" ++ nl ++
          indent ++ "if and(iszero(eq(" ++ rds ++ ", 0)), iszero(eq(" ++ rds ++
            ", 32))) { " ++ revert0 ++ " }" ++ nl ++
          indent ++ "if eq(" ++ rds ++ ", 32) { if iszero(mload(0)) { " ++ revert0 ++ " } }" ++ nl
        st := { st with last := some x0 }
    | .evmTokenApprove256 tw0 tw1 tw2 sw0 sw1 sw2 a0 a1 a2 a3 =>
        let (p0, t0, s0) ← materializeVal p indent paramPrefix paramCount paramWidths tw0 st
        let (p1, t1, s1) ← materializeVal p indent paramPrefix paramCount paramWidths tw1 s0
        let (p2, t2, s2) ← materializeVal p indent paramPrefix paramCount paramWidths tw2 s1
        let (q0, d0, s3) ← materializeVal p indent paramPrefix paramCount paramWidths sw0 s2
        let (q1, d1, s4) ← materializeVal p indent paramPrefix paramCount paramWidths sw1 s3
        let (q2, d2, s5) ← materializeVal p indent paramPrefix paramCount paramWidths sw2 s4
        let (r0, x0, s6) ← materializeVal p indent paramPrefix paramCount paramWidths a0 s5
        let (r1, x1, s7) ← materializeVal p indent paramPrefix paramCount paramWidths a1 s6
        let (r2, x2, s8) ← materializeVal p indent paramPrefix paramCount paramWidths a2 s7
        let (r3, x3, s9) ← materializeVal p indent paramPrefix paramCount paramWidths a3 s8
        let (tok, s10) := fresh s9
        let (amt, s11) := fresh s10
        let (ok, s12) := fresh s11
        let (rds, s13) := fresh s12
        st := s13
        acc := acc ++ p0 ++ p1 ++ p2 ++ q0 ++ q1 ++ q2 ++ r0 ++ r1 ++ r2 ++ r3 ++
          indent ++ "if shr(32, " ++ t2 ++ ") { " ++ revert0 ++ " }" ++ nl ++
          indent ++ "if shr(32, " ++ d2 ++ ") { " ++ revert0 ++ " }" ++ nl ++
          indent ++ "mstore(0, 0)" ++ nl ++
          packAddrMstore8 indent t0 t1 t2 ++
          indent ++ "let " ++ tok ++ " := mload(0)" ++ nl ++
          indent ++ "mstore(0, 0x095ea7b300000000000000000000000000000000000000000000000000000000)" ++ nl ++
          packAddrAt indent 16 d0 d1 d2 ++
          indent ++ "let " ++ amt ++ " := " ++ packU256 x0 x1 x2 x3 ++ nl ++
          indent ++ "mstore(36, " ++ amt ++ ")" ++ nl ++
          indent ++ "let " ++ ok ++ " := call(gas(), " ++ tok ++ ", 0, 0, 68, 0, 32)" ++ nl ++
          indent ++ "if iszero(" ++ ok ++ ") { " ++ revert0 ++ " }" ++ nl ++
          indent ++ "let " ++ rds ++ " := returndatasize()" ++ nl ++
          indent ++ "if and(iszero(eq(" ++ rds ++ ", 0)), iszero(eq(" ++ rds ++
            ", 32))) { " ++ revert0 ++ " }" ++ nl ++
          indent ++ "if eq(" ++ rds ++ ", 32) { if iszero(mload(0)) { " ++ revert0 ++ " } }" ++ nl
        st := { st with last := some x0 }
    | .evmTokenTransferFrom256 tw0 tw1 tw2 ow0 ow1 ow2 dw0 dw1 dw2 a0 a1 a2 a3 =>
        let (p0, t0, s0) ← materializeVal p indent paramPrefix paramCount paramWidths tw0 st
        let (p1, t1, s1) ← materializeVal p indent paramPrefix paramCount paramWidths tw1 s0
        let (p2, t2, s2) ← materializeVal p indent paramPrefix paramCount paramWidths tw2 s1
        let (q0, o0, s3) ← materializeVal p indent paramPrefix paramCount paramWidths ow0 s2
        let (q1, o1, s4) ← materializeVal p indent paramPrefix paramCount paramWidths ow1 s3
        let (q2, o2, s5) ← materializeVal p indent paramPrefix paramCount paramWidths ow2 s4
        let (r0, d0, s6) ← materializeVal p indent paramPrefix paramCount paramWidths dw0 s5
        let (r1, d1, s7) ← materializeVal p indent paramPrefix paramCount paramWidths dw1 s6
        let (r2, d2, s8) ← materializeVal p indent paramPrefix paramCount paramWidths dw2 s7
        let (u0, x0, s9) ← materializeVal p indent paramPrefix paramCount paramWidths a0 s8
        let (u1, x1, s10) ← materializeVal p indent paramPrefix paramCount paramWidths a1 s9
        let (u2, x2, s11) ← materializeVal p indent paramPrefix paramCount paramWidths a2 s10
        let (u3, x3, s12) ← materializeVal p indent paramPrefix paramCount paramWidths a3 s11
        let (tok, s13) := fresh s12
        let (amt, s14) := fresh s13
        let (ok, s15) := fresh s14
        let (rds, s16) := fresh s15
        st := s16
        acc := acc ++ p0 ++ p1 ++ p2 ++ q0 ++ q1 ++ q2 ++ r0 ++ r1 ++ r2 ++ u0 ++ u1 ++ u2 ++ u3 ++
          indent ++ "if shr(32, " ++ t2 ++ ") { " ++ revert0 ++ " }" ++ nl ++
          indent ++ "if shr(32, " ++ o2 ++ ") { " ++ revert0 ++ " }" ++ nl ++
          indent ++ "if shr(32, " ++ d2 ++ ") { " ++ revert0 ++ " }" ++ nl ++
          indent ++ "mstore(0, 0)" ++ nl ++
          packAddrMstore8 indent t0 t1 t2 ++
          indent ++ "let " ++ tok ++ " := mload(0)" ++ nl ++
          indent ++ "mstore(0, 0x23b872dd00000000000000000000000000000000000000000000000000000000)" ++ nl ++
          packAddrAt indent 16 o0 o1 o2 ++
          packAddrAt indent 48 d0 d1 d2 ++
          indent ++ "let " ++ amt ++ " := " ++ packU256 x0 x1 x2 x3 ++ nl ++
          indent ++ "mstore(68, " ++ amt ++ ")" ++ nl ++
          indent ++ "let " ++ ok ++ " := call(gas(), " ++ tok ++ ", 0, 0, 100, 0, 32)" ++ nl ++
          indent ++ "if iszero(" ++ ok ++ ") { " ++ revert0 ++ " }" ++ nl ++
          indent ++ "let " ++ rds ++ " := returndatasize()" ++ nl ++
          indent ++ "if and(iszero(eq(" ++ rds ++ ", 0)), iszero(eq(" ++ rds ++
            ", 32))) { " ++ revert0 ++ " }" ++ nl ++
          indent ++ "if eq(" ++ rds ++ ", 32) { if iszero(mload(0)) { " ++ revert0 ++ " } }" ++ nl
        st := { st with last := some x0 }
    | .evmTokenBalanceOfSelf tw0 tw1 tw2 =>
        let (p0, a0, s0) ← materializeVal p indent paramPrefix paramCount paramWidths tw0 st
        let (p1, a1, s1) ← materializeVal p indent paramPrefix paramCount paramWidths tw1 s0
        let (p2, a2, s2) ← materializeVal p indent paramPrefix paramCount paramWidths tw2 s1
        let (tok, s3) := fresh s2
        let (ok, s4) := fresh s3
        let (ret, s5) := fresh s4
        st := s5
        acc := acc ++ p0 ++ p1 ++ p2 ++
          indent ++ "if shr(32, " ++ a2 ++ ") { " ++ revert0 ++ " }" ++ nl ++
          indent ++ "mstore(0, 0)" ++ nl ++
          packAddrMstore8 indent a0 a1 a2 ++
          indent ++ "let " ++ tok ++ " := mload(0)" ++ nl ++
          indent ++ "mstore(0, 0x70a0823100000000000000000000000000000000000000000000000000000000)" ++ nl ++
          indent ++ "mstore(4, address())" ++ nl ++
          indent ++ "let " ++ ok ++ " := staticcall(gas(), " ++ tok ++ ", 0, 36, 0, 32)" ++ nl ++
          indent ++ "if iszero(" ++ ok ++ ") { " ++ revert0 ++ " }" ++ nl ++
          indent ++ "if iszero(eq(returndatasize(), 32)) { " ++ revert0 ++ " }" ++ nl ++
          indent ++ "let " ++ ret ++ " := mload(0)" ++ nl ++
          indent ++ "if shr(64, " ++ ret ++ ") { " ++ revert0 ++ " }" ++ nl
        st := { st with last := some ret }
    | .evmWethDeposit256 tw0 tw1 tw2 a0 a1 a2 a3 =>
        let (p0, t0, s0) ← materializeVal p indent paramPrefix paramCount paramWidths tw0 st
        let (p1, t1, s1) ← materializeVal p indent paramPrefix paramCount paramWidths tw1 s0
        let (p2, t2, s2) ← materializeVal p indent paramPrefix paramCount paramWidths tw2 s1
        let (r0, x0, s3) ← materializeVal p indent paramPrefix paramCount paramWidths a0 s2
        let (r1, x1, s4) ← materializeVal p indent paramPrefix paramCount paramWidths a1 s3
        let (r2, x2, s5) ← materializeVal p indent paramPrefix paramCount paramWidths a2 s4
        let (r3, x3, s6) ← materializeVal p indent paramPrefix paramCount paramWidths a3 s5
        let (tok, s7) := fresh s6
        let (amt, s8) := fresh s7
        let (ok, s9) := fresh s8
        st := s9
        acc := acc ++ p0 ++ p1 ++ p2 ++ r0 ++ r1 ++ r2 ++ r3 ++
          indent ++ "if shr(32, " ++ t2 ++ ") { " ++ revert0 ++ " }" ++ nl ++
          indent ++ "mstore(0, 0)" ++ nl ++
          packAddrMstore8 indent t0 t1 t2 ++
          indent ++ "let " ++ tok ++ " := mload(0)" ++ nl ++
          indent ++ "mstore(0, 0xd0e30db000000000000000000000000000000000000000000000000000000000)" ++ nl ++
          indent ++ "let " ++ amt ++ " := " ++ packU256 x0 x1 x2 x3 ++ nl ++
          indent ++ "let " ++ ok ++ " := call(gas(), " ++ tok ++ ", " ++ amt ++
            ", 0, 4, 0, 0)" ++ nl ++
          indent ++ "if iszero(" ++ ok ++ ") { " ++ revert0 ++ " }" ++ nl
        st := { st with last := some x0 }
    | .evmWethWithdraw256 tw0 tw1 tw2 a0 a1 a2 a3 =>
        let (p0, t0, s0) ← materializeVal p indent paramPrefix paramCount paramWidths tw0 st
        let (p1, t1, s1) ← materializeVal p indent paramPrefix paramCount paramWidths tw1 s0
        let (p2, t2, s2) ← materializeVal p indent paramPrefix paramCount paramWidths tw2 s1
        let (r0, x0, s3) ← materializeVal p indent paramPrefix paramCount paramWidths a0 s2
        let (r1, x1, s4) ← materializeVal p indent paramPrefix paramCount paramWidths a1 s3
        let (r2, x2, s5) ← materializeVal p indent paramPrefix paramCount paramWidths a2 s4
        let (r3, x3, s6) ← materializeVal p indent paramPrefix paramCount paramWidths a3 s5
        let (tok, s7) := fresh s6
        let (amt, s8) := fresh s7
        let (ok, s9) := fresh s8
        let (rds, s10) := fresh s9
        st := s10
        acc := acc ++ p0 ++ p1 ++ p2 ++ r0 ++ r1 ++ r2 ++ r3 ++
          indent ++ "if shr(32, " ++ t2 ++ ") { " ++ revert0 ++ " }" ++ nl ++
          indent ++ "mstore(0, 0)" ++ nl ++
          packAddrMstore8 indent t0 t1 t2 ++
          indent ++ "let " ++ tok ++ " := mload(0)" ++ nl ++
          indent ++ "mstore(0, 0x2e1a7d4d00000000000000000000000000000000000000000000000000000000)" ++ nl ++
          indent ++ "let " ++ amt ++ " := " ++ packU256 x0 x1 x2 x3 ++ nl ++
          indent ++ "mstore(4, " ++ amt ++ ")" ++ nl ++
          indent ++ "let " ++ ok ++ " := call(gas(), " ++ tok ++ ", 0, 0, 36, 0, 32)" ++ nl ++
          indent ++ "if iszero(" ++ ok ++ ") { " ++ revert0 ++ " }" ++ nl ++
          indent ++ "let " ++ rds ++ " := returndatasize()" ++ nl ++
          indent ++ "if and(iszero(eq(" ++ rds ++ ", 0)), iszero(eq(" ++ rds ++
            ", 32))) { " ++ revert0 ++ " }" ++ nl ++
          indent ++ "if eq(" ++ rds ++ ", 32) { if iszero(mload(0)) { " ++ revert0 ++ " } }" ++ nl
        st := { st with last := some x0 }
    | .evmSwapExact2 rw0 rw1 rw2 a0 a1 a2 b0 b1 b2 i0 i1 i2 i3 m0 m1 m2 m3 =>
        let (p0, t0, s0) ← materializeVal p indent paramPrefix paramCount paramWidths rw0 st
        let (p1, t1, s1) ← materializeVal p indent paramPrefix paramCount paramWidths rw1 s0
        let (p2, t2, s2) ← materializeVal p indent paramPrefix paramCount paramWidths rw2 s1
        let (q0, x0, s3) ← materializeVal p indent paramPrefix paramCount paramWidths a0 s2
        let (q1, x1, s4) ← materializeVal p indent paramPrefix paramCount paramWidths a1 s3
        let (q2, x2, s5) ← materializeVal p indent paramPrefix paramCount paramWidths a2 s4
        let (r0, y0, s6) ← materializeVal p indent paramPrefix paramCount paramWidths b0 s5
        let (r1, y1, s7) ← materializeVal p indent paramPrefix paramCount paramWidths b1 s6
        let (r2, y2, s8) ← materializeVal p indent paramPrefix paramCount paramWidths b2 s7
        let (u0, n0, s9) ← materializeVal p indent paramPrefix paramCount paramWidths i0 s8
        let (u1, n1, s10) ← materializeVal p indent paramPrefix paramCount paramWidths i1 s9
        let (u2, n2, s11) ← materializeVal p indent paramPrefix paramCount paramWidths i2 s10
        let (u3, n3, s12) ← materializeVal p indent paramPrefix paramCount paramWidths i3 s11
        let (v0, k0, s13) ← materializeVal p indent paramPrefix paramCount paramWidths m0 s12
        let (v1, k1, s14) ← materializeVal p indent paramPrefix paramCount paramWidths m1 s13
        let (v2, k2, s15) ← materializeVal p indent paramPrefix paramCount paramWidths m2 s14
        let (v3, k3, s16) ← materializeVal p indent paramPrefix paramCount paramWidths m3 s15
        let (tok, s17) := fresh s16
        let (amt, s18) := fresh s17
        let (minv, s19) := fresh s18
        let (ok, s20) := fresh s19
        st := s20
        acc := acc ++ p0 ++ p1 ++ p2 ++ q0 ++ q1 ++ q2 ++ r0 ++ r1 ++ r2 ++
          u0 ++ u1 ++ u2 ++ u3 ++ v0 ++ v1 ++ v2 ++ v3 ++
          indent ++ "if shr(32, " ++ t2 ++ ") { " ++ revert0 ++ " }" ++ nl ++
          indent ++ "if shr(32, " ++ x2 ++ ") { " ++ revert0 ++ " }" ++ nl ++
          indent ++ "if shr(32, " ++ y2 ++ ") { " ++ revert0 ++ " }" ++ nl ++
          indent ++ "mstore(0, 0)" ++ nl ++
          packAddrMstore8 indent t0 t1 t2 ++
          indent ++ "let " ++ tok ++ " := mload(0)" ++ nl ++
          indent ++ "mstore(0, 0x38ed173900000000000000000000000000000000000000000000000000000000)" ++ nl ++
          indent ++ "let " ++ amt ++ " := " ++ packU256 n0 n1 n2 n3 ++ nl ++
          indent ++ "mstore(4, " ++ amt ++ ")" ++ nl ++
          indent ++ "let " ++ minv ++ " := " ++ packU256 k0 k1 k2 k3 ++ nl ++
          indent ++ "mstore(36, " ++ minv ++ ")" ++ nl ++
          indent ++ "mstore(68, 160)" ++ nl ++
          indent ++ "mstore(100, address())" ++ nl ++
          indent ++ "mstore(132, not(0))" ++ nl ++
          indent ++ "mstore(164, 2)" ++ nl ++
          indent ++ "mstore(196, 0)" ++ nl ++
          packAddrAt indent 208 x0 x1 x2 ++
          indent ++ "mstore(228, 0)" ++ nl ++
          packAddrAt indent 240 y0 y1 y2 ++
          indent ++ "let " ++ ok ++ " := call(gas(), " ++ tok ++ ", 0, 0, 260, 0, 0)" ++ nl ++
          indent ++ "if iszero(" ++ ok ++ ") { " ++ revert0 ++ " }" ++ nl
        st := { st with last := some n0 }
    | .evmSwapExact3 rw0 rw1 rw2 a0 a1 a2 b0 b1 b2 c0 c1 c2 i0 i1 i2 i3 m0 m1 m2 m3 =>
        let (p0, t0, s0) ← materializeVal p indent paramPrefix paramCount paramWidths rw0 st
        let (p1, t1, s1) ← materializeVal p indent paramPrefix paramCount paramWidths rw1 s0
        let (p2, t2, s2) ← materializeVal p indent paramPrefix paramCount paramWidths rw2 s1
        let (q0, x0, s3) ← materializeVal p indent paramPrefix paramCount paramWidths a0 s2
        let (q1, x1, s4) ← materializeVal p indent paramPrefix paramCount paramWidths a1 s3
        let (q2, x2, s5) ← materializeVal p indent paramPrefix paramCount paramWidths a2 s4
        let (r0, y0, s6) ← materializeVal p indent paramPrefix paramCount paramWidths b0 s5
        let (r1, y1, s7) ← materializeVal p indent paramPrefix paramCount paramWidths b1 s6
        let (r2, y2, s8) ← materializeVal p indent paramPrefix paramCount paramWidths b2 s7
        let (sA0, z0, s9) ← materializeVal p indent paramPrefix paramCount paramWidths c0 s8
        let (sA1, z1, s10) ← materializeVal p indent paramPrefix paramCount paramWidths c1 s9
        let (sA2, z2, s11) ← materializeVal p indent paramPrefix paramCount paramWidths c2 s10
        let (u0, n0, s12) ← materializeVal p indent paramPrefix paramCount paramWidths i0 s11
        let (u1, n1, s13) ← materializeVal p indent paramPrefix paramCount paramWidths i1 s12
        let (u2, n2, s14) ← materializeVal p indent paramPrefix paramCount paramWidths i2 s13
        let (u3, n3, s15) ← materializeVal p indent paramPrefix paramCount paramWidths i3 s14
        let (v0, k0, s16) ← materializeVal p indent paramPrefix paramCount paramWidths m0 s15
        let (v1, k1, s17) ← materializeVal p indent paramPrefix paramCount paramWidths m1 s16
        let (v2, k2, s18) ← materializeVal p indent paramPrefix paramCount paramWidths m2 s17
        let (v3, k3, s19) ← materializeVal p indent paramPrefix paramCount paramWidths m3 s18
        let (tok, s20) := fresh s19
        let (amt, s21) := fresh s20
        let (minv, s22) := fresh s21
        let (ok, s23) := fresh s22
        st := s23
        acc := acc ++ p0 ++ p1 ++ p2 ++ q0 ++ q1 ++ q2 ++ r0 ++ r1 ++ r2 ++
          sA0 ++ sA1 ++ sA2 ++ u0 ++ u1 ++ u2 ++ u3 ++ v0 ++ v1 ++ v2 ++ v3 ++
          indent ++ "if shr(32, " ++ t2 ++ ") { " ++ revert0 ++ " }" ++ nl ++
          indent ++ "if shr(32, " ++ x2 ++ ") { " ++ revert0 ++ " }" ++ nl ++
          indent ++ "if shr(32, " ++ y2 ++ ") { " ++ revert0 ++ " }" ++ nl ++
          indent ++ "if shr(32, " ++ z2 ++ ") { " ++ revert0 ++ " }" ++ nl ++
          indent ++ "mstore(0, 0)" ++ nl ++
          packAddrMstore8 indent t0 t1 t2 ++
          indent ++ "let " ++ tok ++ " := mload(0)" ++ nl ++
          indent ++ "mstore(0, 0x38ed173900000000000000000000000000000000000000000000000000000000)" ++ nl ++
          indent ++ "let " ++ amt ++ " := " ++ packU256 n0 n1 n2 n3 ++ nl ++
          indent ++ "mstore(4, " ++ amt ++ ")" ++ nl ++
          indent ++ "let " ++ minv ++ " := " ++ packU256 k0 k1 k2 k3 ++ nl ++
          indent ++ "mstore(36, " ++ minv ++ ")" ++ nl ++
          indent ++ "mstore(68, 160)" ++ nl ++
          indent ++ "mstore(100, address())" ++ nl ++
          indent ++ "mstore(132, not(0))" ++ nl ++
          indent ++ "mstore(164, 3)" ++ nl ++
          indent ++ "mstore(196, 0)" ++ nl ++
          packAddrAt indent 208 x0 x1 x2 ++
          indent ++ "mstore(228, 0)" ++ nl ++
          packAddrAt indent 240 y0 y1 y2 ++
          indent ++ "mstore(260, 0)" ++ nl ++
          packAddrAt indent 272 z0 z1 z2 ++
          indent ++ "let " ++ ok ++ " := call(gas(), " ++ tok ++ ", 0, 0, 292, 0, 0)" ++ nl ++
          indent ++ "if iszero(" ++ ok ++ ") { " ++ revert0 ++ " }" ++ nl
        st := { st with last := some n0 }
    | .evmPermit o0 o1 o2 sA0 sA1 sA2 v0 v1 v2 v3 d0 d1 d2 d3 vv r0 r1 r2 r3 z0 z1 z2 z3 =>
        let (txt, st') ← emitPermit p indent paramPrefix paramCount paramWidths
          o0 o1 o2 sA0 sA1 sA2 v0 v1 v2 v3 d0 d1 d2 d3 vv r0 r1 r2 r3 z0 z1 z2 z3 st
        acc := acc ++ txt
        st := st'
    | .evmTokenPermit tw0 tw1 tw2 ow0 ow1 ow2 sw0 sw1 sw2 v0 v1 v2 v3 d0 d1 d2 d3 vv r0 r1 r2 r3 z0 z1 z2 z3 =>
        let (txt, st') ← emitTokenPermit p indent paramPrefix paramCount paramWidths
          tw0 tw1 tw2 ow0 ow1 ow2 sw0 sw1 sw2 v0 v1 v2 v3 d0 d1 d2 d3 vv r0 r1 r2 r3 z0 z1 z2 z3 st
        acc := acc ++ txt
        st := st'
    | .storeField name v =>
        let destS ← slotOf p name
        let (pre, value, st') ← materializeVal p indent paramPrefix paramCount paramWidths v st
        st := st'
        let w := (IR.slotWidth p name).getD 8
        acc := acc ++ pre ++ storeSlot indent destS (maskExpr w value)
        st := { st with last := some value }
    | .okState v =>
        if IR.hasStoreField ops then
          let (pre, value, st') ←
            match st.last with
            | some nm => pure ("", nm, { st with last := none })
            | none => materializeVal p indent paramPrefix paramCount paramWidths v st
          st := st'
          acc := acc ++ pre ++ returnWord indent value
        else if IR.hasIndexSet ops then
          let value := st.last.getD "0"
          acc := acc ++ returnWord indent value
        else if IR.hasOptionLeaves p then
          let (tagN, payN) := (IR.optionLeafNames? p).getD ("slot_tag", "slot_p0")
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
              let (pre, payload, st') ← materializeVal p indent paramPrefix paramCount paramWidths v st
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
                      loadVal p paramPrefix paramCount paramWidths (.arg 0)
                    else if IR.hasCheckedArith ops then
                      loadVal p paramPrefix paramCount paramWidths v
                    else
                      loadVal p paramPrefix paramCount paramWidths (.arg 0)
                | _ =>
                    let (pre, e, st') ← materializeVal p indent paramPrefix paramCount paramWidths v st
                    st := st'
                    acc := acc ++ pre
                    pure e
          let w := (IR.slotWidth p destName).getD 8
          acc := acc ++ storeSlot indent destS (maskExpr w value) ++ returnWord indent value
        st := { st with last := none }
    | .errorOverflow =>
        -- 抽出序列在 checked 算术后仍带 overflow 叶；Yul 已在运算前 revert。
        unless IR.hasCheckedArith ops do
          acc := acc ++ indent ++ revert0 ++ nl
    | .errorNamed name =>
        acc := acc ++ revertNamed indent name
    | .returnU64 v =>
        let (pre, value, st') ←
          match st.last with
          | some nm => pure ("", nm, { st with last := none })
          | none => materializeVal p indent paramPrefix paramCount paramWidths v st
        st := st'
        acc := acc ++ pre
        if nRets > 1 then
          acc := acc ++ indent ++ "mstore(" ++ toString (returnU64Idx * 32) ++ ", " ++
            value ++ ")" ++ nl
          if returnU64Idx + 1 == nRets then
            acc := acc ++ indent ++ "return(0, " ++ toString (nRets * 32) ++ ")" ++ nl
          returnU64Idx := returnU64Idx + 1
        else
          acc := acc ++ returnWord indent value
    | .returnState v =>
        let (pre, value, st') ← materializeVal p indent paramPrefix paramCount paramWidths v st
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

private inductive CFGResultHint where
  | plain
  | checked (destination : String)
  | effect
  | stored
  | conflict
  deriving BEq, Inhabited

private def cfgHintHasLast : CFGResultHint → Bool
  | .checked _ | .effect => true
  | .plain | .stored | .conflict => false

private def mergeCFGHint (old next : CFGResultHint) : CFGResultHint :=
  if old == next then old else .conflict

private def updateCFGHint (hints : Array (Core.CFG.BlockId × CFGResultHint))
    (id : Core.CFG.BlockId) (next : CFGResultHint) :
    Array (Core.CFG.BlockId × CFGResultHint) × Bool :=
  match hints.findIdx? (·.1 == id) with
  | none => (hints.push (id, next), true)
  | some index =>
      let old := hints[index]!.2
      let merged := mergeCFGHint old next
      if merged == old then (hints, false)
      else (hints.set! index (id, merged), true)

private def cfgHintAfterInstructions (instructions : Array Ops.Op)
    (incoming : CFGResultHint) : CFGResultHint :=
  instructions.foldl (init := incoming) fun hint instruction =>
    match instruction with
    | .storeField .. | .indexSet .. | .indexSetLeaf .. => .stored
    | .ext _ => .effect
    | _ => hint

private def cfgInstructionProducesEffectResult : Ops.Op → Bool
  | .ext _ => true
  | _ => false

private def checkedDestination (p : IR.Program) (lhs : Ops.Val) : String :=
  match lhs with
  | .field _ name => name
  | _ => (p.slots[0]?.map (·.name)).getD "slot0"

private def cfgResultHints (p : IR.Program)
    (graph : Core.CFG.Graph Ops.ValKind Ops.OpExt) :
    Array (Core.CFG.BlockId × CFGResultHint) := Id.run do
  let mut hints : Array (Core.CFG.BlockId × CFGResultHint) := #[(graph.entry, .plain)]
  let fuel := graph.blocks.size * 4 + 1
  for _ in [0:fuel] do
    let mut changed := false
    for block in graph.blocks do
      match hints.find? (·.1 == block.id) with
      | none => pure ()
      | some entry =>
          let outgoing := cfgHintAfterInstructions block.instructions entry.2
          let mut flows : Array (Core.CFG.Edge Ops.ValKind × CFGResultHint) := #[]
          match block.terminator with
          | .jump next => flows := #[(next, outgoing)]
          | .branch _ _ _ thenEdge elseEdge =>
              flows := #[(thenEdge, outgoing), (elseEdge, outgoing)]
          | .checked operation success overflow =>
              let successHint := match operation with
                | .addU64 lhs _ | .subU64 lhs _ | .mulU64 lhs _
                | .divU64 lhs _ | .modU64 lhs _ => .checked (checkedDestination p lhs)
                | .forAccum .. => outgoing
              flows := #[(success, successHint), (overflow, .plain)]
          | .exit _ | .unreachable => pure ()
          for flow in flows do
            let (nextHints, didChange) := updateCFGHint hints flow.1.target flow.2
            hints := nextHints
            changed := changed || didChange
    unless changed do break
  return hints

private def cfgDefinedLocals (graph : Core.CFG.Graph Ops.ValKind Ops.OpExt) : Array Nat :=
  let ids := graph.blocks.flatMap fun block =>
    block.params ++ block.instructions.filterMap (fun
      | .letLocal id _ | .joinLocal id | .setLocal id _ => some id
      | _ => none) ++ match block.terminator with
        | .checked (.forAccum _ _ resultLocal) _ _ => #[resultLocal]
        | _ => #[]
  ids.toList.eraseDups.toArray

private def emitCFGOkState (p : IR.Program) (indent paramPrefix : String)
    (paramCount : Nat) (paramWidths : Array Nat) (value : Ops.Val) (last : Option String)
    (hint : CFGResultHint) (st : Render) : Except String (String × Render) := do
  let mut body := ""
  let mut st := st
  if hint == .stored then
    let (pre, result, next) ← materializeVal p indent paramPrefix paramCount paramWidths value st
    st := next
    body := body ++ pre ++ returnWord indent result
  else if hint == .conflict then
    match value with
    | .field _ _ =>
        let (pre, result, next) ← materializeVal p indent paramPrefix paramCount paramWidths value st
        st := next
        body := body ++ pre ++ returnWord indent result
    | _ => throw "evm/cfg: ambiguous implicit result at state exit"
  else if IR.hasOptionLeaves p then
    let (tagName, payloadName) := (IR.optionLeafNames? p).getD ("slot_tag", "slot_p0")
    match value with
    | .lit 0 =>
        body := body ++ (← storeNamed p indent tagName "0")
        body := body ++ (← storeNamed p indent payloadName "0")
        body := body ++ returnWord indent "0"
    | .lit literal =>
        body := body ++ (← storeNamed p indent tagName "1")
        body := body ++ (← storeNamed p indent payloadName (yulLit literal))
        body := body ++ returnWord indent (yulLit literal)
    | _ =>
        let (pre, payload, next) ← materializeVal p indent paramPrefix paramCount paramWidths value st
        st := next
        body := body ++ pre ++ (← storeNamed p indent tagName "1")
        body := body ++ (← storeNamed p indent payloadName payload)
        body := body ++ returnWord indent payload
  else
    let destination := match hint with
      | .checked name => name
      | _ => destForOk p #[] value
    let slot ← slotOf p destination
    let result ← match last with
      | some expression => pure expression
      | none =>
          if cfgHintHasLast hint then pure "pf_last"
          else match value with
            | .field _ _ => loadVal p paramPrefix paramCount paramWidths (.arg 0)
            | _ =>
                let (pre, expression, next) ←
                  materializeVal p indent paramPrefix paramCount paramWidths value st
                st := next
                body := body ++ pre
                pure expression
    let width := (IR.slotWidth p destination).getD 8
    body := body ++ storeSlot indent slot (maskExpr width result) ++ returnWord indent result
  return (body, st)

private def emitCFGChecked (p : IR.Program) (indent paramPrefix : String)
    (paramCount : Nat) (paramWidths : Array Nat) (operation : Core.CFG.Checked Ops.ValKind)
    (success overflow : Nat) (st : Render) : Except String (String × Render) := do
  match operation with
  | .addU64 lhs rhs | .subU64 lhs rhs | .mulU64 lhs rhs
  | .divU64 lhs rhs | .modU64 lhs rhs =>
      let (preL, left, st1) ← materializeVal p indent paramPrefix paramCount paramWidths lhs st
      let (preR, right, st2) ← materializeVal p indent paramPrefix paramCount paramWidths rhs st1
      let (resultName, st3) := fresh st2
      let (failedName, st4) := fresh st3
      let (result, failed) := match operation with
        | .addU64 .. => ("add(" ++ left ++ ", " ++ right ++ ")",
            "gt(" ++ left ++ ", sub(" ++ u64MaxYul ++ ", " ++ right ++ "))")
        | .subU64 .. => ("sub(" ++ left ++ ", " ++ right ++ ")",
            "lt(" ++ left ++ ", " ++ right ++ ")")
        | .mulU64 .. => ("mul(" ++ left ++ ", " ++ right ++ ")",
            "gt(" ++ resultName ++ ", " ++ u64MaxYul ++ ")")
        | .divU64 .. => ("div(" ++ left ++ ", " ++ right ++ ")", "iszero(" ++ right ++ ")")
        | .modU64 .. => ("mod(" ++ left ++ ", " ++ right ++ ")", "iszero(" ++ right ++ ")")
        | .forAccum .. => ("0", "1")
      let text := preL ++ preR ++
        indent ++ "let " ++ resultName ++ " := " ++ result ++ nl ++
        indent ++ "let " ++ failedName ++ " := " ++ failed ++ nl ++
        indent ++ "if " ++ failedName ++ " { pf_pc := " ++ toString overflow ++ " }" ++ nl ++
        indent ++ "if iszero(" ++ failedName ++ ") {" ++ nl ++
        indent ++ "  pf_last := " ++ resultName ++ nl ++
        indent ++ "  pf_pc := " ++ toString success ++ nl ++
        indent ++ "}" ++ nl
      return (text, { st4 with last := some "pf_last" })
  | .forAccum bound addend resultLocal =>
      let (loopName, st1) := fresh st
      let (failedName, st2) := fresh st1
      let inner := { st2 with loopIx := some loopName }
      let (pre, addendExpr, st3) ←
        materializeVal p (indent ++ "  ") paramPrefix paramCount paramWidths addend inner
      let accumulator := s!"l{resultLocal}"
      let text :=
        indent ++ accumulator ++ " := 0" ++ nl ++
        indent ++ "let " ++ failedName ++ " := 0" ++ nl ++
        indent ++ "for { let " ++ loopName ++ " := 0 } and(lt(" ++ loopName ++ ", " ++
          toString bound ++ "), iszero(" ++ failedName ++ ")) { " ++ loopName ++
          " := add(" ++ loopName ++ ", 1) } {" ++ nl ++ pre ++
        indent ++ "  if gt(" ++ accumulator ++ ", sub(" ++ u64MaxYul ++ ", " ++
          addendExpr ++ ")) { " ++ failedName ++ " := 1 }" ++ nl ++
        indent ++ "  if iszero(" ++ failedName ++ ") { " ++ accumulator ++ " := add(" ++
          accumulator ++ ", " ++ addendExpr ++ ") }" ++ nl ++
        indent ++ "}" ++ nl ++
        indent ++ "if " ++ failedName ++ " { pf_pc := " ++ toString overflow ++ " }" ++ nl ++
        indent ++ "if iszero(" ++ failedName ++ ") {" ++ nl ++
        indent ++ "  pf_last := " ++ accumulator ++ nl ++
        indent ++ "  pf_pc := " ++ toString success ++ nl ++
        indent ++ "}" ++ nl
      return (text, { st3 with last := some "pf_last", loopIx := none })

private def emitCFGCase (p : IR.Program) (method : IR.Method)
    (hints : Array (Core.CFG.BlockId × CFGResultHint))
    (block : Core.CFG.Block Ops.ValKind Ops.OpExt) (st : Render) :
    Except String (String × Render) := do
  unless block.params.isEmpty do
    throw s!"evm/cfg: block parameters are not lowered in block {block.id}"
  let indent := "            "
  let incoming := (hints.find? (·.1 == block.id)).map (·.2) |>.getD .plain
  let initialLast := if cfgHintHasLast incoming then some "pf_last" else none
  let blockState := { st with
    last := initialLast
    loopIx := none
    predeclaredLocals := true
  }
  let mut instructionText := ""
  let mut afterInstructions := blockState
  for sourceInstruction in block.instructions do
    let instruction ← IR.ofSourceOps #[sourceInstruction]
    let (text, next) ←
      emitOps p indent "arg" method.paramCount method.paramWidths instruction afterInstructions
    instructionText := instructionText ++ text
    if cfgInstructionProducesEffectResult sourceInstruction then
      let some expression := next.last
        | throw s!"evm/cfg: effect instruction in block {block.id} produced no result"
      instructionText := instructionText ++ indent ++ "pf_last := " ++ expression ++ nl
    afterInstructions := { next with last := none }
  let afterHint := cfgHintAfterInstructions block.instructions incoming
  let mut body := instructionText
  let mut finalState := { afterInstructions with last := none, loopIx := none }
  match block.terminator with
  | .jump next =>
      unless next.args.isEmpty do throw s!"evm/cfg: edge arguments remain at block {block.id}"
      body := body ++ indent ++ "pf_pc := " ++ toString next.target ++ nl
  | .branch cmp lhs rhs thenEdge elseEdge =>
      unless thenEdge.args.isEmpty && elseEdge.args.isEmpty do
        throw s!"evm/cfg: branch arguments remain at block {block.id}"
      let (preL, left, st1) ←
        materializeVal p indent "arg" method.paramCount method.paramWidths lhs finalState
      let (preR, right, st2) ←
        materializeVal p indent "arg" method.paramCount method.paramWidths rhs st1
      let (condition, st3) := fresh st2
      finalState := st3
      body := body ++ preL ++ preR ++ indent ++ "let " ++ condition ++ " := " ++
        cmpYul cmp left right ++ nl ++
        indent ++ "if " ++ condition ++ " { pf_pc := " ++ toString thenEdge.target ++ " }" ++ nl ++
        indent ++ "if iszero(" ++ condition ++ ") { pf_pc := " ++
          toString elseEdge.target ++ " }" ++ nl
  | .checked operation success overflow =>
      unless success.args.isEmpty && overflow.args.isEmpty do
        throw s!"evm/cfg: checked arguments remain at block {block.id}"
      let (checkedText, next) ← emitCFGChecked p indent "arg" method.paramCount method.paramWidths
        operation success.target overflow.target finalState
      body := body ++ checkedText
      finalState := { next with last := none }
  | .exit result =>
      match result with
      | .initialize _ => throw "evm/cfg: initializer reached runtime entry"
      | .okState value =>
          let (exitText, next) ← emitCFGOkState p indent "arg" method.paramCount method.paramWidths
            value none afterHint finalState
          body := body ++ exitText
          finalState := next
      | .errorOverflow => body := body ++ indent ++ revert0 ++ nl
      | .errorNamed name => body := body ++ revertNamed indent name
      | .returnU64 value =>
          let (pre, expression, next) ←
            if cfgHintHasLast afterHint then pure ("", "pf_last", finalState)
            else materializeVal p indent "arg" method.paramCount method.paramWidths value finalState
          body := body ++ pre ++ returnWord indent expression
          finalState := next
      | .returnU64s values =>
          if values.isEmpty then throw "evm/cfg: empty return tuple"
          if (method.retWidths == #[32] || method.retWidths == #[33]) && values.size == 4 then
            let (p0, a0, s0) ←
              materializeVal p indent "arg" method.paramCount method.paramWidths values[0]! finalState
            let (p1, a1, s1) ←
              materializeVal p indent "arg" method.paramCount method.paramWidths values[1]! s0
            let (p2, a2, s2) ←
              materializeVal p indent "arg" method.paramCount method.paramWidths values[2]! s1
            let (p3, a3, s3) ←
              materializeVal p indent "arg" method.paramCount method.paramWidths values[3]! s2
            finalState := s3
            body := body ++ p0 ++ p1 ++ p2 ++ p3 ++
              indent ++ "mstore(0, " ++ packU256 a0 a1 a2 a3 ++ ")" ++ nl ++
              indent ++ "return(0, 32)" ++ nl
          else if method.retWidths == #[20] && values.size == 3 then
            let (p0, a0, s0) ←
              materializeVal p indent "arg" method.paramCount method.paramWidths values[0]! finalState
            let (p1, a1, s1) ←
              materializeVal p indent "arg" method.paramCount method.paramWidths values[1]! s0
            let (p2, a2, s2) ←
              materializeVal p indent "arg" method.paramCount method.paramWidths values[2]! s1
            finalState := s2
            body := body ++ p0 ++ p1 ++ p2 ++
              indent ++ "mstore(0, 0)" ++ nl ++
              packAddrMstore8 indent a0 a1 a2 ++
              indent ++ "return(0, 32)" ++ nl
          else
            for i in [0:values.size] do
              let (pre, expression, next) ←
                materializeVal p indent "arg" method.paramCount method.paramWidths values[i]! finalState
              finalState := next
              body := body ++ pre ++ indent ++ "mstore(" ++ toString (i * 32) ++ ", " ++
                expression ++ ")" ++ nl
            body := body ++ indent ++ "return(0, " ++ toString (values.size * 32) ++ ")" ++ nl
      | .returnState value =>
          let (pre, expression, next) ←
            materializeVal p indent "arg" method.paramCount method.paramWidths value finalState
          finalState := next
          let destination := (p.slots[0]?.map (·.name)).getD "slot0"
          let slot ← slotOf p destination
          let width := (IR.slotWidth p destination).getD 8
          body := body ++ pre ++ storeSlot indent slot (maskExpr width expression) ++
            returnWord indent expression
  | .unreachable => throw s!"evm/cfg: reachable block {block.id} is incomplete"
  return ("          case " ++ toString block.id ++ " {" ++ nl ++ body ++
    "          }" ++ nl, finalState)

private def emitCFGEntry (p : IR.Program) (method : IR.Method) : Except String String := do
  let graph ← method.toCFG
  let hints := cfgResultHints p graph
  let locals := cfgDefinedLocals graph
  let mut declarations := ""
  for id in locals do
    declarations := declarations ++ "        let l" ++ toString id ++ " := 0" ++ nl
  declarations := declarations ++
    "        let pf_last := 0" ++ nl ++
    "        let pf_pc := " ++ toString graph.entry ++ nl
  let mut cases := ""
  let mut state : Render := { predeclaredLocals := true }
  for block in graph.blocks do
    let (text, next) ← emitCFGCase p method hints block { state with wide := #[] }
    cases := cases ++ text
    state := { next with wide := #[] }
  return declarations ++
    "        for { } 1 { } {" ++ nl ++
    "          switch pf_pc" ++ nl ++ cases ++
    "          default { " ++ revert0 ++ " }" ++ nl ++
    "        }" ++ nl

private def q (s : String) : String :=
  "\"" ++ s ++ "\""

private def emitConstructorStores (p : IR.Program) : Except String String := do
  let graph ← p.constructor.toCFG
  unless graph.blocks.all (·.instructions.isEmpty) do
    throw "extract/unsupported: EVM constructor effects are not lowered"
  let exits := graph.blocks.filterMap fun block => match block.terminator with
    | .exit (.initialize values) => some values
    | _ => none
  unless exits.size == 1 do
    throw "evm/cfg: constructor requires exactly one initialize exit"
  let vs := exits[0]!
  if vs.isEmpty then
    throw "extract/unsupported: init missing returnState"
  if !p.schema.isEmpty && vs.size != p.slots.size then
    throw (s!"extract/unsupported: init initializes {vs.size} state leaves, " ++
      s!"schema requires {p.slots.size}")
  let mut body := ""
  let mut i : Nat := 0
  for s in p.slots do
    if h : i < vs.size then
      let v ← loadVal p "ctor_arg" p.constructor.paramCount p.constructor.paramWidths vs[i]
      unless v == "0" do
        body := body ++ storeSlot "    " s.index (maskExpr s.width v)
    i := i + 1
  return body

private def renderCtorPrelude (objectName : String) (paramCount : Nat)
    (paramWidths : Array Nat) : String :=
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
      let w := (paramWidths[i]?).getD 8
      let max := widthMask w
      out := out ++
        "    let ctor_arg" ++ toString i ++ " := mload(" ++ toString (i * 32) ++ ")" ++ nl
      unless w == 32 || w == 33 do
        out := out ++
          "    if gt(ctor_arg" ++ toString i ++ ", " ++ max ++ ") { " ++
            revert0 ++ " }" ++ nl
    return out

/-- Bake constructor arguments that are not stored: up to two `uint64`
(`imm0`/`imm1`) and two `address` (`immAddr`/`immAddr2`) values.
`setimmutable(offset, name, value)` patches runtime already copied to memory at `offset`. -/
private def renderImmutableSets (paramCount : Nat) (paramWidths : Array Nat) : String :=
  Id.run do
    let mut out := ""
    let mut usedU64 : Nat := 0
    let mut usedAddr : Nat := 0
    for i in [0:paramCount] do
      let w := (paramWidths[i]?).getD 8
      let nm := "ctor_arg" ++ toString i
      if w == 20 && usedAddr < 2 then
        let name := if usedAddr == 0 then "immAddr" else "immAddr2"
        out := out ++ "    setimmutable(0, \"" ++ name ++ "\", " ++ nm ++ ")" ++ nl
        usedAddr := usedAddr + 1
      else if (w == 8 || w == 1 || w == 2 || w == 4) && usedU64 < 2 then
        let name := if usedU64 == 0 then "imm0" else "imm1"
        out := out ++ "    setimmutable(0, \"" ++ name ++ "\", " ++ nm ++ ")" ++ nl
        usedU64 := usedU64 + 1
    return out

private def hasPayableEntry (p : IR.Program) : Bool :=
  p.entries.any (·.payable)

private def renderReceive (p : IR.Program) (m : IR.Method) : Except String String := do
  if !IR.hasEvmReceive m.ops then
    throw s!"extract/unsupported: receive missing evmReceive in {m.ixName}"
  match emitCFGEntry p m with
  | .error reason => throw s!"{reason} in {m.ixName}"
  | .ok "" => throw s!"extract/unsupported: empty ops {m.ixName}"
  | .ok body =>
      pure ("      if iszero(calldatasize()) {" ++ nl ++ body ++ "      }" ++ nl)

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
    let w := (m.paramWidths[i]?).getD 8
    let max := widthMask w
    head := head ++
      "        let arg" ++ toString i ++ " := calldataload(" ++ toString off ++ ")" ++ nl
    unless w == 32 || w == 33 do
      head := head ++
        "        if gt(arg" ++ toString i ++ ", " ++ max ++ ") { " ++
          revert0 ++ " }" ++ nl
  let body ← match emitCFGEntry p m with
    | .ok body => pure body
    | .error reason => throw s!"{reason} in {m.ixName}"
  if body == "" then
    throw s!"extract/unsupported: empty ops {m.ixName}"
  return head ++ body ++ "      }" ++ nl

def emitYul (p : IR.Program) : Except String String := do
  if p.entries.isEmpty then
    throw "extract/unsupported: evm wants at least one entry"
  let runtimeName := p.name ++ "_runtime"
  let ctorHead := renderCtorPrelude p.name p.constructor.paramCount p.constructor.paramWidths
  let ctorStores ← emitConstructorStores p
  let ctorImm :=
    if IR.programHasImmutable p then
      renderImmutableSets p.constructor.paramCount p.constructor.paramWidths
    else ""
  let anyPay := hasPayableEntry p
  let mut receiveTxt := ""
  let mut entries := ""
  for m in p.entries do
    if m.ixName == "receive" then
      receiveTxt := receiveTxt ++ (← renderReceive p m)
    else
      entries := entries ++ (← renderEntry p m anyPay)
  let globalGuard :=
    if anyPay then ""
    else "      if callvalue() { " ++ revert0 ++ " }" ++ nl
  let yul :=
    "// PROOF-FORGE-EVM-YUL v0" ++ nl ++
    "// digest=" ++ IR.digestHex p ++ nl ++
    "object " ++ q p.name ++ " {" ++ nl ++
    "  code {" ++ nl ++
    ctorHead ++ ctorStores ++
    "    datacopy(0, dataoffset(" ++ q runtimeName ++ "), datasize(" ++ q runtimeName ++ "))" ++ nl ++
    ctorImm ++
    "    return(0, datasize(" ++ q runtimeName ++ "))" ++ nl ++
    "  }" ++ nl ++
    "  object " ++ q runtimeName ++ " {" ++ nl ++
    "    code {" ++ nl ++
    renderAddr20Helper ++
    globalGuard ++
    receiveTxt ++
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

private def paramJsonAt (i width : Nat) : String :=
  "{\"name\":\"arg" ++ toString i ++ "\",\"type\":\"" ++
    Keccak.abiTypeOfWidth width ++ "\"}"

private def paramsJsonOf (widths : Array Nat) (fallback : Nat) : String :=
  let ws := if widths.size == fallback then widths else Array.replicate fallback 8
  String.intercalate "," ((List.range fallback).map fun i =>
    paramJsonAt i ((ws[i]?).getD 8))

private def ctorAbi (p : IR.Program) : String :=
  "{\"type\":\"constructor\",\"stateMutability\":\"nonpayable\",\"inputs\":[" ++
    paramsJsonOf p.constructor.paramWidths p.constructor.paramCount ++ "]}"

private def outputsJson (m : IR.Method) : String :=
  if m.retWidths == #[20] then
    "[{\"name\":\"\",\"type\":\"address\"}]"
  else if m.retWidths == #[32] then
    "[{\"name\":\"\",\"type\":\"uint256\"}]"
  else if m.retWidths == #[33] then
    "[{\"name\":\"\",\"type\":\"bytes32\"}]"
  else if m.retWidths == #[1] then
    "[{\"name\":\"\",\"type\":\"uint8\"}]"
  else if m.retWidths == #[2] then
    "[{\"name\":\"\",\"type\":\"uint16\"}]"
  else if m.retWidths == #[4] then
    "[{\"name\":\"\",\"type\":\"uint32\"}]"
  else if m.retCount ≤ 1 then
    "[{\"name\":\"\",\"type\":\"uint64\"}]"
  else
    "[" ++ String.intercalate "," ((List.range m.retCount).map fun _ =>
      "{\"name\":\"\",\"type\":\"uint64\"}") ++ "]"

private def entryAbi (m : IR.Method) : String :=
  let mutab := if m.view then "view" else if m.payable then "payable" else "nonpayable"
  "{\"type\":\"function\",\"name\":\"" ++ escapeJson m.ixName ++
    "\",\"stateMutability\":\"" ++ mutab ++ "\",\"inputs\":[" ++
    paramsJsonOf m.paramWidths m.paramCount ++
    "],\"outputs\":" ++ outputsJson m ++ "}"

private def eventAbi (name : String) : String :=
  if name == "Transfer256" then
    "{\"type\":\"event\",\"name\":\"Transfer\",\"inputs\":[" ++
      "{\"name\":\"from\",\"type\":\"address\",\"indexed\":true}," ++
      "{\"name\":\"to\",\"type\":\"address\",\"indexed\":true}," ++
      "{\"name\":\"value\",\"type\":\"uint256\",\"indexed\":false}],\"anonymous\":false}"
  else if name == "Approval256" then
    "{\"type\":\"event\",\"name\":\"Approval\",\"inputs\":[" ++
      "{\"name\":\"owner\",\"type\":\"address\",\"indexed\":true}," ++
      "{\"name\":\"spender\",\"type\":\"address\",\"indexed\":true}," ++
      "{\"name\":\"value\",\"type\":\"uint256\",\"indexed\":false}],\"anonymous\":false}"
  else
    "{\"type\":\"event\",\"name\":\"" ++ escapeJson name ++
      "\",\"inputs\":[{\"name\":\"amt\",\"type\":\"uint64\",\"indexed\":false}],\"anonymous\":false}"

private def errorAbiInsufficient : String :=
  "{\"type\":\"error\",\"name\":\"Insufficient\",\"inputs\":[" ++
    "{\"name\":\"have\",\"type\":\"uint256\"}," ++
    "{\"name\":\"want\",\"type\":\"uint256\"}]}"

private def errorAbiUnauthorized : String :=
  "{\"type\":\"error\",\"name\":\"Unauthorized\",\"inputs\":[" ++
    "{\"name\":\"who\",\"type\":\"address\"}]}"

private def errorAbiZeroAddress : String :=
  "{\"type\":\"error\",\"name\":\"ZeroAddress\",\"inputs\":[]}"

private def errorAbiExpired : String :=
  "{\"type\":\"error\",\"name\":\"Expired\",\"inputs\":[]}"

private def collectLogNames (fuel : Nat) (ops : Array IR.Op) : Array String :=
  match fuel with
  | 0 => #[]
  | fuel' + 1 =>
    ops.foldl (init := #[]) fun acc op =>
      match op with
      | .evmLog n _ => if acc.contains n then acc else acc.push n
      | .evmLogTransfer256 .. => if acc.contains "Transfer256" then acc else acc.push "Transfer256"
      | .evmLogApproval256 .. => if acc.contains "Approval256" then acc else acc.push "Approval256"
      | .ite _ _ _ t f =>
        (collectLogNames fuel' t ++ collectLogNames fuel' f).foldl (init := acc) fun acc n =>
          if acc.contains n then acc else acc.push n
      | _ => acc

private def hasErrorLeaf (fuel : Nat) (pred : IR.Op → Bool) (ops : Array IR.Op) : Bool :=
  match fuel with
  | 0 => false
  | fuel' + 1 =>
    ops.any fun op =>
      pred op ||
        match op with
        | .ite _ _ _ t f => hasErrorLeaf fuel' pred t || hasErrorLeaf fuel' pred f
        | _ => false

private def receiveAbi : String :=
  "{\"type\":\"receive\",\"stateMutability\":\"payable\"}"

def emitAbi (p : IR.Program) : String :=
  let evs :=
    p.entries.foldl (init := #[]) fun acc m =>
      (collectLogNames 8 m.ops).foldl (init := acc) fun acc n =>
        if acc.contains n then acc else acc.push n
  let needIns := p.entries.any (fun m =>
    hasErrorLeaf 8 (fun | .evmRevertInsufficient .. => true | _ => false) m.ops)
  let needUnauth := p.entries.any (fun m =>
    hasErrorLeaf 8 (fun
      | .evmRevertUnauthorized .. | .evmPermit .. => true
      | _ => false) m.ops)
  let needZero := p.entries.any (fun m =>
    hasErrorLeaf 8 (fun | .evmRevertZeroAddress => true | _ => false) m.ops)
  let needExpired := p.entries.any (fun m =>
    hasErrorLeaf 8 (fun | .evmPermit .. => true | _ => false) m.ops)
  let needRecv := p.entries.any (fun m => m.ixName == "receive")
  let items :=
    #[ctorAbi p] ++ evs.map eventAbi ++
      (if needIns then #[errorAbiInsufficient] else #[]) ++
      (if needUnauth then #[errorAbiUnauthorized] else #[]) ++
      (if needZero then #[errorAbiZeroAddress] else #[]) ++
      (if needExpired then #[errorAbiExpired] else #[]) ++
      (if needRecv then #[receiveAbi] else #[]) ++
      p.entries.filterMap fun m =>
        if m.ixName == "receive" then none else some (entryAbi m)
  "[
  " ++ String.intercalate ",
  " items.toList ++ "
]
"

def emit (p : IR.Program) : Except String (String × String) := do
  let yul ← emitYul p
  return (yul, emitAbi p)

end ProofForge.Evm.Emit
