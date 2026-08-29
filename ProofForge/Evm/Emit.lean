import ProofForge.Evm.Ops
import ProofForge.Evm.IR
import ProofForge.Evm.Payable
import ProofForge.Evm.Payable.Emit
import ProofForge.Evm.Codec.Emit
import ProofForge.Evm.Component.Emit
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

private def staticU64SlotOf (p : IR.Program) (name : String) : Except String Nat := do
  let slot ← slotOf p name
  match IR.slotWidth p name with
  | some 8 => pure slot
  | some width =>
      throw s!"extract/unsupported: immediate static store requires UInt64 field {name}, got width {width}"
  | none => throw s!"extract/unsupported: unknown field {name}"

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

/-- Store logical fixed bytes from little-endian source limbs into ABI byte order. The loop is
bounded by the validated compile-time size supplied at each call site. -/
private def renderFixedBytesHelper : String :=
  "      function pf_store_fixed_bytes(off, w0, w1, w2, w3, size) {" ++ nl ++
  "        mstore(off, 0)" ++ nl ++
  "        for { let i := 0 } lt(i, size) { i := add(i, 1) } {" ++ nl ++
  "          let word := w0" ++ nl ++
  "          switch div(i, 8)" ++ nl ++
  "          case 1 { word := w1 }" ++ nl ++
  "          case 2 { word := w2 }" ++ nl ++
  "          case 3 { word := w3 }" ++ nl ++
  "          mstore8(add(off, i), and(shr(mul(8, mod(i, 8)), word), 0xff))" ++ nl ++
  "        }" ++ nl ++
  "      }" ++ nl

private def widthMask (width : Nat) : String :=
  if width == 8 then u64MaxYul else Codec.byteMask width

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

private def packFixedBytesLimb (src : String) (bytes limb : Nat) : String :=
  let start := 8 * limb
  let count := min 8 (bytes - start)
  let rec orBytes (i remaining : Nat) (acc : String) : String :=
    match remaining with
    | 0 => acc
    | remaining' + 1 =>
      let byte := "byte(" ++ toString (start + i) ++ ", " ++ src ++ ")"
      let next := if i == 0 then byte
        else "or(" ++ acc ++ ", shl(" ++ toString (8 * i) ++ ", " ++ byte ++ "))"
      orBytes (i + 1) remaining' next
  orBytes 0 count "0"

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
    (paramWidths : Array Core.Codec.Scalar) (v : Ops.Val) : Except String String :=
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
        match paramWidths[i]? with
        | some type =>
            if Codec.isWideIntegerCarrier type then
              match uint256LeafOff name with
              | some off =>
                  if off < Codec.limbCount type then .ok (packU256Word s!"{paramPrefix}{i}" off)
                  else .error s!"evm/codec: out-of-range integer projection {name}"
              | none => .error s!"evm/codec: invalid wide-integer projection {name}"
            else if Codec.isFixedBytesCarrier type then
              match type, uint256LeafOff name with
              | .fixedBytes bytes, some off =>
                  if off < Codec.limbCount type then
                    .ok (packFixedBytesLimb s!"{paramPrefix}{i}" bytes off)
                  else .error s!"evm/codec: out-of-range fixed-bytes projection {name}"
              | _, _ => .error s!"evm/codec: invalid fixed-bytes projection {name}"
            else if Codec.isAddressCarrier type then
              match addrLeafOff name with
              | some off => .ok (packAddrWord s!"{paramPrefix}{i}" off)
              | none => .error s!"evm/codec: invalid address projection {name}"
            else do
              let slot ← slotOf p name
              let w := (IR.slotWidth p name).getD 8
              return maskExpr w s!"sload({slot})"
        | none => .error s!"evm/codec: missing parameter metadata at {i}"
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
    .ext (.callValue256 _) _ | .ext (.selfBalance256 _) _ | .ext (.gasLeft256 _) _ |
    .ext (.baseFee256 _) _ | .ext (.prevRandao256 _) _ | .ext (.gasLimit256 _) _ |
    .ext (.domainSep256 _) _ |
    .ext (.component _) _ =>
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

/-- Materialize one 256-bit EVM environment word once, then project its allocation-free UInt64
limbs from the render cache. Environment leaves share this policy instead of duplicating cache and
packing logic for every opcode. -/
private def materializePackedEnvWord (indent cacheKey expression : String) (limb : Nat)
    (st : Render) : String × String × Render :=
  match lookupWide st cacheKey with
  | some packed =>
      let (name, st') := fresh st
      (indent ++ "let " ++ name ++ " := " ++ packU256Word packed limb ++ nl, name, st')
  | none =>
      let (packed, st1) := fresh st
      let (name, st2) := fresh (rememberWide st1 cacheKey packed)
      let text :=
        indent ++ "let " ++ packed ++ " := " ++ expression ++ nl ++
        indent ++ "let " ++ name ++ " := " ++ packU256Word packed limb ++ nl
      (text, name, st2)

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
private partial def materializeVal (p : IR.Program) (indent paramPrefix : String)
    (paramCount : Nat) (paramWidths : Array Core.Codec.Scalar) (v : Ops.Val) (st : Render) :
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
    | .ext (.callValue256 limb) #[] =>
        return materializePackedEnvWord indent "cval256" "callvalue()" limb st
    | .ext (.selfBalance256 limb) #[] =>
        return materializePackedEnvWord indent "sbal256" "selfbalance()" limb st
    | .ext (.gasLeft256 limb) #[] =>
        return materializePackedEnvWord indent "gas256" "gas()" limb st
    | .ext (.baseFee256 limb) #[] =>
        return materializePackedEnvWord indent "basefee256" "basefee()" limb st
    | .ext (.prevRandao256 limb) #[] =>
        return materializePackedEnvWord indent "randao256" "prevrandao()" limb st
    | .ext (.gasLimit256 limb) #[] =>
        return materializePackedEnvWord indent "gaslimit256" "gaslimit()" limb st
    | .ext (.domainSep256 limb) #[] =>
        let (pre, ret, st1) := emitDomainSeparator indent st
        let (nm, st2) := fresh st1
        return (pre ++ indent ++ "let " ++ nm ++ " := " ++
          packFixedBytesLimb ret 32 limb ++ nl, nm, st2)
    | .ext (.component query) operands =>
        let context : Component.Emit.Context Render := {
          materialize := fun value st =>
            materializeVal p indent paramPrefix paramCount paramWidths value st
          fresh := fresh
          rememberWide := rememberWide
          lookupWide := lookupWide
          valKey := valKey
          resolveStaticU64Slot := staticU64SlotOf p
          indent
        }
        Component.Emit.emitQuery context query operands st
    | _ =>
        let e ← loadVal p paramPrefix paramCount paramWidths v
        return ("", e, st)

private def brace (inner : String) : String :=
  "{" ++ nl ++ inner ++ "}"

private partial def emitOps (p : IR.Program) (indent paramPrefix : String)
    (paramCount : Nat) (paramWidths : Array Core.Codec.Scalar) (ops : Array IR.Op) (st : Render) :
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
    | .component call =>
        let context : Component.Emit.Context Render := {
          materialize := fun value st =>
            materializeVal p indent paramPrefix paramCount paramWidths value st
          fresh := fresh
          rememberWide := rememberWide
          lookupWide := lookupWide
          valKey := valKey
          resolveStaticU64Slot := staticU64SlotOf p
          indent
        }
        let (txt, last, st') ← Component.Emit.emitCall context call st
        acc := acc ++ txt
        st := { st' with last := some last }
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
  | query
  | effect
  | stored
  | conflict
  deriving BEq, Inhabited

private def cfgHintHasLast : CFGResultHint → Bool
  | .checked _ | .query | .effect => true
  | .plain | .stored | .conflict => false

private def cfgHintReturnsLast : CFGResultHint → Bool
  | .query => true
  | .plain | .checked _ | .effect | .stored | .conflict => false

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
    | .ext (.component (.hashedMap (.getU64 ..)))
    | .ext (.component (.hashedMap (.getAddr ..)))
    | .ext (.component (.hashedMap (.getPair ..))) => .query
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
    (paramCount : Nat) (paramWidths : Array Core.Codec.Scalar) (value : Ops.Val) (last : Option String)
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
    (paramCount : Nat) (paramWidths : Array Core.Codec.Scalar) (operation : Core.CFG.Checked Ops.ValKind)
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

private def schemaIsStaticAggregate : Core.Codec.Schema → Bool
  | .tuple _ | .record _ _ | .fixedArray _ _ => true
  | _ => false

/-- Pack the scalar source limbs of a static logical aggregate into its canonical ABI words.
Every scalar leaf owns one word; wide integers, addresses, and fixed bytes consume several source
limbs but never extra ABI words. -/
private def emitStaticReturnWords (p : IR.Program) (method : IR.Method) (indent : String)
    (paramTypes retTypes : Array Core.Codec.Scalar) (values : Array Ops.Val) (st : Render) :
    Except String (String × Render) := do
  let expected := retTypes.foldl (init := 0) fun count type => count + Codec.limbCount type
  unless values.size == expected do
    throw s!"evm/codec: aggregate result has {values.size} source parts, expected {expected}"
  let mut out := ""
  let mut st := st
  let mut valueIndex : Nat := 0
  for wordIndex in [0:retTypes.size] do
    let type := retTypes[wordIndex]!
    let partCount := Codec.limbCount type
    let mut parts : Array String := #[]
    for _ in [0:partCount] do
      let (pre, expression, next) ←
        materializeVal p indent "arg" method.paramCount paramTypes values[valueIndex]! st
      out := out ++ pre
      parts := parts.push expression
      st := next
      valueIndex := valueIndex + 1
    let offset := wordIndex * 32
    if Codec.isWideIntegerCarrier type then
      out := out ++ indent ++ "mstore(" ++ toString offset ++ ", " ++
        packU256 (parts[0]!) (parts[1]!) ((parts[2]?).getD "0") ((parts[3]?).getD "0") ++
        ")" ++ nl
    else if Codec.isFixedBytesCarrier type then
      out := out ++ indent ++ "pf_store_fixed_bytes(" ++ toString offset ++ ", " ++
        (parts[0]?).getD "0" ++ ", " ++ (parts[1]?).getD "0" ++ ", " ++
        (parts[2]?).getD "0" ++ ", " ++ (parts[3]?).getD "0" ++ ", " ++
        toString type.byteWidth ++ ")" ++ nl
    else if Codec.isAddressCarrier type then
      out := out ++ indent ++ "pf_store_addr20(" ++ toString offset ++ ", " ++
        (parts[0]?).getD "0" ++ ", " ++ (parts[1]?).getD "0" ++ ", " ++
        (parts[2]?).getD "0" ++ ")" ++ nl
    else
      out := out ++ indent ++ "mstore(" ++ toString offset ++ ", " ++ parts[0]! ++ ")" ++ nl
  return (out ++ indent ++ "return(0, " ++ toString (retTypes.size * 32) ++ ")" ++ nl, st)

private def emitCFGCase (p : IR.Program) (method : IR.Method)
    (hints : Array (Core.CFG.BlockId × CFGResultHint))
    (block : Core.CFG.Block Ops.ValKind Ops.OpExt) (st : Render) :
    Except String (String × Render) := do
  unless block.params.isEmpty do
    throw s!"evm/cfg: block parameters are not lowered in block {block.id}"
  let paramTypes ← method.resolvedParamTypes
  let retTypes ← method.resolvedRetTypes
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
      emitOps p indent "arg" method.paramCount paramTypes instruction afterInstructions
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
        materializeVal p indent "arg" method.paramCount paramTypes lhs finalState
      let (preR, right, st2) ←
        materializeVal p indent "arg" method.paramCount paramTypes rhs st1
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
      let (checkedText, next) ← emitCFGChecked p indent "arg" method.paramCount paramTypes
        operation success.target overflow.target finalState
      body := body ++ checkedText
      finalState := { next with last := none }
  | .exit result =>
      match result with
      | .initialize _ => throw "evm/cfg: initializer reached runtime entry"
      | .okState value =>
          let (exitText, next) ← emitCFGOkState p indent "arg" method.paramCount paramTypes
            value none afterHint finalState
          body := body ++ exitText
          finalState := next
      | .errorOverflow => body := body ++ indent ++ revert0 ++ nl
      | .errorNamed name => body := body ++ revertNamed indent name
      | .returnU64 value =>
          -- A return after a mutation owns its explicit value; substituting the effect carrier
          -- leaks an event/write result into the source ABI (for example an ERC-20 Boolean).
          -- Legacy statement-shaped scalar map reads are the sole query carrier kept in `pf_last`.
          let (pre, expression, next) ←
            if cfgHintReturnsLast afterHint then pure ("", "pf_last", finalState)
            else materializeVal p indent "arg" method.paramCount paramTypes value finalState
          body := body ++ pre
          match retTypes.toList with
          | [.fixedBytes bytes] =>
              body := body ++ indent ++ "pf_store_fixed_bytes(0, " ++ expression ++
                ", 0, 0, 0, " ++ toString bytes ++ ")" ++ nl ++
                indent ++ "return(0, 32)" ++ nl
          | _ => body := body ++ returnWord indent expression
          finalState := next
      | .returnU64s values =>
          if values.isEmpty then throw "evm/cfg: empty return tuple"
          if let some plan := method.outputPlan then
            let context : Codec.Emit.ReturnContext Ops.Val Render := {
              indent
              materialize := fun valueIndent value state =>
                materializeVal p valueIndent "arg" method.paramCount paramTypes value state
            }
            let (text, next) ←
              Codec.Emit.renderReturn context plan values finalState
            body := body ++ text
            finalState := next
          else if schemaIsStaticAggregate method.retSchema then
            let (text, next) ←
              emitStaticReturnWords p method indent paramTypes retTypes values finalState
            body := body ++ text
            finalState := next
          else if retTypes.size == 1 && Codec.isWideIntegerCarrier retTypes[0]! &&
              values.size == Codec.limbCount retTypes[0]! then
            let mut pre := ""
            let mut limbs := #[]
            for value in values do
              let (text, expression, next) ←
                materializeVal p indent "arg" method.paramCount paramTypes value finalState
              finalState := next
              pre := pre ++ text
              limbs := limbs.push expression
            let a0 := limbs[0]!
            let a1 := limbs[1]!
            let a2 := (limbs[2]?).getD "0"
            let a3 := (limbs[3]?).getD "0"
            body := body ++ pre ++
              indent ++ "mstore(0, " ++ packU256 a0 a1 a2 a3 ++ ")" ++ nl ++
              indent ++ "return(0, 32)" ++ nl
          else if retTypes.size == 1 && Codec.isFixedBytesCarrier retTypes[0]! &&
              values.size == Codec.limbCount retTypes[0]! then
            let mut pre := ""
            let mut limbs := #[]
            for value in values do
              let (text, expression, next) ←
                materializeVal p indent "arg" method.paramCount paramTypes value finalState
              finalState := next
              pre := pre ++ text
              limbs := limbs.push expression
            let bytes := retTypes[0]!.byteWidth
            body := body ++ pre ++ indent ++ "pf_store_fixed_bytes(0, " ++
              (limbs[0]?).getD "0" ++ ", " ++ (limbs[1]?).getD "0" ++ ", " ++
              (limbs[2]?).getD "0" ++ ", " ++ (limbs[3]?).getD "0" ++ ", " ++
              toString bytes ++ ")" ++ nl ++ indent ++ "return(0, 32)" ++ nl
          else if retTypes.size == 1 && Codec.isAddressCarrier retTypes[0]! && values.size == 3 then
            let (p0, a0, s0) ←
              materializeVal p indent "arg" method.paramCount paramTypes values[0]! finalState
            let (p1, a1, s1) ←
              materializeVal p indent "arg" method.paramCount paramTypes values[1]! s0
            let (p2, a2, s2) ←
              materializeVal p indent "arg" method.paramCount paramTypes values[2]! s1
            finalState := s2
            body := body ++ p0 ++ p1 ++ p2 ++
              indent ++ "mstore(0, 0)" ++ nl ++
              packAddrMstore8 indent a0 a1 a2 ++
              indent ++ "return(0, 32)" ++ nl
          else
            for i in [0:values.size] do
              let (pre, expression, next) ←
                materializeVal p indent "arg" method.paramCount paramTypes values[i]! finalState
              finalState := next
              body := body ++ pre ++ indent ++ "mstore(" ++ toString (i * 32) ++ ", " ++
                expression ++ ")" ++ nl
            body := body ++ indent ++ "return(0, " ++ toString (values.size * 32) ++ ")" ++ nl
      | .returnState value =>
          let (pre, expression, next) ←
            materializeVal p indent "arg" method.paramCount paramTypes value finalState
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
  let paramTypes ← p.constructor.resolvedParamTypes
  for s in p.slots do
    if h : i < vs.size then
      let v ← loadVal p "ctor_arg" p.constructor.paramCount paramTypes vs[i]
      unless v == "0" do
        body := body ++ storeSlot "    " s.index (maskExpr s.width v)
    i := i + 1
  return body

private def renderCtorPrelude (objectName : String) (paramCount : Nat)
    (paramWidths : Array Core.Codec.Scalar) (plans : Array Codec.AbiInputPlan) :
    Except String String := do
    let ctorGuard ← Payable.Emit.emitValueGate { indent := "    " } .reject
    let argumentBytes := paramCount * 32
    let mut out :=
      ctorGuard ++
      "    let programSize := datasize(" ++ q objectName ++ ")" ++ nl ++
      "    if iszero(eq(codesize(), add(programSize, " ++ toString argumentBytes ++
        "))) { " ++ revert0 ++ " }" ++ nl
    if argumentBytes > 0 then
      out := out ++ "    codecopy(0, programSize, " ++ toString argumentBytes ++ ")" ++ nl
    for i in [0:paramCount] do
      out := out ++
        "    let ctor_arg" ++ toString i ++ " := mload(" ++ toString (i * 32) ++ ")" ++ nl
      let some type := paramWidths[i]?
        | throw s!"evm/codec: missing constructor parameter metadata at {i}"
      out := out ++ (← Codec.Emit.renderWordGuard "    " ("ctor_arg" ++ toString i) type)
    return out ++ (← Codec.Emit.renderTaggedGuards "    " "ctor_arg" plans)

/-- Bake constructor arguments that are not stored: up to two `uint64`
(`imm0`/`imm1`) and two `address` (`immAddr`/`immAddr2`) values.
`setimmutable(offset, name, value)` patches runtime already copied to memory at `offset`. -/
private def renderImmutableSets (paramCount : Nat) (paramWidths : Array Core.Codec.Scalar) : String :=
  Id.run do
    let mut out := ""
    let mut usedU64 : Nat := 0
    let mut usedAddr : Nat := 0
    for i in [0:paramCount] do
      let type := (paramWidths[i]?).getD .uint64
      let nm := "ctor_arg" ++ toString i
      if Codec.isAddressCarrier type && usedAddr < 2 then
        let name := if usedAddr == 0 then "immAddr" else "immAddr2"
        out := out ++ "    setimmutable(0, \"" ++ name ++ "\", " ++ nm ++ ")" ++ nl
        usedAddr := usedAddr + 1
      else if Codec.isNarrowIntegerCarrier type && usedU64 < 2 then
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
      match Payable.Emit.emitReceiveRoute { indent := "      " }
          (Payable.EntryPlan.ofEntry (isReceive := true) m.payable) body with
      | .error reason => throw s!"{reason} in {m.ixName}"
      | .ok txt => pure txt

private def renderEntry (p : IR.Program) (m : IR.Method) (localValueGuard : Bool) :
    Except String String := do
  let paramTypes ← m.resolvedParamTypes
  let plans ←
    if m.paramSchemas.isEmpty then pure #[]
    else m.paramSchemas.mapM Codec.inputPlan
  unless m.inputPolicy == IR.inputPolicyOf plans do
    throw s!"evm/codec: input policy identity mismatch in {m.ixName}"
  let entryPlan := Payable.EntryPlan.ofEntry (isReceive := false) m.payable
  unless entryPlan.wellFormed do
    throw s!"extract/unsupported: evm entry policy shape in {m.ixName}"
  let mut head :=
    "      case 0x" ++ m.selector ++ " {" ++ nl
  if localValueGuard && !m.payable then
    head := head ++ (← Payable.Emit.emitValueGate { indent := "        " } entryPlan.gate)
  if plans.isEmpty then
    let calldataBytes := 4 + m.paramCount * 32
    head := head ++
      "        if iszero(eq(calldatasize(), " ++ toString calldataBytes ++ ")) { " ++
        revert0 ++ " }" ++ nl
    for i in [0:m.paramCount] do
      let off := 4 + i * 32
      head := head ++
        "        let arg" ++ toString i ++ " := calldataload(" ++ toString off ++ ")" ++ nl
      let some type := paramTypes[i]?
        | throw s!"evm/codec: missing entry parameter metadata at {i}"
      head := head ++ (← Codec.Emit.renderWordGuard "        " ("arg" ++ toString i) type)
  else
    head := head ++ (← Codec.Emit.renderEntryArgs plans paramTypes)
  head := head ++ (← Codec.Emit.renderTaggedGuards "        " "arg" plans)
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
  let ctorParamTypes ← p.constructor.resolvedParamTypes
  let ctorPlans ←
    if p.constructor.paramSchemas.isEmpty then pure #[]
    else p.constructor.paramSchemas.mapM Codec.inputPlan
  if ctorPlans.any (·.dynamic.isSome) then
    throw "evm/codec: dynamic constructor inputs are not supported"
  unless p.constructor.inputPolicy == IR.inputPolicyOf ctorPlans do
    throw "evm/codec: constructor input policy identity mismatch"
  let ctorHead ←
    renderCtorPrelude p.name p.constructor.paramCount ctorParamTypes ctorPlans
  let ctorStores ← emitConstructorStores p
  let ctorImm :=
    if IR.programHasImmutable p then
      renderImmutableSets p.constructor.paramCount ctorParamTypes
    else ""
  let anyPay := hasPayableEntry p
  let mut receiveTxt := ""
  let mut entries := ""
  for m in p.entries do
    if m.ixName == "receive" then
      receiveTxt := receiveTxt ++ (← renderReceive p m)
    else
      entries := entries ++ (← renderEntry p m anyPay)
  let globalGuard ←
    if anyPay then pure ""
    else Payable.Emit.emitValueGate { indent := "      " } .reject
  let selectorHead ←
    Payable.Emit.emitSelectorHead { indent := "      " } .selectorDispatch
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
    renderFixedBytesHelper ++
    globalGuard ++
    receiveTxt ++
    selectorHead ++
    entries ++
    "      default { " ++ revert0 ++ " }" ++ nl ++
    "    }" ++ nl ++
    "  }" ++ nl ++
    "}" ++ nl
  return yul

private def escapeJson (s : String) : String :=
  s.replace "\\" "\\\\" |>.replace "\"" "\\\""

private def paramsJsonOf (types : Array Core.Codec.Scalar) : Except String String := do
  let mut params := #[]
  for i in [0:types.size] do
    let abiType ← Codec.abiType types[i]!
    params := params.push ("{\"name\":\"arg" ++ toString i ++ "\",\"type\":\"" ++
      abiType ++ "\"}")
  return String.intercalate "," params.toList

private structure AbiJsonShape where
  type : String
  components : Array (String × AbiJsonShape) := #[]
  deriving Inhabited

private partial def abiJsonShape : Core.Codec.Schema → Except String AbiJsonShape
  | .unit => throw "evm/codec: unit has no ABI JSON parameter shape"
  | .scalar type => return { type := ← Codec.abiType type }
  | .tuple items => do
      let mut components := #[]
      for item in items do
        components := components.push ("", ← abiJsonShape item)
      return { type := "tuple", components }
  | .record _ fields => do
      let mut components := #[]
      for field in fields do
        components := components.push (field.1, ← abiJsonShape field.2)
      return { type := "tuple", components }
  | .fixedArray length element => do
      let shape ← abiJsonShape element
      return { shape with type := shape.type ++ "[" ++ toString length ++ "]" }
  | .enumeration .. => throw "evm/codec: enum ABI JSON requires an explicit tag policy"
  | .option _ => throw "evm/codec: option ABI JSON requires an explicit tag policy"
  | .boundedArray _ element => do
      let shape ← abiJsonShape element
      return { shape with type := shape.type ++ "[]" }
  | .boundedBytes _ => return { type := "bytes" }
  | .boundedString _ => return { type := "string" }

private def abiJsonInputShape : Core.Codec.Schema → Except String AbiJsonShape
  | .option payload => do
      let _ ← Codec.taggedTupleV1InputPlan (.option payload)
      return {
        type := "tuple"
        components := #[
          ("present", { type := "bool" }),
          ("value", ← abiJsonShape payload)
        ]
      }
  | schema@(.enumeration ..) => do
      let plan ← Codec.taggedTupleV1InputPlan schema
      let mut components : Array (String × AbiJsonShape) := #[
        ("tag", { type := "uint8" })
      ]
      for i in [1:plan.wordCount] do
        components := components.push
          ("p" ++ toString (i - 1), { type := ← Codec.abiType plan.words[i]! })
      return { type := "tuple", components }
  | schema => abiJsonShape schema

/-- Output JSON follows the independent ABI output plan. Logical sums use the same public tuple
shape as Tagged Tuple v1 inputs, without reusing calldata plans or decoded guard state. -/
private def abiJsonOutputShape : Core.Codec.Schema → Except String AbiJsonShape
  | schema@(.option payload) => do
      let _ ← Codec.taggedTupleV1OutputPlan schema
      return {
        type := "tuple"
        components := #[
          ("present", { type := "bool" }),
          ("value", ← abiJsonShape payload)
        ]
      }
  | schema@(.enumeration ..) => do
      let plan ← Codec.taggedTupleV1OutputPlan schema
      let mut components : Array (String × AbiJsonShape) := #[
        ("tag", { type := "uint8" })
      ]
      for i in [1:plan.words.size] do
        components := components.push
          ("p" ++ toString (i - 1), { type := ← Codec.abiType plan.words[i]! })
      return { type := "tuple", components }
  | schema => abiJsonShape schema

private partial def renderAbiJsonParam (name : String) (shape : AbiJsonShape) : String :=
  let base := "{\"name\":\"" ++ escapeJson name ++ "\",\"type\":\"" ++ shape.type ++ "\""
  if shape.components.isEmpty then base ++ "}"
  else
    let components := shape.components.map fun component =>
      renderAbiJsonParam component.1 component.2
    base ++ ",\"components\":[" ++ String.intercalate "," components.toList ++ "]}"

private def schemaParamsJsonOf (schemas : Array Core.Codec.Schema) : Except String String := do
  let mut params := #[]
  for i in [0:schemas.size] do
    params := params.push (renderAbiJsonParam s!"arg{i}" (← abiJsonInputShape schemas[i]!))
  return String.intercalate "," params.toList

private def ctorAbi (p : IR.Program) : Except String String := do
  unless p.constructor.paramSchemas.isEmpty do
    let plans ← p.constructor.paramSchemas.mapM Codec.inputPlan
    if plans.any (·.dynamic.isSome) then
      throw "evm/codec: dynamic constructor inputs are not supported"
  let inputs ←
    if p.constructor.paramSchemas.isEmpty then paramsJsonOf (← p.constructor.resolvedParamTypes)
    else schemaParamsJsonOf p.constructor.paramSchemas
  return "{\"type\":\"constructor\",\"stateMutability\":\"nonpayable\",\"inputs\":[" ++
    inputs ++ "]}"

private def outputsJson (m : IR.Method) : Except String String := do
  unless m.retSchema == .unit do
    return "[" ++ renderAbiJsonParam "" (← abiJsonOutputShape m.retSchema) ++ "]"
  let types ← m.resolvedRetTypes
  let mut outputs := #[]
  for type in types do
    outputs := outputs.push ("{\"name\":\"\",\"type\":\"" ++ (← Codec.abiType type) ++ "\"}")
  return "[" ++ String.intercalate "," outputs.toList ++ "]"

private def entryAbi (m : IR.Method) : Except String String := do
  let mutab := if m.view then "view" else if m.payable then "payable" else "nonpayable"
  let inputs ←
    if m.paramSchemas.isEmpty then paramsJsonOf (← m.resolvedParamTypes)
    else schemaParamsJsonOf m.paramSchemas
  let outputs ← outputsJson m
  return "{\"type\":\"function\",\"name\":\"" ++ escapeJson m.ixName ++
    "\",\"stateMutability\":\"" ++ mutab ++ "\",\"inputs\":[" ++
    inputs ++ "],\"outputs\":" ++ outputs ++ "}"

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

private def errorAbiPaused : String :=
  "{\"type\":\"error\",\"name\":\"Paused\",\"inputs\":[]}"

private def errorAbiCapExceeded : String :=
  "{\"type\":\"error\",\"name\":\"CapExceeded\",\"inputs\":[]}"

private def errorAbiExpired : String :=
  "{\"type\":\"error\",\"name\":\"Expired\",\"inputs\":[]}"

private def errorAbiNamed (name : String) : String :=
  "{\"type\":\"error\",\"name\":\"" ++ escapeJson name ++ "\",\"inputs\":[]}"

/-- Collect unique metadata names from the full structured op tree in first-use order. ABI
metadata must follow the same `ite`/bounded-`forBody` nesting that the Yul emitter consumes. -/
private partial def collectOpNames (nameOf : IR.Op → Option String)
    (ops : Array IR.Op) : Array String :=
  ops.foldl (init := #[]) fun acc op =>
    let acc :=
      match nameOf op with
      | some name => if acc.contains name then acc else acc.push name
      | none => acc
    let nested :=
      match op with
      | .ite _ _ _ t f => collectOpNames nameOf t ++ collectOpNames nameOf f
      | .forBody _ body => collectOpNames nameOf body
      | _ => #[]
    nested.foldl (init := acc) fun acc name =>
      if acc.contains name then acc else acc.push name

private def collectLogNames (ops : Array IR.Op) : Array String :=
  collectOpNames (fun
    | .component call => call.logName
    | _ => none) ops

private def collectNamedErrorNames (ops : Array IR.Op) : Array String :=
  collectOpNames (fun
    | .errorNamed name => some name
    | _ => none) ops

private partial def hasErrorLeaf (pred : IR.Op → Bool) (ops : Array IR.Op) : Bool :=
  ops.any fun op =>
    pred op ||
      match op with
      | .ite _ _ _ t f => hasErrorLeaf pred t || hasErrorLeaf pred f
      | .forBody _ body => hasErrorLeaf pred body
      | _ => false

private def receiveAbi : String :=
  "{\"type\":\"receive\",\"stateMutability\":\"payable\"}"

def emitAbiChecked (p : IR.Program) : Except String String := do
  let evs :=
    p.entries.foldl (init := #[]) fun acc m =>
      (collectLogNames m.ops).foldl (init := acc) fun acc n =>
        if acc.contains n then acc else acc.push n
  let namedErrors :=
    p.entries.foldl (init := #[]) fun acc m =>
      (collectNamedErrorNames m.ops).foldl (init := acc) fun acc n =>
        if acc.contains n then acc else acc.push n
  let needIns := p.entries.any (fun m =>
    hasErrorLeaf (fun
      | .component call => call.emitsInsufficient
      | _ => false) m.ops)
  let needUnauth := p.entries.any (fun m =>
    hasErrorLeaf (fun
      | .component call => call.emitsUnauthorized
      | _ => false) m.ops)
  let needZero := p.entries.any (fun m =>
    hasErrorLeaf (fun
      | .component call => call.emitsZeroAddress
      | _ => false) m.ops)
  let needPaused := p.entries.any (fun m =>
    hasErrorLeaf (fun
      | .component call => call.emitsPaused
      | _ => false) m.ops)
  let needCap := p.entries.any (fun m =>
    hasErrorLeaf (fun
      | .component call => call.emitsCapExceeded
      | _ => false) m.ops)
  let needExpired := p.entries.any (fun m =>
    hasErrorLeaf (fun
      | .component call => call.emitsExpired
      | _ => false) m.ops)
  let needRecv := p.entries.any (fun m => m.ixName == "receive")
  let mut entryItems := #[]
  for method in p.entries do
    unless method.ixName == "receive" do
      entryItems := entryItems.push (← entryAbi method)
  let items :=
    #[← ctorAbi p] ++ evs.map eventAbi ++
      (if needIns then #[errorAbiInsufficient] else #[]) ++
      (if needUnauth then #[errorAbiUnauthorized] else #[]) ++
      (if needZero then #[errorAbiZeroAddress] else #[]) ++
      (if needPaused then #[errorAbiPaused] else #[]) ++
      (if needCap then #[errorAbiCapExceeded] else #[]) ++
      (if needExpired then #[errorAbiExpired] else #[]) ++
      namedErrors.map errorAbiNamed ++
      (if needRecv then #[receiveAbi] else #[]) ++
      entryItems
  return "[
  " ++ String.intercalate ",
  " items.toList ++ "
]
"

/-- Compatibility wrapper for callers that only need a valid artifact. Assembly
uses `emitAbiChecked` and reports malformed codec metadata. -/
def emitAbi (p : IR.Program) : String :=
  match emitAbiChecked p with
  | .ok abi => abi
  | .error _ => ""

def emit (p : IR.Program) : Except String (String × String) := do
  let yul ← emitYul p
  return (yul, ← emitAbiChecked p)

end ProofForge.Evm.Emit
