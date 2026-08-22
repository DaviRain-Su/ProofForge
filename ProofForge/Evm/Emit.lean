import ProofForge.Ops
import ProofForge.Evm.IR
import ProofForge.Crypto.Keccak

namespace ProofForge.Evm.Emit

open ProofForge
open ProofForge.Evm
open ProofForge.Crypto

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
  else s!"0x{ProofForge.IR.u64Hex n}"

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

/-- 把三叶 Addr20 写到 calldata 的 `off..off+19`（transfer 的 dest 从 16 起）。 -/
private def packAddrAt (indent : String) (off : Nat) (w0 w1 w2 : String) : String :=
  Id.run do
    let mut out := ""
    for i in [0:8] do
      out := out ++ indent ++ "mstore8(" ++ toString (off + i) ++ ", and(shr(" ++
        toString (8 * i) ++ ", " ++ w0 ++ "), 0xff))" ++ nl
    for i in [0:8] do
      out := out ++ indent ++ "mstore8(" ++ toString (off + 8 + i) ++ ", and(shr(" ++
        toString (8 * i) ++ ", " ++ w1 ++ "), 0xff))" ++ nl
    for i in [0:4] do
      out := out ++ indent ++ "mstore8(" ++ toString (off + 16 + i) ++ ", and(shr(" ++
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
  | .clockEpoch | .slotsPerEpoch | .accLamports0 | .accOwner0 | .accDataLen0
  | .accN | .isSigner0 | .isWritable0 | .isExecutable0
  | .accLamports1 | .accOwner1 | .accDataLen1
  | .isSigner1 | .isWritable1 | .isExecutable1
  | .findPda _ | .checkPda .. | .rentExemption _ | .cpiReturn
  | .sha256Lit _ | .keccak256Lit _ | .accKeyWord .. | .accOwnerWord ..
  | .unixTime | .accLamportsN _ | .accDataLenN _ | .isSignerN _
  | .isWritableN _ | .isExecutableN _ | .signerKeyN _ | .ownerIsSelf _ =>
      .error "extract/unsupported: evm rejects svm leaf"
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
  | .bitAnd l r => do
      let lv ← loadVal p paramPrefix paramCount l
      let rv ← loadVal p paramPrefix paramCount r
      return "and(" ++ lv ++ ", " ++ rv ++ ")"
  | .bitOr l r => do
      let lv ← loadVal p paramPrefix paramCount l
      let rv ← loadVal p paramPrefix paramCount r
      return "or(" ++ lv ++ ", " ++ rv ++ ")"
  | .bitXor l r => do
      let lv ← loadVal p paramPrefix paramCount l
      let rv ← loadVal p paramPrefix paramCount r
      return "xor(" ++ lv ++ ", " ++ rv ++ ")"
  | .bitNot v => do
      let ev ← loadVal p paramPrefix paramCount v
      return "and(not(" ++ ev ++ "), " ++ u64MaxYul ++ ")"
  | .shiftL l r => do
      let lv ← loadVal p paramPrefix paramCount l
      let rv ← loadVal p paramPrefix paramCount r
      return "shl(" ++ rv ++ ", " ++ lv ++ ")"
  | .shiftR l r => do
      let lv ← loadVal p paramPrefix paramCount l
      let rv ← loadVal p paramPrefix paramCount r
      return "shr(" ++ rv ++ ", " ++ lv ++ ")"
  | .indexGet _ name idx _len => do
      let iv ← loadVal p paramPrefix paramCount idx
      let base ←
        match p.slots.find? (fun s => s.name == name ++ "_0" || s.name == name) with
        | some s => pure s.index
        | none =>
          match p.slots.find? (fun s => s.name.endsWith "_0") with
          | some s => pure s.index
          | none => throw s!"extract/unsupported: unknown vector {name}"
      return "sload(add(" ++ toString base ++ ", " ++ iv ++ "))"
  | .loopIx => .ok "i"
  | .addU64 .. | .subU64 .. | .mapGetU64 .. | .mapGetAddr .. | .mapGetPair .. =>
      .error "extract/unsupported: evm map/arith val needs materialize"

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

private def revertNamed (indent name : String) : String :=
  let sel := Keccak.selector name #[]
  indent ++ "mstore(0, shl(224, 0x" ++ sel ++ "))" ++ nl ++
    indent ++ "revert(0, 4)" ++ nl

private def returnU64Count (ops : Array Ops.Op) : Nat :=
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
  loopIx : Option String := none

private def vectorLen (p : IR.Program) (name : String) (given : Nat) : Nat :=
  if given ≠ 0 then given
  else
    let pre := name ++ "_"
    p.slots.foldl (init := 0) fun acc s =>
      if s.name.startsWith pre then acc + 1 else acc

private def fresh (r : Render) : String × Render :=
  (s!"v{r.next}", { r with next := r.next + 1 })

private def bindChecked (indent name expr : String) : String :=
  indent ++ "let " ++ name ++ " := " ++ expr ++ nl ++
    indent ++ "if gt(" ++ name ++ ", " ++ u64MaxYul ++ ") { " ++ revert0 ++ " }" ++ nl

/-- 环境 opcode / 移位 / 下标必须先检查再当值用。 -/
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
    match v with
    | .shiftL l r | .shiftR l r =>
        let (preR, rv, st1) ← materializeVal p indent paramPrefix paramCount r st
        let (preL, lv, st2) ← materializeVal p indent paramPrefix paramCount l st1
        let (nm, st3) := fresh st2
        let op := if match v with | .shiftL .. => true | _ => false then "shl" else "shr"
        let txt := preR ++ preL ++
          indent ++ "if gt(" ++ rv ++ ", 63) { " ++ revert0 ++ " }" ++ nl ++
          indent ++ "let " ++ nm ++ " := " ++ op ++ "(" ++ rv ++ ", " ++ lv ++ ")" ++ nl
        return (txt, nm, st3)
    | .indexGet _ name idx len =>
        let (pre, iv, st1) ←
          match idx with
          | .loopIx =>
              pure ("", st.loopIx.getD "i", st)
          | _ => materializeVal p indent paramPrefix paramCount idx st
        let base ←
          match p.slots.find? (fun s => s.name == name ++ "_0" || s.name == name) with
          | some s => pure s.index
          | none =>
            match p.slots.find? (fun s => s.name.endsWith "_0") with
            | some s => pure s.index
            | none => throw s!"extract/unsupported: unknown vector {name}"
        let (nm, st2) := fresh st1
        let bound := toString (vectorLen p name len)
        let txt := pre ++
          indent ++ "if iszero(lt(" ++ iv ++ ", " ++ bound ++ ")) { " ++ revert0 ++ " }" ++ nl ++
          indent ++ "let " ++ nm ++ " := sload(add(" ++ toString base ++ ", " ++ iv ++ "))" ++ nl
        return (txt, nm, st2)
    | .loopIx =>
        return ("", st.loopIx.getD "i", st)
    | .addU64 l r =>
        let (preL, lv, st1) ← materializeVal p indent paramPrefix paramCount l st
        let (preR, rv, st2) ← materializeVal p indent paramPrefix paramCount r st1
        let (nm, st3) := fresh st2
        let txt := preL ++ preR ++
          indent ++ "if gt(" ++ lv ++ ", sub(" ++ u64MaxYul ++ ", " ++ rv ++
            ")) { " ++ revert0 ++ " }" ++ nl ++
          indent ++ "let " ++ nm ++ " := add(" ++ lv ++ ", " ++ rv ++ ")" ++ nl
        return (txt, nm, st3)
    | .subU64 l r =>
        let (preL, lv, st1) ← materializeVal p indent paramPrefix paramCount l st
        let (preR, rv, st2) ← materializeVal p indent paramPrefix paramCount r st1
        let (nm, st3) := fresh st2
        let txt := preL ++ preR ++
          indent ++ "if lt(" ++ lv ++ ", " ++ rv ++ ") { " ++ revert0 ++ " }" ++ nl ++
          indent ++ "let " ++ nm ++ " := sub(" ++ lv ++ ", " ++ rv ++ ")" ++ nl
        return (txt, nm, st3)
    | .mapGetU64 base key =>
        let (pb, b, st1) ← materializeVal p indent paramPrefix paramCount base st
        let (pk, k, st2) ← materializeVal p indent paramPrefix paramCount key st1
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
    | .mapGetAddr base w0 w1 w2 =>
        let (pb, b, st1) ← materializeVal p indent paramPrefix paramCount base st
        let (p0, a0, st2) ← materializeVal p indent paramPrefix paramCount w0 st1
        let (p1, a1, st3) ← materializeVal p indent paramPrefix paramCount w1 st2
        let (p2, a2, st4) ← materializeVal p indent paramPrefix paramCount w2 st3
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
    | .mapGetPair base o0 o1 o2 s0 s1 s2 =>
        let (pb, b, st1) ← materializeVal p indent paramPrefix paramCount base st
        let (p0, a0, st2) ← materializeVal p indent paramPrefix paramCount o0 st1
        let (p1, a1, st3) ← materializeVal p indent paramPrefix paramCount o1 st2
        let (p2, a2, st4) ← materializeVal p indent paramPrefix paramCount o2 st3
        let (q0, b0, st5) ← materializeVal p indent paramPrefix paramCount s0 st4
        let (q1, b1, st6) ← materializeVal p indent paramPrefix paramCount s1 st5
        let (q2, b2, st7) ← materializeVal p indent paramPrefix paramCount s2 st6
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
    | _ =>
        let e ← loadVal p paramPrefix paramCount v
        return ("", e, st)

private def brace (inner : String) : String :=
  "{" ++ nl ++ inner ++ "}"

private partial def emitOps (p : IR.Program) (indent paramPrefix : String)
    (paramCount : Nat) (ops : Array Ops.Op) (st : Render) :
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
        let (preL, lv, stL) ← materializeVal p indent paramPrefix paramCount l st
        let (preR, rv, stR) ← materializeVal p indent paramPrefix paramCount r stL
        let (nm, st') := fresh stR
        st := st'
        let (thenTxt, st1) ← emitOps p (indent ++ "  ") paramPrefix paramCount thn st
        let (elseTxt, st2) ← emitOps p (indent ++ "  ") paramPrefix paramCount els st1
        st := { st2 with last := none }
        acc := acc ++ preL ++ preR ++
          indent ++ "let " ++ nm ++ " := " ++ cmpYul c lv rv ++ nl ++
          indent ++ "if " ++ nm ++ " " ++ brace thenTxt ++ nl ++
          indent ++ "if iszero(" ++ nm ++ ") " ++ brace elseTxt ++ nl
    | .invoke .. =>
        throw "extract/unsupported: evm rejects svm leaf"
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
    | .evmLog name amount =>
        let (pre, amt, st') ← materializeVal p indent paramPrefix paramCount amount st
        st := st'
        acc := acc ++ pre ++
          indent ++ "mstore(0, " ++ amt ++ ")" ++ nl ++
          indent ++ "log1(0, 32, 0x" ++
            Keccak.keccak256HexOfString (name ++ "(uint64)") ++ ")" ++ nl
        st := { st with last := some amt }
    | .forAccum n addend =>
        let (accN, st1) := fresh st
        let (iN, st2) := fresh st1
        let innerSt := { st2 with loopIx := some iN }
        let (pre, addE, st3) ←
          materializeVal p (indent ++ "  ") paramPrefix paramCount addend innerSt
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
    | .indexSet name idx value len =>
        let (preI, iv, st1) ← materializeVal p indent paramPrefix paramCount idx st
        let (preV, vv, st2) ← materializeVal p indent paramPrefix paramCount value st1
        st := st2
        let base ←
          match p.slots.find? (fun s => s.name == name ++ "_0" || s.name == name) with
          | some s => pure s.index
          | none =>
            match p.slots.find? (fun s => s.name.endsWith "_0") with
            | some s => pure s.index
            | none => throw s!"extract/unsupported: unknown vector {name}"
        let bound := toString (vectorLen p name len)
        acc := acc ++ preI ++ preV ++
          indent ++ "if iszero(lt(" ++ iv ++ ", " ++ bound ++ ")) { " ++ revert0 ++ " }" ++ nl ++
          indent ++ "sstore(add(" ++ toString base ++ ", " ++ iv ++ "), " ++ vv ++ ")" ++ nl
        st := { st with last := some vv }
    | .mapGetU64 base key =>
        let (pb, b, st1) ← materializeVal p indent paramPrefix paramCount base st
        let (pk, k, st2) ← materializeVal p indent paramPrefix paramCount key st1
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
        let (pb, b, st1) ← materializeVal p indent paramPrefix paramCount base st
        let (pk, k, st2) ← materializeVal p indent paramPrefix paramCount key st1
        let (pv, v, st3) ← materializeVal p indent paramPrefix paramCount value st2
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
        let (pb, b, st1) ← materializeVal p indent paramPrefix paramCount base st
        let (p0, a0, st2) ← materializeVal p indent paramPrefix paramCount w0 st1
        let (p1, a1, st3) ← materializeVal p indent paramPrefix paramCount w1 st2
        let (p2, a2, st4) ← materializeVal p indent paramPrefix paramCount w2 st3
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
        let (pb, b, st1) ← materializeVal p indent paramPrefix paramCount base st
        let (p0, a0, st2) ← materializeVal p indent paramPrefix paramCount w0 st1
        let (p1, a1, st3) ← materializeVal p indent paramPrefix paramCount w1 st2
        let (p2, a2, st4) ← materializeVal p indent paramPrefix paramCount w2 st3
        let (pv, v, st5) ← materializeVal p indent paramPrefix paramCount value st4
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
        let (pb, b, st1) ← materializeVal p indent paramPrefix paramCount base st
        let (p0, a0, st2) ← materializeVal p indent paramPrefix paramCount o0 st1
        let (p1, a1, st3) ← materializeVal p indent paramPrefix paramCount o1 st2
        let (p2, a2, st4) ← materializeVal p indent paramPrefix paramCount o2 st3
        let (q0, b0, st5) ← materializeVal p indent paramPrefix paramCount s0 st4
        let (q1, b1, st6) ← materializeVal p indent paramPrefix paramCount s1 st5
        let (q2, b2, st7) ← materializeVal p indent paramPrefix paramCount s2 st6
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
        let (pb, b, st1) ← materializeVal p indent paramPrefix paramCount base st
        let (p0, a0, st2) ← materializeVal p indent paramPrefix paramCount o0 st1
        let (p1, a1, st3) ← materializeVal p indent paramPrefix paramCount o1 st2
        let (p2, a2, st4) ← materializeVal p indent paramPrefix paramCount o2 st3
        let (q0, b0, st5) ← materializeVal p indent paramPrefix paramCount s0 st4
        let (q1, b1, st6) ← materializeVal p indent paramPrefix paramCount s1 st5
        let (q2, b2, st7) ← materializeVal p indent paramPrefix paramCount s2 st6
        let (pv, v, st8) ← materializeVal p indent paramPrefix paramCount value st7
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
    | .evmTokenTransfer tw0 tw1 tw2 dw0 dw1 dw2 amount =>
        let (p0, a0, s0) ← materializeVal p indent paramPrefix paramCount tw0 st
        let (p1, a1, s1) ← materializeVal p indent paramPrefix paramCount tw1 s0
        let (p2, a2, s2) ← materializeVal p indent paramPrefix paramCount tw2 s1
        let (q0, d0, s3) ← materializeVal p indent paramPrefix paramCount dw0 s2
        let (q1, d1, s4) ← materializeVal p indent paramPrefix paramCount dw1 s3
        let (q2, d2, s5) ← materializeVal p indent paramPrefix paramCount dw2 s4
        let (pa, amt, s6) ← materializeVal p indent paramPrefix paramCount amount s5
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
    | .evmTokenBalanceOfSelf tw0 tw1 tw2 =>
        let (p0, a0, s0) ← materializeVal p indent paramPrefix paramCount tw0 st
        let (p1, a1, s1) ← materializeVal p indent paramPrefix paramCount tw1 s0
        let (p2, a2, s2) ← materializeVal p indent paramPrefix paramCount tw2 s1
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
    | .okState v =>
        if Ops.hasIndexSet ops then
          let value := st.last.getD "0"
          acc := acc ++ returnWord indent value
        else if IR.hasOptionLeaves p then
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
    | .errorNamed name =>
        acc := acc ++ revertNamed indent name
    | .returnU64 v =>
        let (pre, value, st') ←
          match st.last with
          | some nm => pure ("", nm, { st with last := none })
          | none => materializeVal p indent paramPrefix paramCount v st
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
    let w := (m.paramWidths[i]?).getD 8
    let max := widthMask w
    head := head ++
      "        let arg" ++ toString i ++ " := calldataload(" ++ toString off ++ ")" ++ nl ++
      "        if gt(arg" ++ toString i ++ ", " ++ max ++ ") { " ++
        revert0 ++ " }" ++ nl
  let (body, _) ←
    match emitOps p "        " "arg" m.paramCount m.ops {} with
    | .ok pair => pure pair
    | .error reason => throw s!"{reason} in {m.ixName}"
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
    "// PROOF-FORGE-EVM-YUL v0" ++ nl ++
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
  if m.retCount ≤ 1 then
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
  "{\"type\":\"event\",\"name\":\"" ++ escapeJson name ++
    "\",\"inputs\":[{\"name\":\"amt\",\"type\":\"uint64\",\"indexed\":false}],\"anonymous\":false}"

private def collectLogNames (fuel : Nat) (ops : Array Ops.Op) : Array String :=
  match fuel with
  | 0 => #[]
  | fuel' + 1 =>
    ops.foldl (init := #[]) fun acc op =>
      match op with
      | .evmLog n _ => if acc.contains n then acc else acc.push n
      | .ite _ _ _ t f =>
        (collectLogNames fuel' t ++ collectLogNames fuel' f).foldl (init := acc) fun acc n =>
          if acc.contains n then acc else acc.push n
      | _ => acc

def emitAbi (p : IR.Program) : String :=
  let evs :=
    p.entries.foldl (init := #[]) fun acc m =>
      (collectLogNames 8 m.ops).foldl (init := acc) fun acc n =>
        if acc.contains n then acc else acc.push n
  let items := #[ctorAbi p] ++ evs.map eventAbi ++ p.entries.map entryAbi
  "[\n  " ++ String.intercalate ",\n  " items.toList ++ "\n]\n"

def emit (p : IR.Program) : Except String (String × String) := do
  let yul ← emitYul p
  return (yul, emitAbi p)

end ProofForge.Evm.Emit
