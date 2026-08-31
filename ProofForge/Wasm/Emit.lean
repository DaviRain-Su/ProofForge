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

private def extLocal (tag : ValExt → String) (kind : ValExt) : String :=
  "pf_x_" ++ tag kind

/-- Hash-lit seeds are spelled `xsha.{seed}` by XRPL `extValCanon`. -/
private def sha512Seed? (tag : String) : Option String :=
  if tag.startsWith "xsha." then some (tag.drop "xsha.".length |>.copy) else none

/-- Compile-time AccountID limbs: `xacc0.{hex}` / `xacc1.{hex}` / `xacc2.{hex}`. -/
private def accountLitLimb? (tag : String) : Option UInt64 :=
  let rec nibble (c : Char) : Option Nat :=
    let n := c.toNat
    if n ≥ 48 && n ≤ 57 then some (n - 48)
    else if n ≥ 97 && n ≤ 102 then some (n - 87)
    else if n ≥ 65 && n ≤ 70 then some (n - 55)
    else none
  let rec bytes (cs : List Char) (acc : Array Nat) : Option (Array Nat) :=
    match cs with
    | c0 :: c1 :: rest =>
      match nibble c0, nibble c1 with
      | some hi, some lo => bytes rest (acc.push (hi * 16 + lo))
      | _, _ => none
    | [] => some acc
    | _ => none
  let rec leU64 (bs : Array Nat) (off len : Nat) : UInt64 :=
    UInt64.ofNat ((Array.range len).foldl (fun a i =>
      a + bs[off + i]! * (256 ^ i)
    ) 0)
  if tag.startsWith "xacc0." || tag.startsWith "xacc1." || tag.startsWith "xacc2." then
    let hex := String.ofList (tag.toList.drop 6)
    match bytes hex.toList #[] with
    | some bs =>
      if bs.size != 20 then none
      else if tag.startsWith "xacc0." then some (leU64 bs 0 8)
      else if tag.startsWith "xacc1." then some (leU64 bs 8 8)
      else some (leU64 bs 16 4)
    | none => none
  else none

private partial def renderVal (host : Contract) (extTag : ValExt → String) (st : EState)
    (v : Val ValExt) : Except String String :=
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
      let l ← renderVal host extTag st lhs
      let r ← renderVal host extTag st rhs
      let t ← renderVal host extTag st thn
      let f ← renderVal host extTag st els
      return ("(if (result i64) (" ++ cmpInstr cmp ++ " " ++ l ++ " " ++ r ++
        ") (then " ++ t ++ ") (else " ++ f ++ "))")
  | .addU64 lhs rhs => do
      let l ← renderVal host extTag st lhs
      let r ← renderVal host extTag st rhs
      return ("(i64.add " ++ l ++ " " ++ r ++ ")")
  | .subU64 lhs rhs => do
      let l ← renderVal host extTag st lhs
      let r ← renderVal host extTag st rhs
      return ("(i64.sub " ++ l ++ " " ++ r ++ ")")
  | .mulU64 lhs rhs => do
      let l ← renderVal host extTag st lhs
      let r ← renderVal host extTag st rhs
      return ("(i64.mul " ++ l ++ " " ++ r ++ ")")
  | .ext kind operands => do
      match sha512Seed? (extTag kind) with
      | some seed =>
          -- Seed at 96, 32-byte digest at 160. First little-endian i64 is the leaf.
          let stores := String.join (seed.toList.mapIdx fun i c =>
            "(i32.store8 (i32.const " ++ toString (96 + i) ++
            ") (i32.const " ++ toString c.toNat ++ ")) ")
          return ("(block (result i64) " ++ stores ++
            "(drop (call $" ++ host.computeSha512Half ++ " (i32.const 96) (i32.const " ++
              toString seed.length ++
              ") (i32.const 160) (i32.const 32))) (i64.load (i32.const 160)))")
      | none =>
        match accountLitLimb? (extTag kind) with
        | some n => return ("(i64.const " ++ toString n.toNat ++ ")")
        | none =>
          let tag := extTag kind
          if tag.startsWith "xlitbal." then
            return "(local.get $pf_x_xlitbal)"
          else if tag == "xsto" then
            unless operands.size = 3 do
              throw "extract/unsupported: storeOwner wants three limbs"
            let w0 ← renderVal host extTag st operands[0]!
            let w1 ← renderVal host extTag st operands[1]!
            let w2 ← renderVal host extTag st operands[2]!
            -- Rewrite persist Owner (mem[0..19]) then yield w2. i32.store
            -- at 16 keeps the 4-byte limb off the param scratch at 20.
            return ("(block (result i64) (i64.store (i32.const 0) " ++ w0 ++
              ") (i64.store (i32.const 8) " ++ w1 ++
              ") (i32.store (i32.const 16) (i32.wrap_i64 " ++ w2 ++
              ")) (i64.extend_i32_u (i32.load (i32.const 16))))")
          else if tag == "xflush" then
            unless operands.size = 1 do
              throw "extract/unsupported: flushBal wants one value"
            let v ← renderVal host extTag st operands[0]!
            -- Persist `$bal` onto the current Owner card, then yield `v`.
            -- Slot/key are the `bal` card (offset 64, length 3).
            let be := String.join ((Array.range 8).toList.map fun i =>
              let shift := (7 - i) * 8
              "(i32.store8 (i32.const " ++ toString (29 + i) ++
                ") (i32.wrap_i64 (i64.shr_u (local.get $bal) (i64.const " ++
                toString shift ++ ")))) ")
            return ("(block (result i64) (local.set $bal " ++ v ++
              ") (i32.store8 (i32.const 28) (i32.const " ++
              toString host.stiUint64 ++ ")) " ++ be ++
              "(local.set $st (call $" ++ host.setDataObject ++
              " (i32.const 0) (i32.const 20) (i32.const 64) (i32.const 3)" ++
              " (i32.const 28) (i32.const 9))) (if (i32.lt_s (local.get $st)" ++
              " (i32.const 0)) (then (return (local.get $st)))) (local.get $bal))")
          else if tag == "xpeek" then
            unless operands.size = 3 do
              throw "extract/unsupported: peekOwner wants three limbs"
            let w0 ← renderVal host extTag st operands[0]!
            let w1 ← renderVal host extTag st operands[1]!
            let w2 ← renderVal host extTag st operands[2]!
            let eqs := host.missingFields.foldl (fun acc (code : Int) =>
              let eq := "(i32.eq (local.get $st) (i32.const " ++ toString code ++ "))"
              if acc.isEmpty then eq else "(i32.or " ++ acc ++ " " ++ eq ++ ")") ""
            let missing := if eqs.isEmpty then "(i32.const 0)" else eqs
            return ("(block (result i64) (i64.store (i32.const 0) " ++ w0 ++
              ") (i64.store (i32.const 8) " ++ w1 ++
              ") (i32.store (i32.const 16) (i32.wrap_i64 " ++ w2 ++
              ")) (local.set $st (call $" ++ host.getDataObject ++
              " (i32.const 0) (i32.const 20) (i32.const 64) (i32.const 3)" ++
              " (i32.const 28) (i32.const 8))) (if (result i64) (i32.lt_s" ++
              " (local.get $st) (i32.const 0)) (then (if (result i64) (i32.eqz " ++
              missing ++ ") (then (return (local.get $st))) (else (i64.const 0))))" ++
              " (else (if (result i64) (i32.gt_s (local.get $st) (i32.const 0))" ++
              " (then (i64.or (i64.shl (i64.or (i64.shl (i64.or (i64.shl (i64.or (i64.shl (i64.or (i64.shl (i64.or (i64.shl (i64.or (i64.shl (i64.extend_i32_u (i32.load8_u (i32.const 28))) (i64.const 8)) (i64.extend_i32_u (i32.load8_u (i32.const 29)))) (i64.const 8)) (i64.extend_i32_u (i32.load8_u (i32.const 30)))) (i64.const 8)) (i64.extend_i32_u (i32.load8_u (i32.const 31)))) (i64.const 8)) (i64.extend_i32_u (i32.load8_u (i32.const 32)))) (i64.const 8)) (i64.extend_i32_u (i32.load8_u (i32.const 33)))) (i64.const 8)) (i64.extend_i32_u (i32.load8_u (i32.const 34)))) (i64.const 8)) (i64.extend_i32_u (i32.load8_u (i32.const 35)))))" ++
              " (else (i64.const 0))))))")
          else if tag == "xflushh" then
            unless operands.size = 1 do
              throw "extract/unsupported: flushHalt wants one value"
            let v ← renderVal host extTag st operands[0]!
            -- Key `halt` at 80. Value scratch at 40 so `$bal` is not clobbered.
            let be := String.join ((Array.range 8).toList.map fun i =>
              let shift := (7 - i) * 8
              "(i32.store8 (i32.const " ++ toString (29 + i) ++
                ") (i32.wrap_i64 (i64.shr_u (i64.load (i32.const 40)) (i64.const " ++
                toString shift ++ ")))) ")
            return ("(block (result i64) (i64.store (i32.const 40) " ++ v ++
              ") (i32.store8 (i32.const 80) (i32.const 104))" ++
              " (i32.store8 (i32.const 81) (i32.const 97))" ++
              " (i32.store8 (i32.const 82) (i32.const 108))" ++
              " (i32.store8 (i32.const 83) (i32.const 116))" ++
              " (i32.store8 (i32.const 28) (i32.const " ++
              toString host.stiUint64 ++ ")) " ++ be ++
              "(local.set $st (call $" ++ host.setDataObject ++
              " (i32.const 0) (i32.const 20) (i32.const 80) (i32.const 4)" ++
              " (i32.const 28) (i32.const 9))) (if (i32.lt_s (local.get $st)" ++
              " (i32.const 0)) (then (return (local.get $st)))) (i64.load (i32.const 40)))")
          else if tag == "xpeelh" then
            unless operands.size = 3 do
              throw "extract/unsupported: peekHalt wants three limbs"
            let w0 ← renderVal host extTag st operands[0]!
            let w1 ← renderVal host extTag st operands[1]!
            let w2 ← renderVal host extTag st operands[2]!
            let eqs := host.missingFields.foldl (fun acc (code : Int) =>
              let eq := "(i32.eq (local.get $st) (i32.const " ++ toString code ++ "))"
              if acc.isEmpty then eq else "(i32.or " ++ acc ++ " " ++ eq ++ ")") ""
            let missing := if eqs.isEmpty then "(i32.const 0)" else eqs
            return ("(block (result i64) (i64.store (i32.const 0) " ++ w0 ++
              ") (i64.store (i32.const 8) " ++ w1 ++
              ") (i32.store (i32.const 16) (i32.wrap_i64 " ++ w2 ++
              ")) (i32.store8 (i32.const 80) (i32.const 104))" ++
              " (i32.store8 (i32.const 81) (i32.const 97))" ++
              " (i32.store8 (i32.const 82) (i32.const 108))" ++
              " (i32.store8 (i32.const 83) (i32.const 116))" ++
              " (local.set $st (call $" ++ host.getDataObject ++
              " (i32.const 0) (i32.const 20) (i32.const 80) (i32.const 4)" ++
              " (i32.const 28) (i32.const 8))) (if (result i64) (i32.lt_s" ++
              " (local.get $st) (i32.const 0)) (then (if (result i64) (i32.eqz " ++
              missing ++ ") (then (return (local.get $st))) (else (i64.const 0))))" ++
              " (else (if (result i64) (i32.gt_s (local.get $st) (i32.const 0))" ++
              " (then (i64.or (i64.shl (i64.or (i64.shl (i64.or (i64.shl (i64.or (i64.shl (i64.or (i64.shl (i64.or (i64.shl (i64.or (i64.shl (i64.extend_i32_u (i32.load8_u (i32.const 28))) (i64.const 8)) (i64.extend_i32_u (i32.load8_u (i32.const 29)))) (i64.const 8)) (i64.extend_i32_u (i32.load8_u (i32.const 30)))) (i64.const 8)) (i64.extend_i32_u (i32.load8_u (i32.const 31)))) (i64.const 8)) (i64.extend_i32_u (i32.load8_u (i32.const 32)))) (i64.const 8)) (i64.extend_i32_u (i32.load8_u (i32.const 33)))) (i64.const 8)) (i64.extend_i32_u (i32.load8_u (i32.const 34)))) (i64.const 8)) (i64.extend_i32_u (i32.load8_u (i32.const 35)))))" ++
              " (else (i64.const 0))))))")
          else if tag == "xflushs" then
            unless operands.size = 1 do
              throw "extract/unsupported: flushSupp wants one value"
            let v ← renderVal host extTag st operands[0]!
            -- Key `supp` at 88. Value scratch at 48 so `$bal` / halt are not clobbered.
            let be := String.join ((Array.range 8).toList.map fun i =>
              let shift := (7 - i) * 8
              "(i32.store8 (i32.const " ++ toString (29 + i) ++
                ") (i32.wrap_i64 (i64.shr_u (i64.load (i32.const 48)) (i64.const " ++
                toString shift ++ ")))) ")
            return ("(block (result i64) (i64.store (i32.const 48) " ++ v ++
              ") (i32.store8 (i32.const 88) (i32.const 115))" ++
              " (i32.store8 (i32.const 89) (i32.const 117))" ++
              " (i32.store8 (i32.const 90) (i32.const 112))" ++
              " (i32.store8 (i32.const 91) (i32.const 112))" ++
              " (i32.store8 (i32.const 28) (i32.const " ++
              toString host.stiUint64 ++ ")) " ++ be ++
              "(local.set $st (call $" ++ host.setDataObject ++
              " (i32.const 0) (i32.const 20) (i32.const 88) (i32.const 4)" ++
              " (i32.const 28) (i32.const 9))) (if (i32.lt_s (local.get $st)" ++
              " (i32.const 0)) (then (return (local.get $st)))) (i64.load (i32.const 48)))")
          else if tag == "xflusha" then
            unless operands.size = 1 do
              throw "extract/unsupported: flushAllw wants one value"
            let v ← renderVal host extTag st operands[0]!
            -- Key `allw` at 92. Value scratch at 104 so persist Owner / `$bal` / halt / supp / cap stay.
            let be := String.join ((Array.range 8).toList.map fun i =>
              let shift := (7 - i) * 8
              "(i32.store8 (i32.const " ++ toString (29 + i) ++
                ") (i32.wrap_i64 (i64.shr_u (i64.load (i32.const 104)) (i64.const " ++
                toString shift ++ ")))) ")
            return ("(block (result i64) (i64.store (i32.const 104) " ++ v ++
              ") (i32.store8 (i32.const 92) (i32.const 97))" ++
              " (i32.store8 (i32.const 93) (i32.const 108))" ++
              " (i32.store8 (i32.const 94) (i32.const 108))" ++
              " (i32.store8 (i32.const 95) (i32.const 119))" ++
              " (i32.store8 (i32.const 28) (i32.const " ++
              toString host.stiUint64 ++ ")) " ++ be ++
              "(local.set $st (call $" ++ host.setDataObject ++
              " (i32.const 0) (i32.const 20) (i32.const 92) (i32.const 4)" ++
              " (i32.const 28) (i32.const 9))) (if (i32.lt_s (local.get $st)" ++
              " (i32.const 0)) (then (return (local.get $st)))) (i64.load (i32.const 104)))")
          else if tag == "xpeeka" then
            unless operands.size = 3 do
              throw "extract/unsupported: peekAllw wants three limbs"
            let w0 ← renderVal host extTag st operands[0]!
            let w1 ← renderVal host extTag st operands[1]!
            let w2 ← renderVal host extTag st operands[2]!
            let eqs := host.missingFields.foldl (fun acc (code : Int) =>
              let eq := "(i32.eq (local.get $st) (i32.const " ++ toString code ++ "))"
              if acc.isEmpty then eq else "(i32.or " ++ acc ++ " " ++ eq ++ ")") ""
            let missing := if eqs.isEmpty then "(i32.const 0)" else eqs
            return ("(block (result i64) (i64.store (i32.const 0) " ++ w0 ++
              ") (i64.store (i32.const 8) " ++ w1 ++
              ") (i32.store (i32.const 16) (i32.wrap_i64 " ++ w2 ++
              ")) (i32.store8 (i32.const 92) (i32.const 97))" ++
              " (i32.store8 (i32.const 93) (i32.const 108))" ++
              " (i32.store8 (i32.const 94) (i32.const 108))" ++
              " (i32.store8 (i32.const 95) (i32.const 119))" ++
              " (local.set $st (call $" ++ host.getDataObject ++
              " (i32.const 0) (i32.const 20) (i32.const 92) (i32.const 4)" ++
              " (i32.const 28) (i32.const 8))) (if (result i64) (i32.lt_s" ++
              " (local.get $st) (i32.const 0)) (then (if (result i64) (i32.eqz " ++
              missing ++ ") (then (return (local.get $st))) (else (i64.const 0))))" ++
              " (else (if (result i64) (i32.gt_s (local.get $st) (i32.const 0))" ++
              " (then (i64.or (i64.shl (i64.or (i64.shl (i64.or (i64.shl (i64.or (i64.shl (i64.or (i64.shl (i64.or (i64.shl (i64.or (i64.shl (i64.extend_i32_u (i32.load8_u (i32.const 28))) (i64.const 8)) (i64.extend_i32_u (i32.load8_u (i32.const 29)))) (i64.const 8)) (i64.extend_i32_u (i32.load8_u (i32.const 30)))) (i64.const 8)) (i64.extend_i32_u (i32.load8_u (i32.const 31)))) (i64.const 8)) (i64.extend_i32_u (i32.load8_u (i32.const 32)))) (i64.const 8)) (i64.extend_i32_u (i32.load8_u (i32.const 33)))) (i64.const 8)) (i64.extend_i32_u (i32.load8_u (i32.const 34)))) (i64.const 8)) (i64.extend_i32_u (i32.load8_u (i32.const 35)))))" ++
              " (else (i64.const 0))))))")
          else if tag == "xflushl" then
            unless operands.size = 1 do
              throw "extract/unsupported: flushLock wants one value"
            let v ← renderVal host extTag st operands[0]!
            -- Key `lock` at 96. Value scratch at 112 so persist Owner / `$bal` / halt / supp / cap / allw stay.
            let be := String.join ((Array.range 8).toList.map fun i =>
              let shift := (7 - i) * 8
              "(i32.store8 (i32.const " ++ toString (29 + i) ++
                ") (i32.wrap_i64 (i64.shr_u (i64.load (i32.const 112)) (i64.const " ++
                toString shift ++ ")))) ")
            return ("(block (result i64) (i64.store (i32.const 112) " ++ v ++
              ") (i32.store8 (i32.const 96) (i32.const 108))" ++
              " (i32.store8 (i32.const 97) (i32.const 111))" ++
              " (i32.store8 (i32.const 98) (i32.const 99))" ++
              " (i32.store8 (i32.const 99) (i32.const 107))" ++
              " (i32.store8 (i32.const 28) (i32.const " ++
              toString host.stiUint64 ++ ")) " ++ be ++
              "(local.set $st (call $" ++ host.setDataObject ++
              " (i32.const 0) (i32.const 20) (i32.const 96) (i32.const 4)" ++
              " (i32.const 28) (i32.const 9))) (if (i32.lt_s (local.get $st)" ++
              " (i32.const 0)) (then (return (local.get $st)))) (i64.load (i32.const 112)))")
          else if tag == "xpeekl" then
            unless operands.size = 3 do
              throw "extract/unsupported: peekLock wants three limbs"
            let w0 ← renderVal host extTag st operands[0]!
            let w1 ← renderVal host extTag st operands[1]!
            let w2 ← renderVal host extTag st operands[2]!
            let eqs := host.missingFields.foldl (fun acc (code : Int) =>
              let eq := "(i32.eq (local.get $st) (i32.const " ++ toString code ++ "))"
              if acc.isEmpty then eq else "(i32.or " ++ acc ++ " " ++ eq ++ ")") ""
            let missing := if eqs.isEmpty then "(i32.const 0)" else eqs
            return ("(block (result i64) (i64.store (i32.const 0) " ++ w0 ++
              ") (i64.store (i32.const 8) " ++ w1 ++
              ") (i32.store (i32.const 16) (i32.wrap_i64 " ++ w2 ++
              ")) (i32.store8 (i32.const 96) (i32.const 108))" ++
              " (i32.store8 (i32.const 97) (i32.const 111))" ++
              " (i32.store8 (i32.const 98) (i32.const 99))" ++
              " (i32.store8 (i32.const 99) (i32.const 107))" ++
              " (local.set $st (call $" ++ host.getDataObject ++
              " (i32.const 0) (i32.const 20) (i32.const 96) (i32.const 4)" ++
              " (i32.const 28) (i32.const 8))) (if (result i64) (i32.lt_s" ++
              " (local.get $st) (i32.const 0)) (then (if (result i64) (i32.eqz " ++
              missing ++ ") (then (return (local.get $st))) (else (i64.const 0))))" ++
              " (else (if (result i64) (i32.gt_s (local.get $st) (i32.const 0))" ++
              " (then (i64.or (i64.shl (i64.or (i64.shl (i64.or (i64.shl (i64.or (i64.shl (i64.or (i64.shl (i64.or (i64.shl (i64.or (i64.shl (i64.extend_i32_u (i32.load8_u (i32.const 28))) (i64.const 8)) (i64.extend_i32_u (i32.load8_u (i32.const 29)))) (i64.const 8)) (i64.extend_i32_u (i32.load8_u (i32.const 30)))) (i64.const 8)) (i64.extend_i32_u (i32.load8_u (i32.const 31)))) (i64.const 8)) (i64.extend_i32_u (i32.load8_u (i32.const 32)))) (i64.const 8)) (i64.extend_i32_u (i32.load8_u (i32.const 33)))) (i64.const 8)) (i64.extend_i32_u (i32.load8_u (i32.const 34)))) (i64.const 8)) (i64.extend_i32_u (i32.load8_u (i32.const 35)))))" ++
              " (else (i64.const 0))))))")
          else if tag == "xflushe" then
            unless operands.size = 1 do
              throw "extract/unsupported: flushEsc wants one value"
            let v ← renderVal host extTag st operands[0]!
            -- Key `esc` at 100. Value scratch at 120 so persist Owner / `$bal` / halt / supp / cap / allw / lock stay.
            let be := String.join ((Array.range 8).toList.map fun i =>
              let shift := (7 - i) * 8
              "(i32.store8 (i32.const " ++ toString (29 + i) ++
                ") (i32.wrap_i64 (i64.shr_u (i64.load (i32.const 120)) (i64.const " ++
                toString shift ++ ")))) ")
            return ("(block (result i64) (i64.store (i32.const 120) " ++ v ++
              ") (i32.store8 (i32.const 100) (i32.const 101))" ++
              " (i32.store8 (i32.const 101) (i32.const 115))" ++
              " (i32.store8 (i32.const 102) (i32.const 99))" ++
              " (i32.store8 (i32.const 28) (i32.const " ++
              toString host.stiUint64 ++ ")) " ++ be ++
              "(local.set $st (call $" ++ host.setDataObject ++
              " (i32.const 0) (i32.const 20) (i32.const 100) (i32.const 3)" ++
              " (i32.const 28) (i32.const 9))) (if (i32.lt_s (local.get $st)" ++
              " (i32.const 0)) (then (return (local.get $st)))) (i64.load (i32.const 120)))")
          else if tag == "xpeeke" then
            unless operands.size = 3 do
              throw "extract/unsupported: peekEsc wants three limbs"
            let w0 ← renderVal host extTag st operands[0]!
            let w1 ← renderVal host extTag st operands[1]!
            let w2 ← renderVal host extTag st operands[2]!
            let eqs := host.missingFields.foldl (fun acc (code : Int) =>
              let eq := "(i32.eq (local.get $st) (i32.const " ++ toString code ++ "))"
              if acc.isEmpty then eq else "(i32.or " ++ acc ++ " " ++ eq ++ ")") ""
            let missing := if eqs.isEmpty then "(i32.const 0)" else eqs
            return ("(block (result i64) (i64.store (i32.const 0) " ++ w0 ++
              ") (i64.store (i32.const 8) " ++ w1 ++
              ") (i32.store (i32.const 16) (i32.wrap_i64 " ++ w2 ++
              ")) (i32.store8 (i32.const 100) (i32.const 101))" ++
              " (i32.store8 (i32.const 101) (i32.const 115))" ++
              " (i32.store8 (i32.const 102) (i32.const 99))" ++
              " (local.set $st (call $" ++ host.getDataObject ++
              " (i32.const 0) (i32.const 20) (i32.const 100) (i32.const 3)" ++
              " (i32.const 28) (i32.const 8))) (if (result i64) (i32.lt_s" ++
              " (local.get $st) (i32.const 0)) (then (if (result i64) (i32.eqz " ++
              missing ++ ") (then (return (local.get $st))) (else (i64.const 0))))" ++
              " (else (if (result i64) (i32.gt_s (local.get $st) (i32.const 0))" ++
              " (then (i64.or (i64.shl (i64.or (i64.shl (i64.or (i64.shl (i64.or (i64.shl (i64.or (i64.shl (i64.or (i64.shl (i64.or (i64.shl (i64.extend_i32_u (i32.load8_u (i32.const 28))) (i64.const 8)) (i64.extend_i32_u (i32.load8_u (i32.const 29)))) (i64.const 8)) (i64.extend_i32_u (i32.load8_u (i32.const 30)))) (i64.const 8)) (i64.extend_i32_u (i32.load8_u (i32.const 31)))) (i64.const 8)) (i64.extend_i32_u (i32.load8_u (i32.const 32)))) (i64.const 8)) (i64.extend_i32_u (i32.load8_u (i32.const 33)))) (i64.const 8)) (i64.extend_i32_u (i32.load8_u (i32.const 34)))) (i64.const 8)) (i64.extend_i32_u (i32.load8_u (i32.const 35)))))" ++
              " (else (i64.const 0))))))")
          else if tag == "xflushd" then
            unless operands.size = 1 do
              throw "extract/unsupported: flushDue wants one value"
            let v ← renderVal host extTag st operands[0]!
            -- Key `due` at 76. Value scratch at 128 so persist Owner / `$bal` / halt / supp / cap / allw / lock / esc stay.
            let be := String.join ((Array.range 8).toList.map fun i =>
              let shift := (7 - i) * 8
              "(i32.store8 (i32.const " ++ toString (29 + i) ++
                ") (i32.wrap_i64 (i64.shr_u (i64.load (i32.const 128)) (i64.const " ++
                toString shift ++ ")))) ")
            return ("(block (result i64) (i64.store (i32.const 128) " ++ v ++
              ") (i32.store8 (i32.const 76) (i32.const 100))" ++
              " (i32.store8 (i32.const 77) (i32.const 117))" ++
              " (i32.store8 (i32.const 78) (i32.const 101))" ++
              " (i32.store8 (i32.const 28) (i32.const " ++
              toString host.stiUint64 ++ ")) " ++ be ++
              "(local.set $st (call $" ++ host.setDataObject ++
              " (i32.const 0) (i32.const 20) (i32.const 76) (i32.const 3)" ++
              " (i32.const 28) (i32.const 9))) (if (i32.lt_s (local.get $st)" ++
              " (i32.const 0)) (then (return (local.get $st)))) (i64.load (i32.const 128)))")
          else if tag == "xpeekd" then
            unless operands.size = 3 do
              throw "extract/unsupported: peekDue wants three limbs"
            let w0 ← renderVal host extTag st operands[0]!
            let w1 ← renderVal host extTag st operands[1]!
            let w2 ← renderVal host extTag st operands[2]!
            let eqs := host.missingFields.foldl (fun acc (code : Int) =>
              let eq := "(i32.eq (local.get $st) (i32.const " ++ toString code ++ "))"
              if acc.isEmpty then eq else "(i32.or " ++ acc ++ " " ++ eq ++ ")") ""
            let missing := if eqs.isEmpty then "(i32.const 0)" else eqs
            return ("(block (result i64) (i64.store (i32.const 0) " ++ w0 ++
              ") (i64.store (i32.const 8) " ++ w1 ++
              ") (i32.store (i32.const 16) (i32.wrap_i64 " ++ w2 ++
              ")) (i32.store8 (i32.const 76) (i32.const 100))" ++
              " (i32.store8 (i32.const 77) (i32.const 117))" ++
              " (i32.store8 (i32.const 78) (i32.const 101))" ++
              " (local.set $st (call $" ++ host.getDataObject ++
              " (i32.const 0) (i32.const 20) (i32.const 76) (i32.const 3)" ++
              " (i32.const 28) (i32.const 8))) (if (result i64) (i32.lt_s" ++
              " (local.get $st) (i32.const 0)) (then (if (result i64) (i32.eqz " ++
              missing ++ ") (then (return (local.get $st))) (else (i64.const 0))))" ++
              " (else (if (result i64) (i32.gt_s (local.get $st) (i32.const 0))" ++
              " (then (i64.or (i64.shl (i64.or (i64.shl (i64.or (i64.shl (i64.or (i64.shl (i64.or (i64.shl (i64.or (i64.shl (i64.or (i64.shl (i64.extend_i32_u (i32.load8_u (i32.const 28))) (i64.const 8)) (i64.extend_i32_u (i32.load8_u (i32.const 29)))) (i64.const 8)) (i64.extend_i32_u (i32.load8_u (i32.const 30)))) (i64.const 8)) (i64.extend_i32_u (i32.load8_u (i32.const 31)))) (i64.const 8)) (i64.extend_i32_u (i32.load8_u (i32.const 32)))) (i64.const 8)) (i64.extend_i32_u (i32.load8_u (i32.const 33)))) (i64.const 8)) (i64.extend_i32_u (i32.load8_u (i32.const 34)))) (i64.const 8)) (i64.extend_i32_u (i32.load8_u (i32.const 35)))))" ++
              " (else (i64.const 0))))))")
          else if tag == "xflushc" then
            unless operands.size = 1 do
              throw "extract/unsupported: flushCap wants one value"
            let v ← renderVal host extTag st operands[0]!
            -- Key `cap` at 72. Value scratch at 56 so `$bal` / halt / supp are not clobbered.
            let be := String.join ((Array.range 8).toList.map fun i =>
              let shift := (7 - i) * 8
              "(i32.store8 (i32.const " ++ toString (29 + i) ++
                ") (i32.wrap_i64 (i64.shr_u (i64.load (i32.const 56)) (i64.const " ++
                toString shift ++ ")))) ")
            return ("(block (result i64) (i64.store (i32.const 56) " ++ v ++
              ") (i32.store8 (i32.const 72) (i32.const 99))" ++
              " (i32.store8 (i32.const 73) (i32.const 97))" ++
              " (i32.store8 (i32.const 74) (i32.const 112))" ++
              " (i32.store8 (i32.const 28) (i32.const " ++
              toString host.stiUint64 ++ ")) " ++ be ++
              "(local.set $st (call $" ++ host.setDataObject ++
              " (i32.const 0) (i32.const 20) (i32.const 72) (i32.const 3)" ++
              " (i32.const 28) (i32.const 9))) (if (i32.lt_s (local.get $st)" ++
              " (i32.const 0)) (then (return (local.get $st)))) (i64.load (i32.const 56)))")
          else if tag == "xpeekc" then
            unless operands.size = 3 do
              throw "extract/unsupported: peekCap wants three limbs"
            let w0 ← renderVal host extTag st operands[0]!
            let w1 ← renderVal host extTag st operands[1]!
            let w2 ← renderVal host extTag st operands[2]!
            let eqs := host.missingFields.foldl (fun acc (code : Int) =>
              let eq := "(i32.eq (local.get $st) (i32.const " ++ toString code ++ "))"
              if acc.isEmpty then eq else "(i32.or " ++ acc ++ " " ++ eq ++ ")") ""
            let missing := if eqs.isEmpty then "(i32.const 0)" else eqs
            return ("(block (result i64) (i64.store (i32.const 0) " ++ w0 ++
              ") (i64.store (i32.const 8) " ++ w1 ++
              ") (i32.store (i32.const 16) (i32.wrap_i64 " ++ w2 ++
              ")) (i32.store8 (i32.const 72) (i32.const 99))" ++
              " (i32.store8 (i32.const 73) (i32.const 97))" ++
              " (i32.store8 (i32.const 74) (i32.const 112))" ++
              " (local.set $st (call $" ++ host.getDataObject ++
              " (i32.const 0) (i32.const 20) (i32.const 72) (i32.const 3)" ++
              " (i32.const 28) (i32.const 8))) (if (result i64) (i32.lt_s" ++
              " (local.get $st) (i32.const 0)) (then (if (result i64) (i32.eqz " ++
              missing ++ ") (then (return (local.get $st))) (else (i64.const 0))))" ++
              " (else (if (result i64) (i32.gt_s (local.get $st) (i32.const 0))" ++
              " (then (i64.or (i64.shl (i64.or (i64.shl (i64.or (i64.shl (i64.or (i64.shl (i64.or (i64.shl (i64.or (i64.shl (i64.or (i64.shl (i64.extend_i32_u (i32.load8_u (i32.const 28))) (i64.const 8)) (i64.extend_i32_u (i32.load8_u (i32.const 29)))) (i64.const 8)) (i64.extend_i32_u (i32.load8_u (i32.const 30)))) (i64.const 8)) (i64.extend_i32_u (i32.load8_u (i32.const 31)))) (i64.const 8)) (i64.extend_i32_u (i32.load8_u (i32.const 32)))) (i64.const 8)) (i64.extend_i32_u (i32.load8_u (i32.const 33)))) (i64.const 8)) (i64.extend_i32_u (i32.load8_u (i32.const 34)))) (i64.const 8)) (i64.extend_i32_u (i32.load8_u (i32.const 35)))))" ++
              " (else (i64.const 0))))))")
          else if tag == "xpeeks" then
            unless operands.size = 3 do
              throw "extract/unsupported: peekSupp wants three limbs"
            let w0 ← renderVal host extTag st operands[0]!
            let w1 ← renderVal host extTag st operands[1]!
            let w2 ← renderVal host extTag st operands[2]!
            let eqs := host.missingFields.foldl (fun acc (code : Int) =>
              let eq := "(i32.eq (local.get $st) (i32.const " ++ toString code ++ "))"
              if acc.isEmpty then eq else "(i32.or " ++ acc ++ " " ++ eq ++ ")") ""
            let missing := if eqs.isEmpty then "(i32.const 0)" else eqs
            return ("(block (result i64) (i64.store (i32.const 0) " ++ w0 ++
              ") (i64.store (i32.const 8) " ++ w1 ++
              ") (i32.store (i32.const 16) (i32.wrap_i64 " ++ w2 ++
              ")) (i32.store8 (i32.const 88) (i32.const 115))" ++
              " (i32.store8 (i32.const 89) (i32.const 117))" ++
              " (i32.store8 (i32.const 90) (i32.const 112))" ++
              " (i32.store8 (i32.const 91) (i32.const 112))" ++
              " (local.set $st (call $" ++ host.getDataObject ++
              " (i32.const 0) (i32.const 20) (i32.const 88) (i32.const 4)" ++
              " (i32.const 28) (i32.const 8))) (if (result i64) (i32.lt_s" ++
              " (local.get $st) (i32.const 0)) (then (if (result i64) (i32.eqz " ++
              missing ++ ") (then (return (local.get $st))) (else (i64.const 0))))" ++
              " (else (if (result i64) (i32.gt_s (local.get $st) (i32.const 0))" ++
              " (then (i64.or (i64.shl (i64.or (i64.shl (i64.or (i64.shl (i64.or (i64.shl (i64.or (i64.shl (i64.or (i64.shl (i64.or (i64.shl (i64.extend_i32_u (i32.load8_u (i32.const 28))) (i64.const 8)) (i64.extend_i32_u (i32.load8_u (i32.const 29)))) (i64.const 8)) (i64.extend_i32_u (i32.load8_u (i32.const 30)))) (i64.const 8)) (i64.extend_i32_u (i32.load8_u (i32.const 31)))) (i64.const 8)) (i64.extend_i32_u (i32.load8_u (i32.const 32)))) (i64.const 8)) (i64.extend_i32_u (i32.load8_u (i32.const 33)))) (i64.const 8)) (i64.extend_i32_u (i32.load8_u (i32.const 34)))) (i64.const 8)) (i64.extend_i32_u (i32.load8_u (i32.const 35)))))" ++
              " (else (i64.const 0))))))")
          else if tag == "xpay" then
            if host.buildTxn.isEmpty || host.addTxnField.isEmpty ||
                host.emitBuiltTxn.isEmpty || host.getTxField.isEmpty then
              throw "extract/unsupported: emitPay wants build_txn"
            -- Local 2.6.1: Payment 192 drops to caller + NetworkID 63456.
            -- Public AlphaNet still tefBAD_AUTH -196. Scratch at 224+ so
            -- persist Owner / `$bal` stay. Txn index at 260.
            let nidStores :=
              if host.ledgerSqnBuffer then ""
              else
                "(i32.store8 (i32.const 256) (i32.const 0x00))" ++
                "(i32.store8 (i32.const 257) (i32.const 0x00))" ++
                "(i32.store8 (i32.const 258) (i32.const 0xF7))" ++
                "(i32.store8 (i32.const 259) (i32.const 0xE0))"
            let nidField :=
              if host.ledgerSqnBuffer then ""
              else
                " (local.set $st (call $" ++ host.addTxnField ++
                " (i32.load (i32.const 260)) (i32.const 131073) (i32.const 256) (i32.const 4)))" ++
                " (if (i32.lt_s (local.get $st) (i32.const 0))" ++
                " (then (return (local.get $st))))"
            return ("(block (result i64) (i32.store8 (i32.const 224) (i32.const 0x14))" ++
              " (local.set $st (call $" ++ host.getTxField ++
              " (i32.const " ++ toString host.sfieldTxAccount ++
              ") (i32.const 225) (i32.const 20))) (if (i32.lt_s (local.get $st)" ++
              " (i32.const 0)) (then (return (local.get $st))))" ++
              " (i32.store8 (i32.const 248) (i32.const 0x40))" ++
              " (i32.store8 (i32.const 249) (i32.const 0x00))" ++
              " (i32.store8 (i32.const 250) (i32.const 0x00))" ++
              " (i32.store8 (i32.const 251) (i32.const 0x00))" ++
              " (i32.store8 (i32.const 252) (i32.const 0x00))" ++
              " (i32.store8 (i32.const 253) (i32.const 0x00))" ++
              " (i32.store8 (i32.const 254) (i32.const 0x00))" ++
              " (i32.store8 (i32.const 255) (i32.const 0xC0)) " ++ nidStores ++
              " (local.set $st (call $" ++ host.buildTxn ++ " (i32.const 0)))" ++
              " (if (i32.lt_s (local.get $st) (i32.const 0))" ++
              " (then (return (local.get $st))))" ++
              " (i32.store (i32.const 260) (local.get $st))" ++
              " (local.set $st (call $" ++ host.addTxnField ++
              " (i32.load (i32.const 260)) (i32.const 393217) (i32.const 248) (i32.const 8)))" ++
              " (if (i32.lt_s (local.get $st) (i32.const 0))" ++
              " (then (return (local.get $st))))" ++
              " (local.set $st (call $" ++ host.addTxnField ++
              " (i32.load (i32.const 260)) (i32.const 524291) (i32.const 224) (i32.const 21)))" ++
              " (if (i32.lt_s (local.get $st) (i32.const 0))" ++
              " (then (return (local.get $st))))" ++ nidField ++
              " (local.set $st (call $" ++ host.emitBuiltTxn ++
              " (i32.load (i32.const 260))))" ++
              " (if (i32.lt_s (local.get $st) (i32.const 0))" ++
              " (then (return (local.get $st))))" ++
              " (i64.extend_i32_s (local.get $st)))")
          else if tag == "xpayd" then
            unless operands.size = 1 do
              throw "extract/unsupported: emitPayDrops wants one value"
            if host.buildTxn.isEmpty || host.addTxnField.isEmpty ||
                host.emitBuiltTxn.isEmpty || host.getTxField.isEmpty then
              throw "extract/unsupported: emitPayDrops wants build_txn"
            let drops ← renderVal host extTag st operands[0]!
            -- STAmount = 0x4000000000000000 | drops (57-bit mantissa). Scratch 224+.
            let nidStores :=
              if host.ledgerSqnBuffer then ""
              else
                "(i32.store8 (i32.const 256) (i32.const 0x00))" ++
                "(i32.store8 (i32.const 257) (i32.const 0x00))" ++
                "(i32.store8 (i32.const 258) (i32.const 0xF7))" ++
                "(i32.store8 (i32.const 259) (i32.const 0xE0))"
            let nidField :=
              if host.ledgerSqnBuffer then ""
              else
                " (local.set $st (call $" ++ host.addTxnField ++
                " (i32.load (i32.const 260)) (i32.const 131073) (i32.const 256) (i32.const 4)))" ++
                " (if (i32.lt_s (local.get $st) (i32.const 0))" ++
                " (then (return (local.get $st))))"
            return ("(block (result i64) (i32.store8 (i32.const 224) (i32.const 0x14))" ++
              " (local.set $st (call $" ++ host.getTxField ++
              " (i32.const " ++ toString host.sfieldTxAccount ++
              ") (i32.const 225) (i32.const 20))) (if (i32.lt_s (local.get $st)" ++
              " (i32.const 0)) (then (return (local.get $st))))" ++
              " (i64.store (i32.const 264) (i64.or (i64.const 4611686018427387904) " ++
              drops ++ "))" ++
              " (i32.store8 (i32.const 248) (i32.wrap_i64 (i64.shr_u (i64.load (i32.const 264)) (i64.const 56))))" ++
              " (i32.store8 (i32.const 249) (i32.wrap_i64 (i64.shr_u (i64.load (i32.const 264)) (i64.const 48))))" ++
              " (i32.store8 (i32.const 250) (i32.wrap_i64 (i64.shr_u (i64.load (i32.const 264)) (i64.const 40))))" ++
              " (i32.store8 (i32.const 251) (i32.wrap_i64 (i64.shr_u (i64.load (i32.const 264)) (i64.const 32))))" ++
              " (i32.store8 (i32.const 252) (i32.wrap_i64 (i64.shr_u (i64.load (i32.const 264)) (i64.const 24))))" ++
              " (i32.store8 (i32.const 253) (i32.wrap_i64 (i64.shr_u (i64.load (i32.const 264)) (i64.const 16))))" ++
              " (i32.store8 (i32.const 254) (i32.wrap_i64 (i64.shr_u (i64.load (i32.const 264)) (i64.const 8))))" ++
              " (i32.store8 (i32.const 255) (i32.wrap_i64 (i64.load (i32.const 264)))) " ++ nidStores ++
              " (local.set $st (call $" ++ host.buildTxn ++ " (i32.const 0)))" ++
              " (if (i32.lt_s (local.get $st) (i32.const 0))" ++
              " (then (return (local.get $st))))" ++
              " (i32.store (i32.const 260) (local.get $st))" ++
              " (local.set $st (call $" ++ host.addTxnField ++
              " (i32.load (i32.const 260)) (i32.const 393217) (i32.const 248) (i32.const 8)))" ++
              " (if (i32.lt_s (local.get $st) (i32.const 0))" ++
              " (then (return (local.get $st))))" ++
              " (local.set $st (call $" ++ host.addTxnField ++
              " (i32.load (i32.const 260)) (i32.const 524291) (i32.const 224) (i32.const 21)))" ++
              " (if (i32.lt_s (local.get $st) (i32.const 0))" ++
              " (then (return (local.get $st))))" ++ nidField ++
              " (local.set $st (call $" ++ host.emitBuiltTxn ++
              " (i32.load (i32.const 260))))" ++
              " (if (i32.lt_s (local.get $st) (i32.const 0))" ++
              " (then (return (local.get $st))))" ++
              " (i64.extend_i32_s (local.get $st)))")
          else if tag.startsWith "xpayt." then
            if host.buildTxn.isEmpty || host.addTxnField.isEmpty ||
                host.emitBuiltTxn.isEmpty then
              throw "extract/unsupported: emitPayToLit wants build_txn"
            let hex := String.ofList (tag.toList.drop 6)
            let rec nibble (c : Char) : Option Nat :=
              let n := c.toNat
              if n ≥ 48 && n ≤ 57 then some (n - 48)
              else if n ≥ 97 && n ≤ 102 then some (n - 87)
              else if n ≥ 65 && n ≤ 70 then some (n - 55)
              else none
            let rec bytes (cs : List Char) (acc : Array Nat) : Option (Array Nat) :=
              match cs with
              | c0 :: c1 :: rest =>
                match nibble c0, nibble c1 with
                | some hi, some lo => bytes rest (acc.push (hi * 16 + lo))
                | _, _ => none
              | [] => some acc
              | _ => none
            let destStores :=
              match bytes hex.toList #[] with
              | some bs =>
                if bs.size != 20 then ""
                else String.join ((Array.range 20).toList.map fun i =>
                  "(i32.store8 (i32.const " ++ toString (225 + i) ++
                  ") (i32.const " ++ toString bs[i]! ++ "))")
              | none => ""
            unless !destStores.isEmpty do
              throw "extract/unsupported: emitPayToLit wants 40 hex chars"
            let nidStores :=
              if host.ledgerSqnBuffer then ""
              else
                "(i32.store8 (i32.const 256) (i32.const 0x00))" ++
                "(i32.store8 (i32.const 257) (i32.const 0x00))" ++
                "(i32.store8 (i32.const 258) (i32.const 0xF7))" ++
                "(i32.store8 (i32.const 259) (i32.const 0xE0))"
            let nidField :=
              if host.ledgerSqnBuffer then ""
              else
                " (local.set $st (call $" ++ host.addTxnField ++
                " (i32.load (i32.const 260)) (i32.const 131073) (i32.const 256) (i32.const 4)))" ++
                " (if (i32.lt_s (local.get $st) (i32.const 0))" ++
                " (then (return (local.get $st))))"
            return ("(block (result i64) (i32.store8 (i32.const 224) (i32.const 0x14)) " ++
              destStores ++
              " (i32.store8 (i32.const 248) (i32.const 0x40))" ++
              " (i32.store8 (i32.const 249) (i32.const 0x00))" ++
              " (i32.store8 (i32.const 250) (i32.const 0x00))" ++
              " (i32.store8 (i32.const 251) (i32.const 0x00))" ++
              " (i32.store8 (i32.const 252) (i32.const 0x00))" ++
              " (i32.store8 (i32.const 253) (i32.const 0x00))" ++
              " (i32.store8 (i32.const 254) (i32.const 0x00))" ++
              " (i32.store8 (i32.const 255) (i32.const 0xC0)) " ++ nidStores ++
              " (local.set $st (call $" ++ host.buildTxn ++ " (i32.const 0)))" ++
              " (if (i32.lt_s (local.get $st) (i32.const 0))" ++
              " (then (return (local.get $st))))" ++
              " (i32.store (i32.const 260) (local.get $st))" ++
              " (local.set $st (call $" ++ host.addTxnField ++
              " (i32.load (i32.const 260)) (i32.const 393217) (i32.const 248) (i32.const 8)))" ++
              " (if (i32.lt_s (local.get $st) (i32.const 0))" ++
              " (then (return (local.get $st))))" ++
              " (local.set $st (call $" ++ host.addTxnField ++
              " (i32.load (i32.const 260)) (i32.const 524291) (i32.const 224) (i32.const 21)))" ++
              " (if (i32.lt_s (local.get $st) (i32.const 0))" ++
              " (then (return (local.get $st))))" ++ nidField ++
              " (local.set $st (call $" ++ host.emitBuiltTxn ++
              " (i32.load (i32.const 260))))" ++
              " (if (i32.lt_s (local.get $st) (i32.const 0))" ++
              " (then (return (local.get $st))))" ++
              " (i64.extend_i32_s (local.get $st)))")
          else
            return ("(local.get $" ++ extLocal extTag kind ++ ")")
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

/-- Consecutive `returnState` leaves, one per slot, as emitted by a multi-field init. -/
private def collectReturnStates (first : Val ValExt) (rest : List (Op ValExt OpExt)) :
    Array (Val ValExt) × List (Op ValExt OpExt) :=
  let rec go (acc : Array (Val ValExt)) (rest : List (Op ValExt OpExt)) :
      Array (Val ValExt) × List (Op ValExt OpExt) :=
    match rest with
    | .returnState next :: more => go (acc.push next) more
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

/-- Linear-memory map for object-field storage (XRPL ContractData). -/
private def accountOff : Nat := 0
private def accountLen : Nat := 20
private def paramOffObj : Nat := 20
private def storeOff : Nat := 28
private def keyBase : Nat := 64

/-- Slot `user_bal` → nested `{user:{bal}}`. `xs_0` stays a flat key (digit suffix). -/
private def nestedParts (name : String) : Option (String × String) :=
  match name.toList.span (· != '_') with
  | (outer, '_' :: rest) =>
    let o := String.ofList outer
    let inner := String.ofList rest
    if o.isEmpty || inner.isEmpty then none
    else if inner.front.isDigit then none
    else some (o, inner)
  | _ => none

private def keyBlob (p : Program ValExt OpExt) : String :=
  let parts : Array String :=
    p.slots.foldl (fun acc slot =>
      match nestedParts slot.name with
      | some (o, i) => acc.push o |>.push i
      | none => acc.push slot.name) #[]
  String.join parts.toList

private def keyOffsetOf (p : Program ValExt OpExt) (name : String) : Nat :=
  (p.slots.foldl (fun (acc : Nat × Bool) slot =>
    if acc.2 then acc
    else if slot.name == name then (acc.1, true)
    else
      let n :=
        match nestedParts slot.name with
        | some (o, i) => o.length + i.length
        | none => slot.name.length
      (acc.1 + n, false)) (keyBase, false)).1

private def nestedOffsets (p : Program ValExt OpExt) (name : String) : Option (Nat × Nat × Nat × Nat) :=
  match nestedParts name with
  | none => none
  | some (outer, inner) =>
    let off := keyOffsetOf p name
    some (off, outer.length, off + outer.length, inner.length)

/-- Big-endian store of an i64 local into 8 bytes at `ptr`. -/
private def storeBe64 (level ptr : Nat) (localName : String) : Array String :=
  (Array.range 8).map fun i =>
    let shift := (7 - i) * 8
    indent level ("(i32.store8 (i32.const " ++ toString (ptr + i) ++
      ") (i32.wrap_i64 (i64.shr_u (local.get " ++ localName ++
      ") (i64.const " ++ toString shift ++ "))))")

/-- Big-endian load of 8 bytes at `ptr` as i64. -/
private def loadBe64 (ptr : Nat) : String :=
  (Array.range 8).foldl (fun acc i =>
    let byte := "(i64.extend_i32_u (i32.load8_u (i32.const " ++
      toString (ptr + i) ++ ")))"
    if acc.isEmpty then byte
    else "(i64.or (i64.shl " ++ acc ++ " (i64.const 8)) " ++ byte ++ ")") ""

/-- On a negative `$st`, return it unless it is a host "missing" code. -/
private def returnUnlessMissing (host : Contract) (level : Nat) : Array String :=
  if host.missingFields.isEmpty then
    #[
      indent level "(if (i32.lt_s (local.get $st) (i32.const 0))",
      indent (level + 2) "(then (return (local.get $st))))"
    ]
  else
    let eqs := host.missingFields.foldl (fun acc (code : Int) =>
      let eq := "(i32.eq (local.get $st) (i32.const " ++ toString code ++ "))"
      if acc.isEmpty then eq else "(i32.or " ++ acc ++ " " ++ eq ++ ")") ""
    #[
      indent level "(if (i32.lt_s (local.get $st) (i32.const 0))",
      indent (level + 2) "(then",
      indent (level + 4) ("(if (i32.eqz " ++ eqs ++ ")"),
      indent (level + 6) "(then (return (local.get $st))))))"
    ]

/-- Write every slot through the chain's storage host. -/
private def persistSlots (host : Contract) (p : Program ValExt OpExt) (level : Nat) :
    Array String :=
  if !host.objectStore then
    dumpSlots p level ++ hostWrite host p level
  else
    p.slots.flatMap fun slot =>
      let hdr := #[
        indent level ("(i32.store8 (i32.const " ++ toString storeOff ++
          ") (i32.const " ++ toString host.stiUint64 ++ "))")
      ]
      let be := storeBe64 level (storeOff + 1) (localOfSlot slot.name)
      let call :=
        match nestedOffsets p slot.name with
        | some (oOff, oLen, iOff, iLen) =>
          if host.setDataNested.isEmpty then
            let keyOff := keyOffsetOf p slot.name
            #[
              indent level ("(local.set $st (call $" ++ host.setDataObject ++
                " (i32.const " ++ toString accountOff ++
                ") (i32.const " ++ toString accountLen ++
                ") (i32.const " ++ toString keyOff ++
                ") (i32.const " ++ toString slot.name.length ++
                ") (i32.const " ++ toString storeOff ++
                ") (i32.const 9)))")
            ]
          else
            #[
              indent level ("(local.set $st (call $" ++ host.setDataNested ++
                " (i32.const " ++ toString accountOff ++
                ") (i32.const " ++ toString accountLen ++
                ") (i32.const " ++ toString oOff ++
                ") (i32.const " ++ toString oLen ++
                ") (i32.const " ++ toString iOff ++
                ") (i32.const " ++ toString iLen ++
                ") (i32.const " ++ toString storeOff ++
                ") (i32.const 9)))")
            ]
        | none =>
          let keyOff := keyOffsetOf p slot.name
          #[
            indent level ("(local.set $st (call $" ++ host.setDataObject ++
              " (i32.const " ++ toString accountOff ++
              ") (i32.const " ++ toString accountLen ++
              ") (i32.const " ++ toString keyOff ++
              ") (i32.const " ++ toString slot.name.length ++
              ") (i32.const " ++ toString storeOff ++
              ") (i32.const 9)))")
          ]
      hdr ++ be ++ call ++ #[
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
    (extTag : ValExt → String) (view : Bool) (level : Nat) (defaultSlot : String)
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
            let l ← renderVal host extTag st lhs
            let r ← renderVal host extTag st rhs
            let (raw, st1) ← emitChecked st kind l r
            let dest' := (fieldOf lhs).orElse (fun _ => st.pendingDest)
            let st' := { st1 with pendingDest := dest' }
            let lines := raw.map (indent level)
            let region ← emitRegion host p extTag view level defaultSlot tail st'
            return { lines := lines ++ region.lines, st := region.st, terminal := true }
        | none => throw "extract/unsupported: wasm v0 checked operation"
    | .ite cmp lhs rhs thn els =>
        let l ← renderVal host extTag st lhs
        let r ← renderVal host extTag st rhs
        let head := indent level ("(if (" ++ cmpInstr cmp ++ " " ++ l ++ " " ++ r ++ ")")
        let thenRegion ← emitRegion host p extTag view (level + 4) defaultSlot thn.toList
          { st with last := none, pendingDest := none }
        unless thenRegion.terminal do
          throw "extract/unsupported: wasm v0 ite branch must end in a terminal"
        let elseRegion ← emitRegion host p extTag view (level + 4) defaultSlot els.toList
          { st with fresh := thenRegion.st.fresh, last := none, pendingDest := none }
        unless elseRegion.terminal do
          throw "extract/unsupported: wasm v0 ite branch must end in a terminal"
        let terminalIte := tail.isEmpty || tail.all isExitOp
        let iteHead :=
          if terminalIte then
            let ty := if view && !host.viewResultI32 then "i64" else "i32"
            indent level ("(if (result " ++ ty ++ ") (" ++ cmpInstr cmp ++ " " ++ l ++ " " ++ r ++ ")")
          else head
        let iteLines :=
          #[iteHead, indent (level + 2) "(then"] ++ thenRegion.lines ++
          #[indent (level + 2) ")", indent (level + 2) "(else"] ++ elseRegion.lines ++
          #[indent (level + 2) "))"]
        if terminalIte then
          return { lines := iteLines, st := elseRegion.st, terminal := true }
        let region ← emitRegion host p extTag view level defaultSlot tail
          { st with fresh := elseRegion.st.fresh, last := none, pendingDest := none }
        return { lines := iteLines ++ region.lines, st := region.st, terminal := true }
    | .storeField name value =>
        if view then throw "extract/unsupported: wasm v0 view cannot write state"
        let v ← renderVal host extTag st value
        let lines :=
          #[indent level ("(local.set " ++ localOfSlot name ++ " " ++ v ++ ")")] ++
          persistSlots host p level
        let region ← emitRegion host p extTag view level defaultSlot tail
          { st with last := some (localOfSlot name), pendingDest := some name }
        return { lines := lines ++ region.lines, st := region.st, terminal := true }
    | .okState value =>
        if view then throw "extract/unsupported: wasm v0 view cannot write state"
        let dest := st.pendingDest <|> fieldOf value |>.getD defaultSlot
        let v ← match st.last with
          | some e => .ok ("(local.get " ++ e ++ ")")
          | none => renderVal host extTag st value
        unless tail.all isExitOp do
          throw "extract/unsupported: wasm v0 instructions follow terminal operation"
        let lines :=
          #[indent level ("(local.set " ++ localOfSlot dest ++ " " ++ v ++ ")")] ++
          persistSlots host p level ++
          #[indent level "(i32.const 0)"]
        return { lines, st, terminal := true }
    | .returnState value =>
        if view then throw "extract/unsupported: wasm v0 view cannot write state"
        let (values, skipped) := collectReturnStates value tail
        unless skipped.all isExitOp do
          throw "extract/unsupported: wasm v0 instructions follow terminal operation"
        if values.size == p.slots.size then
          let mut lines : Array String := #[]
          for i in [:p.slots.size] do
            let v ← renderVal host extTag st values[i]!
            lines := lines.push
              (indent level ("(local.set " ++ localOfSlot p.slots[i]!.name ++ " " ++ v ++ ")"))
          lines := lines ++ persistSlots host p level ++ #[indent level "(i32.const 0)"]
          return { lines, st, terminal := true }
        else
          let dest := st.pendingDest <|> fieldOf value |>.getD defaultSlot
          let v ← match st.last with
            | some e => .ok ("(local.get " ++ e ++ ")")
            | none => renderVal host extTag st value
          let lines :=
            #[indent level ("(local.set " ++ localOfSlot dest ++ " " ++ v ++ ")")] ++
            persistSlots host p level ++
            #[indent level "(i32.const 0)"]
          return { lines, st, terminal := true }
    | .errorOverflow =>
        if view then throw "extract/unsupported: wasm v0 view cannot fail"
        unless tail.all isExitOp do
          throw "extract/unsupported: wasm v0 instructions follow terminal operation"
        return { lines := #[indent level "(i32.const 1)"], st, terminal := true }
    | .errorNamed "unauthorized" =>
        if view then throw "extract/unsupported: wasm v0 view cannot fail"
        unless tail.all isExitOp do
          throw "extract/unsupported: wasm v0 instructions follow terminal operation"
        return { lines := #[indent level "(i32.const 3)"], st, terminal := true }
    | .errorNamed "paused" =>
        if view then throw "extract/unsupported: wasm v0 view cannot fail"
        unless tail.all isExitOp do
          throw "extract/unsupported: wasm v0 instructions follow terminal operation"
        return { lines := #[indent level "(i32.const 4)"], st, terminal := true }
    | .errorNamed "frozen" =>
        if view then throw "extract/unsupported: wasm v0 view cannot fail"
        unless tail.all isExitOp do
          throw "extract/unsupported: wasm v0 instructions follow terminal operation"
        return { lines := #[indent level "(i32.const 5)"], st, terminal := true }
    | .returnU64 value =>
        unless view do
          throw "extract/unsupported: wasm v0 mutating region cannot return a value"
        let (values, skipped) := collectReturnU64s value tail
        unless skipped.all isExitOp do
          throw "extract/unsupported: wasm v0 instructions follow terminal operation"
        unless values.size == 1 do
          throw "extract/unsupported: wasm v0 view result count is out of range"
        let v ← renderVal host extTag st values[0]!
        let lines :=
          if host.viewResultI32 then
            #[indent level ("(i32.wrap_i64 " ++ v ++ ")")]
          else
            #[indent level v]
        return { lines, st, terminal := true }
    | _ => throw "extract/unsupported: wasm v0 op"

private def defaultSlotOf (p : Program ValExt OpExt) : String :=
  (p.slots[0]?).map (·.name) |>.getD "slot0"

private def paramDecl (count : Nat) : String :=
  String.intercalate " " ((List.range count).map (fun i =>
    "(param " ++ localOfArg i ++ " i64)"))

private def paramLocals (count : Nat) : Array String :=
  (Array.range count).map fun i => "(local " ++ localOfArg i ++ " i64)"

private def slotLocals (p : Program ValExt OpExt) : Array String :=
  p.slots.map fun slot => "(local " ++ localOfSlot slot.name ++ " i64)"

private def tempLocals (n : Nat) : Array String :=
  (Array.range n).map fun i => "(local " ++ localOfTemp i ++ " i64)"

/-- Scratch for `function_param` so it does not clobber account/keys. -/
private def paramScratch (host : Contract) (_p : Program ValExt OpExt) : Nat :=
  if host.objectStore then paramOffObj else 0

/-- Copy each ContractCall UINT64 into `$pf_p{i}` via `host.functionParam`. -/
private def loadHostParams (host : Contract) (p : Program ValExt OpExt)
    (count : Nat) (level : Nat) (view : Bool) : Array String :=
  if host.functionParam.isEmpty || count == 0 then #[]
  else
    let scratch := paramScratch host p
    (Array.range count).flatMap fun i =>
      let header :=
        indent level ("(local.set $st (call $" ++ host.functionParam ++
          " (i32.const " ++ toString i ++
          ") (i32.const " ++ toString host.stiUint64 ++
          ") (i32.const " ++ toString scratch ++
          ") (i32.const 8)))")
      let err :=
        if view then #[]
        else #[
          indent level "(if (i32.lt_s (local.get $st) (i32.const 0))",
          indent (level + 2) "(then (return (local.get $st))))"
        ]
      let load :=
        indent level ("(local.set " ++ localOfArg i ++
          " (i64.load (i32.const " ++ toString scratch ++ ")))")
      #[header] ++ err ++ #[load]

private def loadAccount (host : Contract) (level : Nat) (view : Bool) : Array String :=
  if !host.objectStore then #[]
  else
    let hostFn := if host.ownerFromTx then host.getTxField else host.homeLeField
    let field := if host.ownerFromTx then host.sfieldTxAccount else host.sfieldAccount
    let header := #[
      indent level ("(local.set $st (call $" ++ hostFn ++
        " (i32.const " ++ toString field ++
        ") (i32.const " ++ toString accountOff ++
        ") (i32.const " ++ toString accountLen ++ ")))")
    ]
    let err :=
      if view then #[]
      else #[
        indent level "(if (i32.lt_s (local.get $st) (i32.const 0))",
        indent (level + 2) "(then (return (local.get $st))))"
      ]
    header ++ err

private def loadSlots (host : Contract) (p : Program ValExt OpExt) (level : Nat)
    (view : Bool) : Array String :=
  if host.objectStore then
    p.slots.flatMap fun slot =>
      let call :=
        match nestedOffsets p slot.name with
        | some (oOff, oLen, iOff, iLen) =>
          if host.getDataNested.isEmpty then
            let keyOff := keyOffsetOf p slot.name
            indent level ("(local.set $st (call $" ++ host.getDataObject ++
              " (i32.const " ++ toString accountOff ++
              ") (i32.const " ++ toString accountLen ++
              ") (i32.const " ++ toString keyOff ++
              ") (i32.const " ++ toString slot.name.length ++
              ") (i32.const " ++ toString storeOff ++
              ") (i32.const 8)))")
          else
            indent level ("(local.set $st (call $" ++ host.getDataNested ++
              " (i32.const " ++ toString accountOff ++
              ") (i32.const " ++ toString accountLen ++
              ") (i32.const " ++ toString oOff ++
              ") (i32.const " ++ toString oLen ++
              ") (i32.const " ++ toString iOff ++
              ") (i32.const " ++ toString iLen ++
              ") (i32.const " ++ toString storeOff ++
              ") (i32.const 8)))")
        | none =>
          let keyOff := keyOffsetOf p slot.name
          indent level ("(local.set $st (call $" ++ host.getDataObject ++
            " (i32.const " ++ toString accountOff ++
            ") (i32.const " ++ toString accountLen ++
            ") (i32.const " ++ toString keyOff ++
            ") (i32.const " ++ toString slot.name.length ++
            ") (i32.const " ++ toString storeOff ++
            ") (i32.const 8)))")
      let err :=
        if view then #[] else returnUnlessMissing host level
      let load := #[
        indent level "(if (i32.gt_s (local.get $st) (i32.const 0))",
        indent (level + 2) "(then",
        indent (level + 4) ("(local.set " ++ localOfSlot slot.name ++
          " " ++ loadBe64 storeOff ++ ")))")
      ]
      #[call] ++ err ++ load
  else
    let blob := blobLen p
    let header := #[
      indent level ("(local.set $st (call $" ++ host.homeLeField ++
        " (i32.const " ++ toString host.sfieldData ++
        ") (i32.const 0) (i32.const " ++ toString blob ++ ")))")
    ]
    let err := if view then #[] else returnUnlessMissing host level
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
    (method : Method ValExt OpExt)
    (extValCanon : ValExt → String)
    (loadEnv : Contract → Method ValExt OpExt → Nat → Bool → Array String) : Except String (Array String) := do
  let view := method.tupleArity.isSome
  let st : EState := { paramCount := method.paramCount }
  let region ← emitRegion host p extValCanon view 4 (defaultSlotOf p) method.ops.toList st
  unless region.terminal do
    throw s!"extract/unsupported: {method.ixName} does not end in a terminal"
  let resultTy := if view && !host.viewResultI32 then "i64" else "i32"
  let hostParams := !host.functionParam.isEmpty
  let params := if hostParams then "" else paramDecl method.paramCount
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
  if hostParams then
    for loc in paramLocals method.paramCount do
      lines := lines.push s!"    {loc}"
  if !host.getTxField.isEmpty then
    for name in #["pf_x_xc0", "pf_x_xc1", "pf_x_xc2",
                  "pf_x_xs0", "pf_x_xs1", "pf_x_xs2",
                  "pf_x_xsqn", "pf_x_xtime", "pf_x_xhash0", "pf_x_xfee", "pf_x_xbal",
                  "pf_x_xseq", "pf_x_xflags", "pf_x_xownc",
                  "pf_x_xtseq", "pf_x_xtfee", "pf_x_xtflags", "pf_x_xlitbal"] do
      lines := lines.push s!"    (local ${name} i64)"
  for loc in slotLocals p do
    lines := lines.push s!"    {loc}"
  for loc in tempLocals (Nat.max (countTemps method.ops) region.st.fresh) do
    lines := lines.push s!"    {loc}"
  lines := lines ++ loadHostParams host p method.paramCount 4 view
  lines := lines ++ loadAccount host 4 view
  lines := lines ++ loadEnv host method 4 view
  lines := lines ++ loadSlots host p 4 view
  lines := lines ++ region.lines
  lines := lines.push "  )"
  return lines

/-- Render one program as WAT. Digest line pins the canonical IR identity. -/
def emit (host : Contract)
    (extValCanon : ValExt → String) (extOpCanon : OpExt (Val ValExt) → String)
    (p : Program ValExt OpExt)
    (loadEnv : Contract → Method ValExt OpExt → Nat → Bool → Array String := fun _ _ _ _ => #[])
    (extraImports : Array String := #[]) : Except String String := do
  let mut lines : Array String := #[]
  lines := lines.push s!";; {host.headerTag}"
  lines := lines.push s!";; digest={IR.digestHex host.digestDomain extValCanon extOpCanon p}"
  for note in host.headerNotes do
    lines := lines.push note
  lines := lines.push "(module"
  lines := lines.push
    ("  (import \"" ++ host.importModule ++ "\" \"" ++ host.homeLeField ++
      "\" (func $" ++ host.homeLeField ++ " (param i32 i32 i32) (result i32)))")
  if host.objectStore then
    lines := lines.push
      ("  (import \"" ++ host.importModule ++ "\" \"" ++ host.getDataObject ++
        "\" (func $" ++ host.getDataObject ++
        " (param i32 i32 i32 i32 i32 i32) (result i32)))")
    lines := lines.push
      ("  (import \"" ++ host.importModule ++ "\" \"" ++ host.setDataObject ++
        "\" (func $" ++ host.setDataObject ++
        " (param i32 i32 i32 i32 i32 i32) (result i32)))")
    if !host.getDataNested.isEmpty && p.slots.any (fun s => (nestedParts s.name).isSome) then
      lines := lines.push
        ("  (import \"" ++ host.importModule ++ "\" \"" ++ host.getDataNested ++
          "\" (func $" ++ host.getDataNested ++
          " (param i32 i32 i32 i32 i32 i32 i32 i32) (result i32)))")
      lines := lines.push
        ("  (import \"" ++ host.importModule ++ "\" \"" ++ host.setDataNested ++
          "\" (func $" ++ host.setDataNested ++
          " (param i32 i32 i32 i32 i32 i32 i32 i32) (result i32)))")
  else
    lines := lines.push
      ("  (import \"" ++ host.importModule ++ "\" \"" ++ host.setData ++
        "\" (func $" ++ host.setData ++ " (param i32 i32) (result i32)))")
  if !host.functionParam.isEmpty then
    lines := lines.push
      ("  (import \"" ++ host.importModule ++ "\" \"" ++ host.functionParam ++
        "\" (func $" ++ host.functionParam ++
        " (param i32 i32 i32 i32) (result i32)))")
  for extra in extraImports do
    lines := lines.push extra
  lines := lines.push "  (memory (export \"memory\") 1)"
  if host.objectStore && !p.slots.isEmpty then
    lines := lines.push
      ("  (data (i32.const " ++ toString keyBase ++ ") \"" ++ keyBlob p ++ "\")")
  lines := lines.push ""
  lines := lines ++ (← renderFn host p p.initializer extValCanon loadEnv)
  lines := lines.push ""
  for method in p.entries do
    lines := lines ++ (← renderFn host p method extValCanon loadEnv)
    lines := lines.push ""
  lines := lines.push ")"
  return String.intercalate "\n" lines.toList ++ "\n"

end ProofForge.Wasm.Emit
