import ProofForge.Evm.HashedMap
import ProofForge.Evm.Ops

namespace ProofForge.Evm.HashedMap.Emit

private def nl : String := "\n"
private def u64MaxYul : String := "0xffffffffffffffff"
private def revert0 : String := "revert(0, 0)"

private def packU256 (w0 w1 w2 w3 : String) : String :=
  "or(or(" ++ w0 ++ ", shl(64, " ++ w1 ++ ")), or(shl(128, " ++ w2 ++ "), shl(192, " ++ w3 ++ ")))"

private def packU256Word (src : String) (word : Nat) : String :=
  "and(shr(" ++ toString (64 * word) ++ ", " ++ src ++ "), " ++ u64MaxYul ++ ")"

/-- Generic hashed-map emission context. The main emitter supplies materialization and
fresh-name state; this module does not know about the surrounding Render record. -/
structure Context (σ : Type) where
  materialize : Ops.Val → σ → Except String (String × String × σ)
  fresh : σ → String × σ
  rememberWide : σ → String → String → σ
  lookupWide : σ → String → Option String
  valKey : Ops.Val → String
  indent : String

private def emitGetU64 (context : Context σ) (base key : Ops.Val) (st : σ) :
    Except String (String × String × σ) := do
  let indent := context.indent
  let (pb, b, st1) ← context.materialize base st
  let (pk, k, st2) ← context.materialize key st1
  let (slot, st3) := context.fresh st2
  let (tag, st4) := context.fresh st3
  let (pay, st5) := context.fresh st4
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

private def emitGetAddr (context : Context σ) (base w0 w1 w2 : Ops.Val) (st : σ) :
    Except String (String × String × σ) := do
  let indent := context.indent
  let (pb, b, st1) ← context.materialize base st
  let (p0, a0, st2) ← context.materialize w0 st1
  let (p1, a1, st3) ← context.materialize w1 st2
  let (p2, a2, st4) ← context.materialize w2 st3
  let (slot, st5) := context.fresh st4
  let (tag, st6) := context.fresh st5
  let (pay, st7) := context.fresh st6
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

private def emitGetPair (context : Context σ) (base o0 o1 o2 s0 s1 s2 : Ops.Val) (st : σ) :
    Except String (String × String × σ) := do
  let indent := context.indent
  let (pb, b, st1) ← context.materialize base st
  let (p0, a0, st2) ← context.materialize o0 st1
  let (p1, a1, st3) ← context.materialize o1 st2
  let (p2, a2, st4) ← context.materialize o2 st3
  let (q0, b0, st5) ← context.materialize s0 st4
  let (q1, b1, st6) ← context.materialize s1 st5
  let (q2, b2, st7) ← context.materialize s2 st6
  let (slot, st8) := context.fresh st7
  let (tag, st9) := context.fresh st8
  let (pay, st10) := context.fresh st9
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

private def emitGetAddr256 (context : Context σ) (limb : Nat)
    (base w0 w1 w2 : Ops.Val) (st : σ) : Except String (String × String × σ) := do
  let indent := context.indent
  let (pb, b, st1) ← context.materialize base st
  let (p0, a0, st2) ← context.materialize w0 st1
  let (p1, a1, st3) ← context.materialize w1 st2
  let (p2, a2, st4) ← context.materialize w2 st3
  let cacheKey :=
    "mga256|" ++ context.valKey base ++ "|" ++ context.valKey w0 ++ "|" ++
      context.valKey w1 ++ "|" ++ context.valKey w2
  match context.lookupWide st4 cacheKey with
  | some pay =>
      let (nm, st5) := context.fresh st4
      return (pb ++ p0 ++ p1 ++ p2 ++
        indent ++ "let " ++ nm ++ " := " ++ packU256Word pay limb ++ nl, nm, st5)
  | none =>
      let (slot, st5) := context.fresh st4
      let (tag, st6) := context.fresh st5
      let (pay, st7) := context.fresh st6
      let (nm, st8) := context.fresh (context.rememberWide st7 cacheKey pay)
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

private def emitGetPair256 (context : Context σ) (limb : Nat)
    (base o0 o1 o2 s0 s1 s2 : Ops.Val) (st : σ) : Except String (String × String × σ) := do
  let indent := context.indent
  let (pb, b, st1) ← context.materialize base st
  let (p0, a0, st2) ← context.materialize o0 st1
  let (p1, a1, st3) ← context.materialize o1 st2
  let (p2, a2, st4) ← context.materialize o2 st3
  let (q0, b0, st5) ← context.materialize s0 st4
  let (q1, b1, st6) ← context.materialize s1 st5
  let (q2, b2, st7) ← context.materialize s2 st6
  let cacheKey :=
    "mgp256|" ++ context.valKey base ++ "|" ++ context.valKey o0 ++ "|" ++
      context.valKey o1 ++ "|" ++ context.valKey o2 ++ "|" ++
      context.valKey s0 ++ "|" ++ context.valKey s1 ++ "|" ++ context.valKey s2
  match context.lookupWide st7 cacheKey with
  | some pay =>
      let (nm, st8) := context.fresh st7
      return (pb ++ p0 ++ p1 ++ p2 ++ q0 ++ q1 ++ q2 ++
        indent ++ "let " ++ nm ++ " := " ++ packU256Word pay limb ++ nl, nm, st8)
  | none =>
      let (slot, st8) := context.fresh st7
      let (tag, st9) := context.fresh st8
      let (pay, st10) := context.fresh st9
      let (nm, st11) := context.fresh (context.rememberWide st10 cacheKey pay)
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

def emitQuery (context : Context σ) (query : HashedMap.Query) (operands : Array Ops.Val)
    (st : σ) : Except String (String × String × σ) :=
  match query, operands.toList with
  | .getU64, [base, key] => emitGetU64 context base key st
  | .getAddr, [base, w0, w1, w2] => emitGetAddr context base w0 w1 w2 st
  | .getPair, [base, o0, o1, o2, s0, s1, s2] =>
      emitGetPair context base o0 o1 o2 s0 s1 s2 st
  | .getAddr256 limb, [base, w0, w1, w2] =>
      emitGetAddr256 context limb base w0 w1 w2 st
  | .getPair256 limb, [base, o0, o1, o2, s0, s1, s2] =>
      emitGetPair256 context limb base o0 o1 o2 s0 s1 s2 st
  | _, _ =>
      .error s!"extract/unsupported: evm hashed-map query arity {operands.size}"

private def emitSetU64 (context : Context σ) (base key value : Ops.Val) (st : σ) :
    Except String (String × String × σ) := do
  let indent := context.indent
  let (pb, b, st1) ← context.materialize base st
  let (pk, k, st2) ← context.materialize key st1
  let (pv, v, st3) ← context.materialize value st2
  let (slot, st4) := context.fresh st3
  let txt := pb ++ pk ++ pv ++
    indent ++ "mstore(0, " ++ k ++ ")" ++ nl ++
    indent ++ "mstore(32, " ++ b ++ ")" ++ nl ++
    indent ++ "let " ++ slot ++ " := keccak256(0, 64)" ++ nl ++
    indent ++ "sstore(" ++ slot ++ ", 1)" ++ nl ++
    indent ++ "sstore(add(" ++ slot ++ ", 1), " ++ v ++ ")" ++ nl
  return (txt, v, st4)

private def emitSetAddr (context : Context σ) (base w0 w1 w2 value : Ops.Val) (st : σ) :
    Except String (String × String × σ) := do
  let indent := context.indent
  let (pb, b, st1) ← context.materialize base st
  let (p0, a0, st2) ← context.materialize w0 st1
  let (p1, a1, st3) ← context.materialize w1 st2
  let (p2, a2, st4) ← context.materialize w2 st3
  let (pv, v, st5) ← context.materialize value st4
  let (slot, st6) := context.fresh st5
  let txt := pb ++ p0 ++ p1 ++ p2 ++ pv ++
    indent ++ "mstore(0, " ++ a0 ++ ")" ++ nl ++
    indent ++ "mstore(32, " ++ a1 ++ ")" ++ nl ++
    indent ++ "mstore(64, " ++ a2 ++ ")" ++ nl ++
    indent ++ "mstore(96, " ++ b ++ ")" ++ nl ++
    indent ++ "let " ++ slot ++ " := keccak256(0, 128)" ++ nl ++
    indent ++ "sstore(" ++ slot ++ ", 1)" ++ nl ++
    indent ++ "sstore(add(" ++ slot ++ ", 1), " ++ v ++ ")" ++ nl
  return (txt, v, st6)

private def emitSetPair (context : Context σ) (base o0 o1 o2 s0 s1 s2 value : Ops.Val)
    (st : σ) : Except String (String × String × σ) := do
  let indent := context.indent
  let (pb, b, st1) ← context.materialize base st
  let (p0, a0, st2) ← context.materialize o0 st1
  let (p1, a1, st3) ← context.materialize o1 st2
  let (p2, a2, st4) ← context.materialize o2 st3
  let (q0, b0, st5) ← context.materialize s0 st4
  let (q1, b1, st6) ← context.materialize s1 st5
  let (q2, b2, st7) ← context.materialize s2 st6
  let (pv, v, st8) ← context.materialize value st7
  let (slot, st9) := context.fresh st8
  let txt := pb ++ p0 ++ p1 ++ p2 ++ q0 ++ q1 ++ q2 ++ pv ++
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
  return (txt, v, st9)

private def emitSetAddr256 (context : Context σ)
    (base w0 w1 w2 v0 v1 v2 v3 : Ops.Val) (st : σ) :
    Except String (String × String × σ) := do
  let indent := context.indent
  let (pb, b, st1) ← context.materialize base st
  let (p0, a0, st2) ← context.materialize w0 st1
  let (p1, a1, st3) ← context.materialize w1 st2
  let (p2, a2, st4) ← context.materialize w2 st3
  let (q0, x0, st5) ← context.materialize v0 st4
  let (q1, x1, st6) ← context.materialize v1 st5
  let (q2, x2, st7) ← context.materialize v2 st6
  let (q3, x3, st8) ← context.materialize v3 st7
  let (slot, st9) := context.fresh st8
  let (pay, st10) := context.fresh st9
  let txt := pb ++ p0 ++ p1 ++ p2 ++ q0 ++ q1 ++ q2 ++ q3 ++
    indent ++ "mstore(0, " ++ a0 ++ ")" ++ nl ++
    indent ++ "mstore(32, " ++ a1 ++ ")" ++ nl ++
    indent ++ "mstore(64, " ++ a2 ++ ")" ++ nl ++
    indent ++ "mstore(96, " ++ b ++ ")" ++ nl ++
    indent ++ "let " ++ slot ++ " := keccak256(0, 128)" ++ nl ++
    indent ++ "let " ++ pay ++ " := " ++ packU256 x0 x1 x2 x3 ++ nl ++
    indent ++ "sstore(" ++ slot ++ ", 1)" ++ nl ++
    indent ++ "sstore(add(" ++ slot ++ ", 1), " ++ pay ++ ")" ++ nl
  return (txt, x0, st10)

private def emitSetPair256 (context : Context σ)
    (base o0 o1 o2 s0 s1 s2 v0 v1 v2 v3 : Ops.Val) (st : σ) :
    Except String (String × String × σ) := do
  let indent := context.indent
  let (pb, b, st1) ← context.materialize base st
  let (p0, a0, st2) ← context.materialize o0 st1
  let (p1, a1, st3) ← context.materialize o1 st2
  let (p2, a2, st4) ← context.materialize o2 st3
  let (q0, b0, st5) ← context.materialize s0 st4
  let (q1, b1, st6) ← context.materialize s1 st5
  let (q2, b2, st7) ← context.materialize s2 st6
  let (r0, x0, st8) ← context.materialize v0 st7
  let (r1, x1, st9) ← context.materialize v1 st8
  let (r2, x2, st10) ← context.materialize v2 st9
  let (r3, x3, st11) ← context.materialize v3 st10
  let (slot, st12) := context.fresh st11
  let (pay, st13) := context.fresh st12
  let txt := pb ++ p0 ++ p1 ++ p2 ++ q0 ++ q1 ++ q2 ++ r0 ++ r1 ++ r2 ++ r3 ++
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
  return (txt, x0, st13)

def emitCall (context : Context σ) (call : HashedMap.Call Ops.Val) (st : σ) :
    Except String (String × String × σ) :=
  match call with
  | .getU64 base key => emitGetU64 context base key st
  | .setU64 base key value => emitSetU64 context base key value st
  | .getAddr base w0 w1 w2 => emitGetAddr context base w0 w1 w2 st
  | .setAddr base w0 w1 w2 value => emitSetAddr context base w0 w1 w2 value st
  | .getPair base o0 o1 o2 s0 s1 s2 =>
      emitGetPair context base o0 o1 o2 s0 s1 s2 st
  | .setPair base o0 o1 o2 s0 s1 s2 value =>
      emitSetPair context base o0 o1 o2 s0 s1 s2 value st
  | .setAddr256 base w0 w1 w2 v0 v1 v2 v3 =>
      emitSetAddr256 context base w0 w1 w2 v0 v1 v2 v3 st
  | .setPair256 base o0 o1 o2 s0 s1 s2 v0 v1 v2 v3 =>
      emitSetPair256 context base o0 o1 o2 s0 s1 s2 v0 v1 v2 v3 st

end ProofForge.Evm.HashedMap.Emit
