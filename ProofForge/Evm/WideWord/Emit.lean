import ProofForge.Evm.WideWord
import ProofForge.Evm.Ops

namespace ProofForge.Evm.WideWord.Emit

private def nl : String := "\n"
private def u64MaxYul : String := "0xffffffffffffffff"
private def revert0 : String := "revert(0, 0)"

private def packU256 (w0 w1 w2 w3 : String) : String :=
  "or(or(" ++ w0 ++ ", shl(64, " ++ w1 ++ ")), or(shl(128, " ++ w2 ++ "), shl(192, " ++ w3 ++ ")))"

private def packU256Word (src : String) (word : Nat) : String :=
  "and(shr(" ++ toString (64 * word) ++ ", " ++ src ++ "), " ++ u64MaxYul ++ ")"

/-- Call the shared runtime helper that packs three little-endian Addr20 limbs into an
ABI address word at `memory[0..31]`. -/
private def packAddrMstore8 (indent w0 w1 w2 : String) : String :=
  indent ++ "pf_store_addr20(0, " ++ w0 ++ ", " ++ w1 ++ ", " ++ w2 ++ ")" ++ nl

/-- Shared with hashed-map emission so the main emitter can pass one context record. -/
structure Context (σ : Type) where
  materialize : Ops.Val → σ → Except String (String × String × σ)
  fresh : σ → String × σ
  rememberWide : σ → String → String → σ
  lookupWide : σ → String → Option String
  valKey : Ops.Val → String
  indent : String

private def compareExpr (comparison : WideWord.Comparison) (left right : String) : String :=
  match comparison with
  | .eq => "eq(" ++ left ++ ", " ++ right ++ ")"
  | .lt => "lt(" ++ left ++ ", " ++ right ++ ")"
  | .le => "iszero(gt(" ++ left ++ ", " ++ right ++ "))"
  | .gt => "gt(" ++ left ++ ", " ++ right ++ ")"
  | .ge => "iszero(lt(" ++ left ++ ", " ++ right ++ "))"

private def emitCompare256 (context : Context σ) (comparison : WideWord.Comparison)
    (a0 a1 a2 a3 b0 b1 b2 b3 : Ops.Val) (st : σ) :
    Except String (String × String × σ) := do
  let indent := context.indent
  let (p0, x0, s0) ← context.materialize a0 st
  let (p1, x1, s1) ← context.materialize a1 s0
  let (p2, x2, s2) ← context.materialize a2 s1
  let (p3, x3, s3) ← context.materialize a3 s2
  let (q0, y0, t0) ← context.materialize b0 s3
  let (q1, y1, t1) ← context.materialize b1 t0
  let (q2, y2, t2) ← context.materialize b2 t1
  let (q3, y3, t3) ← context.materialize b3 t2
  let (av, t4) := context.fresh t3
  let (bv, t5) := context.fresh t4
  let (nm, t6) := context.fresh t5
  let txt := p0 ++ p1 ++ p2 ++ p3 ++ q0 ++ q1 ++ q2 ++ q3 ++
    indent ++ "let " ++ av ++ " := " ++ packU256 x0 x1 x2 x3 ++ nl ++
    indent ++ "let " ++ bv ++ " := " ++ packU256 y0 y1 y2 y3 ++ nl ++
    indent ++ "let " ++ nm ++ " := " ++ compareExpr comparison av bv ++ nl
  return (txt, nm, t6)

private def emitEq20 (context : Context σ)
    (a0 a1 a2 b0 b1 b2 : Ops.Val) (st : σ) :
    Except String (String × String × σ) := do
  let indent := context.indent
  let (p0, x0, s0) ← context.materialize a0 st
  let (p1, x1, s1) ← context.materialize a1 s0
  let (p2, x2, s2) ← context.materialize a2 s1
  let (q0, y0, t0) ← context.materialize b0 s2
  let (q1, y1, t1) ← context.materialize b1 t0
  let (q2, y2, t2) ← context.materialize b2 t1
  let (av, t3) := context.fresh t2
  let (bv, t4) := context.fresh t3
  let (nm, t5) := context.fresh t4
  let txt := p0 ++ p1 ++ p2 ++ q0 ++ q1 ++ q2 ++
    indent ++ "mstore(0, 0)" ++ nl ++
    packAddrMstore8 indent x0 x1 x2 ++
    indent ++ "let " ++ av ++ " := mload(0)" ++ nl ++
    indent ++ "mstore(0, 0)" ++ nl ++
    packAddrMstore8 indent y0 y1 y2 ++
    indent ++ "let " ++ bv ++ " := mload(0)" ++ nl ++
    indent ++ "let " ++ nm ++ " := eq(" ++ av ++ ", " ++ bv ++ ")" ++ nl
  return (txt, nm, t5)

private def bitwiseExpr (operation : WideWord.Bitwise) (left right : String) : String :=
  match operation with
  | .and => "and(" ++ left ++ ", " ++ right ++ ")"
  | .or => "or(" ++ left ++ ", " ++ right ++ ")"
  | .xor => "xor(" ++ left ++ ", " ++ right ++ ")"

private def emitBitwise256 (context : Context σ) (operation : WideWord.Bitwise) (limb : Nat)
    (a0 a1 a2 a3 b0 b1 b2 b3 : Ops.Val) (st : σ) :
    Except String (String × String × σ) := do
  let indent := context.indent
  let (p0, x0, s0) ← context.materialize a0 st
  let (p1, x1, s1) ← context.materialize a1 s0
  let (p2, x2, s2) ← context.materialize a2 s1
  let (p3, x3, s3) ← context.materialize a3 s2
  let (q0, y0, t0) ← context.materialize b0 s3
  let (q1, y1, t1) ← context.materialize b1 t0
  let (q2, y2, t2) ← context.materialize b2 t1
  let (q3, y3, t3) ← context.materialize b3 t2
  let cacheKey :=
    "bitwise256|" ++ toString (repr operation) ++ "|" ++ context.valKey a0 ++ "|" ++
      context.valKey a1 ++ "|" ++ context.valKey a2 ++ "|" ++ context.valKey a3 ++ "|" ++
      context.valKey b0 ++ "|" ++ context.valKey b1 ++ "|" ++ context.valKey b2 ++ "|" ++
      context.valKey b3
  let pre := p0 ++ p1 ++ p2 ++ p3 ++ q0 ++ q1 ++ q2 ++ q3
  match context.lookupWide t3 cacheKey with
  | some rv =>
      let (nm, t4) := context.fresh t3
      return (pre ++ indent ++ "let " ++ nm ++ " := " ++ packU256Word rv limb ++ nl, nm, t4)
  | none =>
      let (av, t4) := context.fresh t3
      let (bv, t5) := context.fresh t4
      let (rv, t6) := context.fresh t5
      let (nm, t7) := context.fresh (context.rememberWide t6 cacheKey rv)
      let txt := pre ++
        indent ++ "let " ++ av ++ " := " ++ packU256 x0 x1 x2 x3 ++ nl ++
        indent ++ "let " ++ bv ++ " := " ++ packU256 y0 y1 y2 y3 ++ nl ++
        indent ++ "let " ++ rv ++ " := " ++ bitwiseExpr operation av bv ++ nl ++
        indent ++ "let " ++ nm ++ " := " ++ packU256Word rv limb ++ nl
      return (txt, nm, t7)

private def emitNot256 (context : Context σ) (limb : Nat)
    (a0 a1 a2 a3 : Ops.Val) (st : σ) : Except String (String × String × σ) := do
  let indent := context.indent
  let (p0, x0, s0) ← context.materialize a0 st
  let (p1, x1, s1) ← context.materialize a1 s0
  let (p2, x2, s2) ← context.materialize a2 s1
  let (p3, x3, s3) ← context.materialize a3 s2
  let cacheKey :=
    "not256|" ++ context.valKey a0 ++ "|" ++ context.valKey a1 ++ "|" ++
      context.valKey a2 ++ "|" ++ context.valKey a3
  let pre := p0 ++ p1 ++ p2 ++ p3
  match context.lookupWide s3 cacheKey with
  | some rv =>
      let (nm, s4) := context.fresh s3
      return (pre ++ indent ++ "let " ++ nm ++ " := " ++ packU256Word rv limb ++ nl, nm, s4)
  | none =>
      let (av, s4) := context.fresh s3
      let (rv, s5) := context.fresh s4
      let (nm, s6) := context.fresh (context.rememberWide s5 cacheKey rv)
      let txt := pre ++
        indent ++ "let " ++ av ++ " := " ++ packU256 x0 x1 x2 x3 ++ nl ++
        indent ++ "let " ++ rv ++ " := not(" ++ av ++ ")" ++ nl ++
        indent ++ "let " ++ nm ++ " := " ++ packU256Word rv limb ++ nl
      return (txt, nm, s6)

private def emitShift256 (context : Context σ) (direction : WideWord.Shift) (limb : Nat)
    (a0 a1 a2 a3 amount : Ops.Val) (st : σ) : Except String (String × String × σ) := do
  let indent := context.indent
  let (p0, x0, s0) ← context.materialize a0 st
  let (p1, x1, s1) ← context.materialize a1 s0
  let (p2, x2, s2) ← context.materialize a2 s1
  let (p3, x3, s3) ← context.materialize a3 s2
  let (pb, bits, s4) ← context.materialize amount s3
  let cacheKey :=
    "shift256|" ++ toString (repr direction) ++ "|" ++ context.valKey a0 ++ "|" ++
      context.valKey a1 ++ "|" ++ context.valKey a2 ++ "|" ++ context.valKey a3 ++ "|" ++
      context.valKey amount
  let pre := p0 ++ p1 ++ p2 ++ p3 ++ pb
  match context.lookupWide s4 cacheKey with
  | some rv =>
      let (nm, s5) := context.fresh s4
      return (pre ++ indent ++ "let " ++ nm ++ " := " ++ packU256Word rv limb ++ nl, nm, s5)
  | none =>
      let (av, s5) := context.fresh s4
      let (rv, s6) := context.fresh s5
      let (nm, s7) := context.fresh (context.rememberWide s6 cacheKey rv)
      let shift :=
        match direction with
        | .left => "shl(" ++ bits ++ ", " ++ av ++ ")"
        | .right => "shr(" ++ bits ++ ", " ++ av ++ ")"
      let txt := pre ++
        indent ++ "let " ++ av ++ " := " ++ packU256 x0 x1 x2 x3 ++ nl ++
        indent ++ "let " ++ rv ++ " := " ++ shift ++ nl ++
        indent ++ "let " ++ nm ++ " := " ++ packU256Word rv limb ++ nl
      return (txt, nm, s7)

private def emitArith256 (context : Context σ) (op limb : Nat)
    (a0 a1 a2 a3 b0 b1 b2 b3 : Ops.Val) (st : σ) :
    Except String (String × String × σ) := do
  let indent := context.indent
  let (p0, x0, s0) ← context.materialize a0 st
  let (p1, x1, s1) ← context.materialize a1 s0
  let (p2, x2, s2) ← context.materialize a2 s1
  let (p3, x3, s3) ← context.materialize a3 s2
  let (q0, y0, t0) ← context.materialize b0 s3
  let (q1, y1, t1) ← context.materialize b1 t0
  let (q2, y2, t2) ← context.materialize b2 t1
  let (q3, y3, t3) ← context.materialize b3 t2
  let cacheKey :=
    "arith256|" ++ toString op ++ "|" ++ context.valKey a0 ++ "|" ++ context.valKey a1 ++ "|" ++
      context.valKey a2 ++ "|" ++ context.valKey a3 ++ "|" ++ context.valKey b0 ++ "|" ++
      context.valKey b1 ++ "|" ++ context.valKey b2 ++ "|" ++ context.valKey b3
  match context.lookupWide t3 cacheKey with
  | some rv =>
      let (nm, t4) := context.fresh t3
      return (p0 ++ p1 ++ p2 ++ p3 ++ q0 ++ q1 ++ q2 ++ q3 ++
        indent ++ "let " ++ nm ++ " := " ++ packU256Word rv limb ++ nl, nm, t4)
  | none =>
      let (av, t4) := context.fresh t3
      let (bv, t5) := context.fresh t4
      let (rv, t6) := context.fresh t5
      let (nm, t7) := context.fresh (context.rememberWide t6 cacheKey rv)
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

def emitQuery (context : Context σ) (query : WideWord.Query) (operands : Array Ops.Val)
    (st : σ) : Except String (String × String × σ) :=
  match query, operands.toList with
  | .ge256, [a0, a1, a2, a3, b0, b1, b2, b3] =>
      emitCompare256 context .ge a0 a1 a2 a3 b0 b1 b2 b3 st
  | .compare256 comparison, [a0, a1, a2, a3, b0, b1, b2, b3] =>
      emitCompare256 context comparison a0 a1 a2 a3 b0 b1 b2 b3 st
  | .eq20, [a0, a1, a2, b0, b1, b2] =>
      emitEq20 context a0 a1 a2 b0 b1 b2 st
  | .bitwise256 operation limb, [a0, a1, a2, a3, b0, b1, b2, b3] =>
      emitBitwise256 context operation limb a0 a1 a2 a3 b0 b1 b2 b3 st
  | .not256 limb, [a0, a1, a2, a3] =>
      emitNot256 context limb a0 a1 a2 a3 st
  | .shift256 direction limb, [a0, a1, a2, a3, amount] =>
      emitShift256 context direction limb a0 a1 a2 a3 amount st
  | .arith256 op limb, [a0, a1, a2, a3, b0, b1, b2, b3] =>
      emitArith256 context op limb a0 a1 a2 a3 b0 b1 b2 b3 st
  | _, _ =>
      .error s!"extract/unsupported: evm wide-word query arity {operands.size}"

end ProofForge.Evm.WideWord.Emit
