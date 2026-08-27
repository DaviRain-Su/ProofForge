import ProofForge.Evm.NativeFx
import ProofForge.Evm.Ops
import ProofForge.Crypto.Keccak

namespace ProofForge.Evm.NativeFx.Emit

open ProofForge.Crypto

private def nl : String := "\n"
private def revert0 : String := "revert(0, 0)"

private def packU256 (w0 w1 w2 w3 : String) : String :=
  "or(or(" ++ w0 ++ ", shl(64, " ++ w1 ++ ")), or(shl(128, " ++ w2 ++ "), shl(192, " ++ w3 ++ ")))"

/-- Call the shared runtime helper that packs three little-endian Addr20 limbs into an
ABI address word at `memory[0..31]`. -/
private def packAddrMstore8 (indent w0 w1 w2 : String) : String :=
  indent ++ "pf_store_addr20(0, " ++ w0 ++ ", " ++ w1 ++ ", " ++ w2 ++ ")" ++ nl

structure Context (σ : Type) where
  materialize : Ops.Val → σ → Except String (String × String × σ)
  fresh : σ → String × σ
  indent : String

private def emitDeposit (context : Context σ) (amount : Ops.Val) (st : σ) :
    Except String (String × String × σ) := do
  let indent := context.indent
  let (pre, amt, st') ← context.materialize amount st
  let txt := pre ++
    indent ++ "if iszero(eq(callvalue(), " ++ amt ++ ")) { " ++ revert0 ++ " }" ++ nl
  return (txt, amt, st')

private def emitDeposit256 (context : Context σ) (a0 a1 a2 a3 : Ops.Val) (st : σ) :
    Except String (String × String × σ) := do
  let indent := context.indent
  let (p0, x0, s0) ← context.materialize a0 st
  let (p1, x1, s1) ← context.materialize a1 s0
  let (p2, x2, s2) ← context.materialize a2 s1
  let (p3, x3, s3) ← context.materialize a3 s2
  let (amt, s4) := context.fresh s3
  let txt := p0 ++ p1 ++ p2 ++ p3 ++
    indent ++ "let " ++ amt ++ " := " ++ packU256 x0 x1 x2 x3 ++ nl ++
    indent ++ "if iszero(eq(callvalue(), " ++ amt ++ ")) { " ++ revert0 ++ " }" ++ nl
  return (txt, x0, s4)

private def emitSendEth (context : Context σ) (w0 w1 w2 amount : Ops.Val) (st : σ) :
    Except String (String × String × σ) := do
  let indent := context.indent
  let (p0, a0, st0) ← context.materialize w0 st
  let (p1, a1, st1) ← context.materialize w1 st0
  let (p2, a2, st2) ← context.materialize w2 st1
  let (p3, amt, st3) ← context.materialize amount st2
  let (ok, st') := context.fresh st3
  let txt := p0 ++ p1 ++ p2 ++ p3 ++
    indent ++ "if shr(32, " ++ a2 ++ ") { " ++ revert0 ++ " }" ++ nl ++
    indent ++ "mstore(0, 0)" ++ nl ++
    packAddrMstore8 indent a0 a1 a2 ++
    indent ++ "let " ++ ok ++ " := call(gas(), mload(0), " ++ amt ++
      ", 0, 0, 0, 0)" ++ nl ++
    indent ++ "if iszero(" ++ ok ++ ") { " ++ revert0 ++ " }" ++ nl
  return (txt, amt, st')

private def emitSendEth256 (context : Context σ)
    (w0 w1 w2 a0 a1 a2 a3 : Ops.Val) (st : σ) :
    Except String (String × String × σ) := do
  let indent := context.indent
  let (p0, d0, s0) ← context.materialize w0 st
  let (p1, d1, s1) ← context.materialize w1 s0
  let (p2, d2, s2) ← context.materialize w2 s1
  let (q0, x0, s3) ← context.materialize a0 s2
  let (q1, x1, s4) ← context.materialize a1 s3
  let (q2, x2, s5) ← context.materialize a2 s4
  let (q3, x3, s6) ← context.materialize a3 s5
  let (amt, s7) := context.fresh s6
  let (ok, s8) := context.fresh s7
  let txt := p0 ++ p1 ++ p2 ++ q0 ++ q1 ++ q2 ++ q3 ++
    indent ++ "if shr(32, " ++ d2 ++ ") { " ++ revert0 ++ " }" ++ nl ++
    indent ++ "mstore(0, 0)" ++ nl ++
    packAddrMstore8 indent d0 d1 d2 ++
    indent ++ "let " ++ amt ++ " := " ++ packU256 x0 x1 x2 x3 ++ nl ++
    indent ++ "let " ++ ok ++ " := call(gas(), mload(0), " ++ amt ++
      ", 0, 0, 0, 0)" ++ nl ++
    indent ++ "if iszero(" ++ ok ++ ") { " ++ revert0 ++ " }" ++ nl
  return (txt, x0, s8)

private def emitLog (context : Context σ) (name : String) (amount : Ops.Val) (st : σ) :
    Except String (String × String × σ) := do
  let indent := context.indent
  let (pre, amt, st') ← context.materialize amount st
  let txt := pre ++
    indent ++ "mstore(0, " ++ amt ++ ")" ++ nl ++
    indent ++ "log1(0, 32, 0x" ++
      Keccak.keccak256HexOfString (name ++ "(uint64)") ++ ")" ++ nl
  return (txt, amt, st')

private def emitLogTransfer256 (context : Context σ)
    (f0 f1 f2 t0 t1 t2 a0 a1 a2 a3 : Ops.Val) (st : σ) :
    Except String (String × String × σ) := do
  let indent := context.indent
  let (p0, x0, s0) ← context.materialize f0 st
  let (p1, x1, s1) ← context.materialize f1 s0
  let (p2, x2, s2) ← context.materialize f2 s1
  let (q0, y0, s3) ← context.materialize t0 s2
  let (q1, y1, s4) ← context.materialize t1 s3
  let (q2, y2, s5) ← context.materialize t2 s4
  let (r0, z0, s6) ← context.materialize a0 s5
  let (r1, z1, s7) ← context.materialize a1 s6
  let (r2, z2, s8) ← context.materialize a2 s7
  let (r3, z3, s9) ← context.materialize a3 s8
  let (fromT, s10) := context.fresh s9
  let (toT, s11) := context.fresh s10
  let (amt, s12) := context.fresh s11
  let txt := p0 ++ p1 ++ p2 ++ q0 ++ q1 ++ q2 ++ r0 ++ r1 ++ r2 ++ r3 ++
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
  return (txt, z0, s12)

private def emitLogApproval256 (context : Context σ)
    (o0 o1 o2 sp0 sp1 sp2 a0 a1 a2 a3 : Ops.Val) (st : σ) :
    Except String (String × String × σ) := do
  let indent := context.indent
  let (p0, x0, s0) ← context.materialize o0 st
  let (p1, x1, s1) ← context.materialize o1 s0
  let (p2, x2, s2) ← context.materialize o2 s1
  let (q0, y0, s3) ← context.materialize sp0 s2
  let (q1, y1, s4) ← context.materialize sp1 s3
  let (q2, y2, s5) ← context.materialize sp2 s4
  let (r0, z0, s6) ← context.materialize a0 s5
  let (r1, z1, s7) ← context.materialize a1 s6
  let (r2, z2, s8) ← context.materialize a2 s7
  let (r3, z3, s9) ← context.materialize a3 s8
  let (ownT, s10) := context.fresh s9
  let (spdT, s11) := context.fresh s10
  let (amt, s12) := context.fresh s11
  let txt := p0 ++ p1 ++ p2 ++ q0 ++ q1 ++ q2 ++ r0 ++ r1 ++ r2 ++ r3 ++
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
  return (txt, z0, s12)

private def emitRevertInsufficient (context : Context σ)
    (h0 h1 h2 h3 w0 w1 w2 w3 : Ops.Val) (st : σ) :
    Except String (String × String × σ) := do
  let indent := context.indent
  let (p0, x0, s0) ← context.materialize h0 st
  let (p1, x1, s1) ← context.materialize h1 s0
  let (p2, x2, s2) ← context.materialize h2 s1
  let (p3, x3, s3) ← context.materialize h3 s2
  let (q0, y0, s4) ← context.materialize w0 s3
  let (q1, y1, s5) ← context.materialize w1 s4
  let (q2, y2, s6) ← context.materialize w2 s5
  let (q3, y3, s7) ← context.materialize w3 s6
  let sel := Keccak.selector "Insufficient" #["uint256", "uint256"]
  let txt := p0 ++ p1 ++ p2 ++ p3 ++ q0 ++ q1 ++ q2 ++ q3 ++
    indent ++ "mstore(0, shl(224, 0x" ++ sel ++ "))" ++ nl ++
    indent ++ "mstore(4, " ++ packU256 x0 x1 x2 x3 ++ ")" ++ nl ++
    indent ++ "mstore(36, " ++ packU256 y0 y1 y2 y3 ++ ")" ++ nl ++
    indent ++ "revert(0, 68)" ++ nl
  return (txt, x0, s7)

private def emitRevertUnauthorized (context : Context σ)
    (w0 w1 w2 : Ops.Val) (st : σ) : Except String (String × String × σ) := do
  let indent := context.indent
  let (p0, a0, s0) ← context.materialize w0 st
  let (p1, a1, s1) ← context.materialize w1 s0
  let (p2, a2, s2) ← context.materialize w2 s1
  let sel := Keccak.selector "Unauthorized" #["address"]
  let txt := p0 ++ p1 ++ p2 ++
    indent ++ "mstore(0, 0)" ++ nl ++
    packAddrMstore8 indent a0 a1 a2 ++
    indent ++ "let pf_who := mload(0)" ++ nl ++
    indent ++ "mstore(0, shl(224, 0x" ++ sel ++ "))" ++ nl ++
    indent ++ "mstore(4, pf_who)" ++ nl ++
    indent ++ "revert(0, 36)" ++ nl
  return (txt, a0, s2)

private def emitRevertZeroAddress (context : Context σ) (st : σ) :
    Except String (String × String × σ) :=
  let indent := context.indent
  let sel := Keccak.selector "ZeroAddress" #[]
  let txt :=
    indent ++ "mstore(0, shl(224, 0x" ++ sel ++ "))" ++ nl ++
    indent ++ "revert(0, 4)" ++ nl
  pure (txt, "0", st)

private def emitRevertPaused (context : Context σ) (st : σ) :
    Except String (String × String × σ) :=
  let indent := context.indent
  let sel := Keccak.selector "Paused" #[]
  let txt :=
    indent ++ "mstore(0, shl(224, 0x" ++ sel ++ "))" ++ nl ++
    indent ++ "revert(0, 4)" ++ nl
  pure (txt, "0", st)

private def emitRevertCapExceeded (context : Context σ) (st : σ) :
    Except String (String × String × σ) :=
  let indent := context.indent
  let sel := Keccak.selector "CapExceeded" #[]
  let txt :=
    indent ++ "mstore(0, shl(224, 0x" ++ sel ++ "))" ++ nl ++
    indent ++ "revert(0, 4)" ++ nl
  pure (txt, "0", st)

private def emitReceive (context : Context σ) (st : σ) :
    Except String (String × String × σ) :=
  let indent := context.indent
  let txt := indent ++ "let pf_recv := callvalue()" ++ nl
  pure (txt, "pf_recv", st)

def emitCall (context : Context σ) (call : NativeFx.Call Ops.Val) (st : σ) :
    Except String (String × String × σ) :=
  match call with
  | .deposit amount => emitDeposit context amount st
  | .deposit256 a0 a1 a2 a3 => emitDeposit256 context a0 a1 a2 a3 st
  | .sendEth w0 w1 w2 amount => emitSendEth context w0 w1 w2 amount st
  | .sendEth256 w0 w1 w2 a0 a1 a2 a3 =>
      emitSendEth256 context w0 w1 w2 a0 a1 a2 a3 st
  | .log name amount => emitLog context name amount st
  | .logTransfer256 f0 f1 f2 t0 t1 t2 a0 a1 a2 a3 =>
      emitLogTransfer256 context f0 f1 f2 t0 t1 t2 a0 a1 a2 a3 st
  | .logApproval256 o0 o1 o2 s0 s1 s2 a0 a1 a2 a3 =>
      emitLogApproval256 context o0 o1 o2 s0 s1 s2 a0 a1 a2 a3 st
  | .revertInsufficient h0 h1 h2 h3 w0 w1 w2 w3 =>
      emitRevertInsufficient context h0 h1 h2 h3 w0 w1 w2 w3 st
  | .revertUnauthorized w0 w1 w2 => emitRevertUnauthorized context w0 w1 w2 st
  | .revertZeroAddress => emitRevertZeroAddress context st
  | .revertPaused => emitRevertPaused context st
  | .revertCapExceeded => emitRevertCapExceeded context st
  | .receive => emitReceive context st

end ProofForge.Evm.NativeFx.Emit
