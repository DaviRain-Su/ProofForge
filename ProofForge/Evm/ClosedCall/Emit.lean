import ProofForge.Evm.ClosedCall
import ProofForge.Evm.CallResult.Emit
import ProofForge.Evm.LogError.Emit
import ProofForge.Evm.Precompile.Emit
import ProofForge.Evm.Ops
import ProofForge.Crypto.Keccak

namespace ProofForge.Evm.ClosedCall.Emit

open ProofForge.Crypto

private def nl : String := "\n"
private def u64MaxYul : String := "0xffffffffffffffff"
private def revert0 : String := "revert(0, 0)"

private def packU256 (w0 w1 w2 w3 : String) : String :=
  "or(or(" ++ w0 ++ ", shl(64, " ++ w1 ++ ")), or(shl(128, " ++ w2 ++ "), shl(192, " ++ w3 ++ ")))"

private def packU256Word (src : String) (word : Nat) : String :=
  "and(shr(" ++ toString (64 * word) ++ ", " ++ src ++ "), " ++ u64MaxYul ++ ")"

/-- Call the shared runtime helper that packs three little-endian Addr20 limbs into an
ABI address word at `memory[off..off+31]`. -/
private def packAddrMstore8 (indent w0 w1 w2 : String) : String :=
  indent ++ "pf_store_addr20(0, " ++ w0 ++ ", " ++ w1 ++ ", " ++ w2 ++ ")" ++ nl

/-- Pack three Addr20 limbs into calldata at `off..off+19` (transfer dest starts at 16). -/
private def packAddrAt (indent : String) (off : Nat) (w0 w1 w2 : String) : String :=
  indent ++ "pf_store_addr20(" ++ toString (off - 12) ++ ", " ++ w0 ++ ", " ++ w1 ++
    ", " ++ w2 ++ ")" ++ nl

/-- Pack source-order fixed bytes into one ABI bytes32 word. -/
private def packBytes32At (indent : String) (off : Nat) (w0 w1 w2 w3 : String) : String :=
  indent ++ "pf_store_fixed_bytes(" ++ toString off ++ ", " ++ w0 ++ ", " ++ w1 ++
    ", " ++ w2 ++ ", " ++ w3 ++ ", 32)" ++ nl

private def eip712DomainTypeHash : String :=
  Keccak.keccak256HexOfString
    "EIP712Domain(string name,string version,uint256 chainId,address verifyingContract)"

private def eip712PermitTypeHash : String :=
  Keccak.keccak256HexOfString
    "Permit(address owner,address spender,uint256 value,uint256 nonce,uint256 deadline)"

private def eip712NameHash : String := Keccak.keccak256HexOfString "Token"

private def eip712VersionHash : String := Keccak.keccak256HexOfString "1"

structure Context (σ : Type) where
  materialize : Ops.Val → σ → Except String (String × String × σ)
  fresh : σ → String × σ
  rememberWide : σ → String → String → σ
  lookupWide : σ → String → Option String
  valKey : Ops.Val → String
  indent : String

/-- Project the shared typed call-result emission context (EVM-RT-2a). Every closed ERC-20 /
WETH / Uniswap / permit external call below is emitted through `CallResult.Emit.emit`, so the
success, returndata-length, and bool-word gates have exactly one spelling. -/
private def Context.callResult (context : Context σ) : CallResult.Emit.Context σ :=
  { fresh := context.fresh, indent := context.indent }

/-- Project the shared typed log/error emission context (EVM-RT-2b). Permit below spells its
Approval LOG3 and its nested Expired / Unauthorized custom-error reverts through
`Evm.LogError.Emit`, the same interpreter the NativeFx effects consume, so the memory geometry
has exactly one spelling. Nested gates pass a deepened indent; the interpreter allocates no
fresh names, so emission order and output are unchanged. -/
private def Context.logError (context : Context σ) : LogError.Emit.Context :=
  { indent := context.indent }

/-- Project the typed ecrecover precompile emission context (EVM-RT-2d). Permit below spells
its signer recovery through `Evm.Precompile.Emit`, the sole interpreter of the closed
precompile contract, so the STATICCALL success, exact-32-byte returndata, and nonzero-signer
gates have exactly one spelling instead of a hand-written inline assumption. -/
private def Context.precompile (context : Context σ) : Precompile.Emit.Context σ :=
  { fresh := context.fresh, indent := context.indent }

private def emitDomainSeparator (context : Context σ) (st : σ) : String × String × σ :=
  let indent := context.indent
  match context.lookupWide st "domsep" with
  | some ret => ("", ret, st)
  | none =>
    let (nameH, st1) := context.fresh st
    let (verH, st2) := context.fresh st1
    let (domainH, st3) := context.fresh st2
    let txt :=
      indent ++ "let " ++ nameH ++ " := 0x" ++ eip712NameHash ++ nl ++
      indent ++ "let " ++ verH ++ " := 0x" ++ eip712VersionHash ++ nl ++
      indent ++ "mstore(0, 0x" ++ eip712DomainTypeHash ++ ")" ++ nl ++
      indent ++ "mstore(32, " ++ nameH ++ ")" ++ nl ++
      indent ++ "mstore(64, " ++ verH ++ ")" ++ nl ++
      indent ++ "mstore(96, chainid())" ++ nl ++
      indent ++ "mstore(128, address())" ++ nl ++
      indent ++ "let " ++ domainH ++ " := keccak256(0, 160)" ++ nl
    (txt, domainH, context.rememberWide st3 "domsep" domainH)

private def emitBalance256 (context : Context σ) (limb : Nat)
    (tw0 tw1 tw2 : Ops.Val) (st : σ) : Except String (String × String × σ) := do
  let indent := context.indent
  let (p0, a0, s0) ← context.materialize tw0 st
  let (p1, a1, s1) ← context.materialize tw1 s0
  let (p2, a2, s2) ← context.materialize tw2 s1
  let cacheKey := "tbal256|" ++ context.valKey tw0 ++ "|" ++ context.valKey tw1 ++ "|" ++ context.valKey tw2
  match context.lookupWide s2 cacheKey with
  | some ret =>
      let (nm, s3) := context.fresh s2
      return (p0 ++ p1 ++ p2 ++
        indent ++ "let " ++ nm ++ " := " ++ packU256Word ret limb ++ nl, nm, s3)
  | none =>
      let (tok, s3) := context.fresh s2
      let (callTxt, word, s5) ← CallResult.Emit.emit context.callResult
        (.staticWord 36) tok none s3
      let some ret := word
        | throw "extract/unsupported: evm call-result missing word"
      let (nm, s6) := context.fresh (context.rememberWide s5 cacheKey ret)
      let txt := p0 ++ p1 ++ p2 ++
        indent ++ "if shr(32, " ++ a2 ++ ") { " ++ revert0 ++ " }" ++ nl ++
        indent ++ "mstore(0, 0)" ++ nl ++
        packAddrMstore8 indent a0 a1 a2 ++
        indent ++ "let " ++ tok ++ " := mload(0)" ++ nl ++
        indent ++ "mstore(0, 0x70a0823100000000000000000000000000000000000000000000000000000000)" ++ nl ++
        indent ++ "mstore(4, address())" ++ nl ++
        callTxt ++
        indent ++ "let " ++ nm ++ " := " ++ packU256Word ret limb ++ nl
      return (txt, nm, s6)

private def emitAllowance256 (context : Context σ) (limb : Nat)
    (tw0 tw1 tw2 o0 o1 o2 s0 s1 s2 : Ops.Val) (st : σ) :
    Except String (String × String × σ) := do
  let indent := context.indent
  let (p0, a0, st0) ← context.materialize tw0 st
  let (p1, a1, st1) ← context.materialize tw1 st0
  let (p2, a2, st2) ← context.materialize tw2 st1
  let (q0, b0, st3) ← context.materialize o0 st2
  let (q1, b1, st4) ← context.materialize o1 st3
  let (q2, b2, st5) ← context.materialize o2 st4
  let (r0, c0, st6) ← context.materialize s0 st5
  let (r1, c1, st7) ← context.materialize s1 st6
  let (r2, c2, st8) ← context.materialize s2 st7
  let cacheKey :=
    "tallow256|" ++ context.valKey tw0 ++ "|" ++ context.valKey tw1 ++ "|" ++ context.valKey tw2 ++ "|" ++
      context.valKey o0 ++ "|" ++ context.valKey o1 ++ "|" ++ context.valKey o2 ++ "|" ++
      context.valKey s0 ++ "|" ++ context.valKey s1 ++ "|" ++ context.valKey s2
  match context.lookupWide st8 cacheKey with
  | some ret =>
      let (nm, st9) := context.fresh st8
      return (p0 ++ p1 ++ p2 ++ q0 ++ q1 ++ q2 ++ r0 ++ r1 ++ r2 ++
        indent ++ "let " ++ nm ++ " := " ++ packU256Word ret limb ++ nl, nm, st9)
  | none =>
      let (tok, st9) := context.fresh st8
      let (callTxt, word, st11) ← CallResult.Emit.emit context.callResult
        (.staticWord 68) tok none st9
      let some ret := word
        | throw "extract/unsupported: evm call-result missing word"
      let (nm, st12) := context.fresh (context.rememberWide st11 cacheKey ret)
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
        callTxt ++
        indent ++ "let " ++ nm ++ " := " ++ packU256Word ret limb ++ nl
      return (txt, nm, st12)

def emitQuery (context : Context σ) (query : ClosedCall.Query) (operands : Array Ops.Val)
    (st : σ) : Except String (String × String × σ) :=
  match query, operands.toList with
  | .balance256 limb, [tw0, tw1, tw2] => emitBalance256 context limb tw0 tw1 tw2 st
  | .allowance256 limb, [tw0, tw1, tw2, o0, o1, o2, s0, s1, s2] =>
      emitAllowance256 context limb tw0 tw1 tw2 o0 o1 o2 s0 s1 s2 st
  | _, _ => .error s!"extract/unsupported: evm closed-call query arity {operands.size}"

private def emitTransfer (context : Context σ)
    (tw0 tw1 tw2 dw0 dw1 dw2 amount : Ops.Val) (st : σ) :
    Except String (String × String × σ) := do
  let indent := context.indent
  let (p0, a0, s0) ← context.materialize tw0 st
  let (p1, a1, s1) ← context.materialize tw1 s0
  let (p2, a2, s2) ← context.materialize tw2 s1
  let (q0, d0, s3) ← context.materialize dw0 s2
  let (q1, d1, s4) ← context.materialize dw1 s3
  let (q2, d2, s5) ← context.materialize dw2 s4
  let (pa, amt, s6) ← context.materialize amount s5
  let (tok, s7) := context.fresh s6
  let (callTxt, _, s9) ← CallResult.Emit.emit context.callResult
    (.erc20Mutation 68) tok none s7
  let txt := p0 ++ p1 ++ p2 ++ q0 ++ q1 ++ q2 ++ pa ++
    indent ++ "if shr(32, " ++ a2 ++ ") { " ++ revert0 ++ " }" ++ nl ++
    indent ++ "if shr(32, " ++ d2 ++ ") { " ++ revert0 ++ " }" ++ nl ++
    indent ++ "mstore(0, 0)" ++ nl ++
    packAddrMstore8 indent a0 a1 a2 ++
    indent ++ "let " ++ tok ++ " := mload(0)" ++ nl ++
    indent ++ "mstore(0, 0xa9059cbb00000000000000000000000000000000000000000000000000000000)" ++ nl ++
    packAddrAt indent 16 d0 d1 d2 ++
    indent ++ "mstore(36, " ++ amt ++ ")" ++ nl ++
    callTxt
  return (txt, amt, s9)

private def emitTransfer256 (context : Context σ)
    (tw0 tw1 tw2 dw0 dw1 dw2 a0 a1 a2 a3 : Ops.Val) (st : σ) :
    Except String (String × String × σ) := do
  let indent := context.indent
  let (p0, t0, s0) ← context.materialize tw0 st
  let (p1, t1, s1) ← context.materialize tw1 s0
  let (p2, t2, s2) ← context.materialize tw2 s1
  let (q0, d0, s3) ← context.materialize dw0 s2
  let (q1, d1, s4) ← context.materialize dw1 s3
  let (q2, d2, s5) ← context.materialize dw2 s4
  let (r0, x0, s6) ← context.materialize a0 s5
  let (r1, x1, s7) ← context.materialize a1 s6
  let (r2, x2, s8) ← context.materialize a2 s7
  let (r3, x3, s9) ← context.materialize a3 s8
  let (tok, s10) := context.fresh s9
  let (amt, s11) := context.fresh s10
  let (callTxt, _, s13) ← CallResult.Emit.emit context.callResult
    (.erc20Mutation 68) tok none s11
  let txt := p0 ++ p1 ++ p2 ++ q0 ++ q1 ++ q2 ++ r0 ++ r1 ++ r2 ++ r3 ++
    indent ++ "if shr(32, " ++ t2 ++ ") { " ++ revert0 ++ " }" ++ nl ++
    indent ++ "if shr(32, " ++ d2 ++ ") { " ++ revert0 ++ " }" ++ nl ++
    indent ++ "mstore(0, 0)" ++ nl ++
    packAddrMstore8 indent t0 t1 t2 ++
    indent ++ "let " ++ tok ++ " := mload(0)" ++ nl ++
    indent ++ "mstore(0, 0xa9059cbb00000000000000000000000000000000000000000000000000000000)" ++ nl ++
    packAddrAt indent 16 d0 d1 d2 ++
    indent ++ "let " ++ amt ++ " := " ++ packU256 x0 x1 x2 x3 ++ nl ++
    indent ++ "mstore(36, " ++ amt ++ ")" ++ nl ++
    callTxt
  return (txt, x0, s13)

private def emitApprove256 (context : Context σ)
    (tw0 tw1 tw2 sw0 sw1 sw2 a0 a1 a2 a3 : Ops.Val) (st : σ) :
    Except String (String × String × σ) := do
  let indent := context.indent
  let (p0, t0, s0) ← context.materialize tw0 st
  let (p1, t1, s1) ← context.materialize tw1 s0
  let (p2, t2, s2) ← context.materialize tw2 s1
  let (q0, d0, s3) ← context.materialize sw0 s2
  let (q1, d1, s4) ← context.materialize sw1 s3
  let (q2, d2, s5) ← context.materialize sw2 s4
  let (r0, x0, s6) ← context.materialize a0 s5
  let (r1, x1, s7) ← context.materialize a1 s6
  let (r2, x2, s8) ← context.materialize a2 s7
  let (r3, x3, s9) ← context.materialize a3 s8
  let (tok, s10) := context.fresh s9
  let (amt, s11) := context.fresh s10
  let (callTxt, _, s13) ← CallResult.Emit.emit context.callResult
    (.erc20Mutation 68) tok none s11
  let txt := p0 ++ p1 ++ p2 ++ q0 ++ q1 ++ q2 ++ r0 ++ r1 ++ r2 ++ r3 ++
    indent ++ "if shr(32, " ++ t2 ++ ") { " ++ revert0 ++ " }" ++ nl ++
    indent ++ "if shr(32, " ++ d2 ++ ") { " ++ revert0 ++ " }" ++ nl ++
    indent ++ "mstore(0, 0)" ++ nl ++
    packAddrMstore8 indent t0 t1 t2 ++
    indent ++ "let " ++ tok ++ " := mload(0)" ++ nl ++
    indent ++ "mstore(0, 0x095ea7b300000000000000000000000000000000000000000000000000000000)" ++ nl ++
    packAddrAt indent 16 d0 d1 d2 ++
    indent ++ "let " ++ amt ++ " := " ++ packU256 x0 x1 x2 x3 ++ nl ++
    indent ++ "mstore(36, " ++ amt ++ ")" ++ nl ++
    callTxt
  return (txt, x0, s13)

private def emitTransferFrom256 (context : Context σ)
    (tw0 tw1 tw2 ow0 ow1 ow2 dw0 dw1 dw2 a0 a1 a2 a3 : Ops.Val) (st : σ) :
    Except String (String × String × σ) := do
  let indent := context.indent
  let (p0, t0, s0) ← context.materialize tw0 st
  let (p1, t1, s1) ← context.materialize tw1 s0
  let (p2, t2, s2) ← context.materialize tw2 s1
  let (q0, o0, s3) ← context.materialize ow0 s2
  let (q1, o1, s4) ← context.materialize ow1 s3
  let (q2, o2, s5) ← context.materialize ow2 s4
  let (r0, d0, s6) ← context.materialize dw0 s5
  let (r1, d1, s7) ← context.materialize dw1 s6
  let (r2, d2, s8) ← context.materialize dw2 s7
  let (u0, x0, s9) ← context.materialize a0 s8
  let (u1, x1, s10) ← context.materialize a1 s9
  let (u2, x2, s11) ← context.materialize a2 s10
  let (u3, x3, s12) ← context.materialize a3 s11
  let (tok, s13) := context.fresh s12
  let (amt, s14) := context.fresh s13
  let (callTxt, _, s16) ← CallResult.Emit.emit context.callResult
    (.erc20Mutation 100) tok none s14
  let txt := p0 ++ p1 ++ p2 ++ q0 ++ q1 ++ q2 ++ r0 ++ r1 ++ r2 ++ u0 ++ u1 ++ u2 ++ u3 ++
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
    callTxt
  return (txt, x0, s16)

private def emitBalanceOfSelf (context : Context σ) (tw0 tw1 tw2 : Ops.Val) (st : σ) :
    Except String (String × String × σ) := do
  let indent := context.indent
  let (p0, a0, s0) ← context.materialize tw0 st
  let (p1, a1, s1) ← context.materialize tw1 s0
  let (p2, a2, s2) ← context.materialize tw2 s1
  let (tok, s3) := context.fresh s2
  let (callTxt, word, s5) ← CallResult.Emit.emit context.callResult
    (.staticWord 36) tok none s3
  let some ret := word
    | throw "extract/unsupported: evm call-result missing word"
  let txt := p0 ++ p1 ++ p2 ++
    indent ++ "if shr(32, " ++ a2 ++ ") { " ++ revert0 ++ " }" ++ nl ++
    indent ++ "mstore(0, 0)" ++ nl ++
    packAddrMstore8 indent a0 a1 a2 ++
    indent ++ "let " ++ tok ++ " := mload(0)" ++ nl ++
    indent ++ "mstore(0, 0x70a0823100000000000000000000000000000000000000000000000000000000)" ++ nl ++
    indent ++ "mstore(4, address())" ++ nl ++
    callTxt ++
    indent ++ "if shr(64, " ++ ret ++ ") { " ++ revert0 ++ " }" ++ nl
  return (txt, ret, s5)

private def emitWethDeposit256 (context : Context σ)
    (tw0 tw1 tw2 a0 a1 a2 a3 : Ops.Val) (st : σ) :
    Except String (String × String × σ) := do
  let indent := context.indent
  let (p0, t0, s0) ← context.materialize tw0 st
  let (p1, t1, s1) ← context.materialize tw1 s0
  let (p2, t2, s2) ← context.materialize tw2 s1
  let (r0, x0, s3) ← context.materialize a0 s2
  let (r1, x1, s4) ← context.materialize a1 s3
  let (r2, x2, s5) ← context.materialize a2 s4
  let (r3, x3, s6) ← context.materialize a3 s5
  let (tok, s7) := context.fresh s6
  let (amt, s8) := context.fresh s7
  let (callTxt, _, s9) ← CallResult.Emit.emit context.callResult
    (.successOnly 4 true) tok (some amt) s8
  let txt := p0 ++ p1 ++ p2 ++ r0 ++ r1 ++ r2 ++ r3 ++
    indent ++ "if shr(32, " ++ t2 ++ ") { " ++ revert0 ++ " }" ++ nl ++
    indent ++ "mstore(0, 0)" ++ nl ++
    packAddrMstore8 indent t0 t1 t2 ++
    indent ++ "let " ++ tok ++ " := mload(0)" ++ nl ++
    indent ++ "mstore(0, 0xd0e30db000000000000000000000000000000000000000000000000000000000)" ++ nl ++
    indent ++ "let " ++ amt ++ " := " ++ packU256 x0 x1 x2 x3 ++ nl ++
    callTxt
  return (txt, x0, s9)

private def emitWethWithdraw256 (context : Context σ)
    (tw0 tw1 tw2 a0 a1 a2 a3 : Ops.Val) (st : σ) :
    Except String (String × String × σ) := do
  let indent := context.indent
  let (p0, t0, s0) ← context.materialize tw0 st
  let (p1, t1, s1) ← context.materialize tw1 s0
  let (p2, t2, s2) ← context.materialize tw2 s1
  let (r0, x0, s3) ← context.materialize a0 s2
  let (r1, x1, s4) ← context.materialize a1 s3
  let (r2, x2, s5) ← context.materialize a2 s4
  let (r3, x3, s6) ← context.materialize a3 s5
  let (tok, s7) := context.fresh s6
  let (amt, s8) := context.fresh s7
  let (callTxt, _, s10) ← CallResult.Emit.emit context.callResult
    (.erc20Mutation 36) tok none s8
  let txt := p0 ++ p1 ++ p2 ++ r0 ++ r1 ++ r2 ++ r3 ++
    indent ++ "if shr(32, " ++ t2 ++ ") { " ++ revert0 ++ " }" ++ nl ++
    indent ++ "mstore(0, 0)" ++ nl ++
    packAddrMstore8 indent t0 t1 t2 ++
    indent ++ "let " ++ tok ++ " := mload(0)" ++ nl ++
    indent ++ "mstore(0, 0x2e1a7d4d00000000000000000000000000000000000000000000000000000000)" ++ nl ++
    indent ++ "let " ++ amt ++ " := " ++ packU256 x0 x1 x2 x3 ++ nl ++
    indent ++ "mstore(4, " ++ amt ++ ")" ++ nl ++
    callTxt
  return (txt, x0, s10)

private def emitSwapExact2 (context : Context σ)
    (rw0 rw1 rw2 a0 a1 a2 b0 b1 b2 i0 i1 i2 i3 m0 m1 m2 m3 : Ops.Val) (st : σ) :
    Except String (String × String × σ) := do
  let indent := context.indent
  let (p0, t0, s0) ← context.materialize rw0 st
  let (p1, t1, s1) ← context.materialize rw1 s0
  let (p2, t2, s2) ← context.materialize rw2 s1
  let (q0, x0, s3) ← context.materialize a0 s2
  let (q1, x1, s4) ← context.materialize a1 s3
  let (q2, x2, s5) ← context.materialize a2 s4
  let (r0, y0, s6) ← context.materialize b0 s5
  let (r1, y1, s7) ← context.materialize b1 s6
  let (r2, y2, s8) ← context.materialize b2 s7
  let (u0, n0, s9) ← context.materialize i0 s8
  let (u1, n1, s10) ← context.materialize i1 s9
  let (u2, n2, s11) ← context.materialize i2 s10
  let (u3, n3, s12) ← context.materialize i3 s11
  let (v0, k0, s13) ← context.materialize m0 s12
  let (v1, k1, s14) ← context.materialize m1 s13
  let (v2, k2, s15) ← context.materialize m2 s14
  let (v3, k3, s16) ← context.materialize m3 s15
  let (tok, s17) := context.fresh s16
  let (amt, s18) := context.fresh s17
  let (minv, s19) := context.fresh s18
  let (callTxt, _, s20) ← CallResult.Emit.emit context.callResult
    (.successOnly 260) tok none s19
  let txt := p0 ++ p1 ++ p2 ++ q0 ++ q1 ++ q2 ++ r0 ++ r1 ++ r2 ++
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
    callTxt
  return (txt, n0, s20)

private def emitSwapExact3 (context : Context σ)
    (rw0 rw1 rw2 a0 a1 a2 b0 b1 b2 c0 c1 c2 i0 i1 i2 i3 m0 m1 m2 m3 : Ops.Val) (st : σ) :
    Except String (String × String × σ) := do
  let indent := context.indent
  let (p0, t0, s0) ← context.materialize rw0 st
  let (p1, t1, s1) ← context.materialize rw1 s0
  let (p2, t2, s2) ← context.materialize rw2 s1
  let (q0, x0, s3) ← context.materialize a0 s2
  let (q1, x1, s4) ← context.materialize a1 s3
  let (q2, x2, s5) ← context.materialize a2 s4
  let (r0, y0, s6) ← context.materialize b0 s5
  let (r1, y1, s7) ← context.materialize b1 s6
  let (r2, y2, s8) ← context.materialize b2 s7
  let (sA0, z0, s9) ← context.materialize c0 s8
  let (sA1, z1, s10) ← context.materialize c1 s9
  let (sA2, z2, s11) ← context.materialize c2 s10
  let (u0, n0, s12) ← context.materialize i0 s11
  let (u1, n1, s13) ← context.materialize i1 s12
  let (u2, n2, s14) ← context.materialize i2 s13
  let (u3, n3, s15) ← context.materialize i3 s14
  let (v0, k0, s16) ← context.materialize m0 s15
  let (v1, k1, s17) ← context.materialize m1 s16
  let (v2, k2, s18) ← context.materialize m2 s17
  let (v3, k3, s19) ← context.materialize m3 s18
  let (tok, s20) := context.fresh s19
  let (amt, s21) := context.fresh s20
  let (minv, s22) := context.fresh s21
  let (callTxt, _, s23) ← CallResult.Emit.emit context.callResult
    (.successOnly 292) tok none s22
  let txt := p0 ++ p1 ++ p2 ++ q0 ++ q1 ++ q2 ++ r0 ++ r1 ++ r2 ++
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
    callTxt
  return (txt, n0, s23)

private def emitPermit (context : Context σ)
    (o0 o1 o2 sA0 sA1 sA2 v0 v1 v2 v3 d0 d1 d2 d3 vv r0 r1 r2 r3 z0 z1 z2 z3 : Ops.Val)
    (st : σ) : Except String (String × String × σ) := do
  let indent := context.indent
  let (p0, ow0, st0) ← context.materialize o0 st
  let (p1, ow1, st1) ← context.materialize o1 st0
  let (p2, ow2, st2) ← context.materialize o2 st1
  let (q0, sp0, st3) ← context.materialize sA0 st2
  let (q1, sp1, st4) ← context.materialize sA1 st3
  let (q2, sp2, st5) ← context.materialize sA2 st4
  let (u0, n0, st6) ← context.materialize v0 st5
  let (u1, n1, st7) ← context.materialize v1 st6
  let (u2, n2, st8) ← context.materialize v2 st7
  let (u3, n3, st9) ← context.materialize v3 st8
  let (t0, k0, st10) ← context.materialize d0 st9
  let (t1, k1, st11) ← context.materialize d1 st10
  let (t2, k2, st12) ← context.materialize d2 st11
  let (t3, k3, st13) ← context.materialize d3 st12
  let (pv, vbyte, st14) ← context.materialize vv st13
  let (x0, hr0, st15) ← context.materialize r0 st14
  let (x1, hr1, st16) ← context.materialize r1 st15
  let (x2, hr2, st17) ← context.materialize r2 st16
  let (x3, hr3, st18) ← context.materialize r3 st17
  let (y0, hs0, st19) ← context.materialize z0 st18
  let (y1, hs1, st20) ← context.materialize z1 st19
  let (y2, hs2, st21) ← context.materialize z2 st20
  let (y3, hs3, st22) ← context.materialize z3 st21
  let (own, st23) := context.fresh st22
  let (spd, st24) := context.fresh st23
  let (amt, st25) := context.fresh st24
  let (dead, st26) := context.fresh st25
  let (rword, st27) := context.fresh st26
  let (sword, st28) := context.fresh st27
  let (nslot, st29) := context.fresh st28
  let (ntag, st30) := context.fresh st29
  let (nonce, st31) := context.fresh st30
  let (structH, st32) := context.fresh st31
  let (domPre, domainH, st33) := emitDomainSeparator context st32
  let (digest, st34) := context.fresh st33
  let (precompileTxt, signer, st35) ← Precompile.Emit.emit context.precompile
    .ecrecover st34
  let (aslot, st36) := context.fresh st35
  let expiredSel := Keccak.selector "Expired" #[]
  let expiredTxt ← LogError.Emit.emitRevert { indent := indent ++ "  " }
    { selector := expiredSel }
  let unauthorizedTxt ← LogError.Emit.emitRevert { indent := indent ++ "  " }
    { selector := Keccak.selector "Unauthorized" #["address"], args := #[signer] }
  let approvalTxt ← LogError.Emit.emitLog context.logError
    { data := #[amt]
      topics := #["0x" ++ Keccak.keccak256HexOfString "Approval(address,address,uint256)",
        own, spd] }
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
    packBytes32At indent 0 hr0 hr1 hr2 hr3 ++
    indent ++ "let " ++ rword ++ " := mload(0)" ++ nl ++
    packBytes32At indent 0 hs0 hs1 hs2 hs3 ++
    indent ++ "let " ++ sword ++ " := mload(0)" ++ nl ++
    indent ++ "if lt(" ++ dead ++ ", timestamp()) {" ++ nl ++
    expiredTxt ++
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
    precompileTxt
  acc := acc ++
    indent ++ "if iszero(eq(" ++ signer ++ ", " ++ own ++ ")) {" ++ nl ++
    unauthorizedTxt ++
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
    approvalTxt
  return (acc, n0, st36)

private def emitTokenPermit (context : Context σ)
    (tw0 tw1 tw2 ow0 ow1 ow2 sw0 sw1 sw2 v0 v1 v2 v3 d0 d1 d2 d3 vv r0 r1 r2 r3 z0 z1 z2 z3 : Ops.Val)
    (st : σ) : Except String (String × String × σ) := do
  let indent := context.indent
  let (p0, t0, s0) ← context.materialize tw0 st
  let (p1, t1, s1) ← context.materialize tw1 s0
  let (p2, t2, s2) ← context.materialize tw2 s1
  let (q0, o0, s3) ← context.materialize ow0 s2
  let (q1, o1, s4) ← context.materialize ow1 s3
  let (q2, o2, s5) ← context.materialize ow2 s4
  let (rA0, a0, s6) ← context.materialize sw0 s5
  let (rA1, a1, s7) ← context.materialize sw1 s6
  let (rA2, a2, s8) ← context.materialize sw2 s7
  let (u0, n0, s9) ← context.materialize v0 s8
  let (u1, n1, s10) ← context.materialize v1 s9
  let (u2, n2, s11) ← context.materialize v2 s10
  let (u3, n3, s12) ← context.materialize v3 s11
  let (k0p, k0, s13) ← context.materialize d0 s12
  let (k1p, k1, s14) ← context.materialize d1 s13
  let (k2p, k2, s15) ← context.materialize d2 s14
  let (k3p, k3, s16) ← context.materialize d3 s15
  let (pv, vbyte, s17) ← context.materialize vv s16
  let (x0, hr0, s18) ← context.materialize r0 s17
  let (x1, hr1, s19) ← context.materialize r1 s18
  let (x2, hr2, s20) ← context.materialize r2 s19
  let (x3, hr3, s21) ← context.materialize r3 s20
  let (y0, hs0, s22) ← context.materialize z0 s21
  let (y1, hs1, s23) ← context.materialize z1 s22
  let (y2, hs2, s24) ← context.materialize z2 s23
  let (y3, hs3, s25) ← context.materialize z3 s24
  let (tok, s26) := context.fresh s25
  let (amt, s27) := context.fresh s26
  let (dead, s28) := context.fresh s27
  let (callTxt, _, s30) ← CallResult.Emit.emit context.callResult
    (.erc20Mutation 228) tok none s28
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
    packBytes32At indent 164 hr0 hr1 hr2 hr3 ++
    packBytes32At indent 196 hs0 hs1 hs2 hs3 ++
    callTxt
  return (acc, n0, s30)

def emitCall (context : Context σ) (call : ClosedCall.Call Ops.Val) (st : σ) :
    Except String (String × String × σ) :=
  match call with
  | .transfer tw0 tw1 tw2 dw0 dw1 dw2 amount =>
      emitTransfer context tw0 tw1 tw2 dw0 dw1 dw2 amount st
  | .transfer256 tw0 tw1 tw2 dw0 dw1 dw2 a0 a1 a2 a3 =>
      emitTransfer256 context tw0 tw1 tw2 dw0 dw1 dw2 a0 a1 a2 a3 st
  | .approve256 tw0 tw1 tw2 sw0 sw1 sw2 a0 a1 a2 a3 =>
      emitApprove256 context tw0 tw1 tw2 sw0 sw1 sw2 a0 a1 a2 a3 st
  | .transferFrom256 tw0 tw1 tw2 ow0 ow1 ow2 dw0 dw1 dw2 a0 a1 a2 a3 =>
      emitTransferFrom256 context tw0 tw1 tw2 ow0 ow1 ow2 dw0 dw1 dw2 a0 a1 a2 a3 st
  | .balanceOfSelf tw0 tw1 tw2 => emitBalanceOfSelf context tw0 tw1 tw2 st
  | .wethDeposit256 tw0 tw1 tw2 a0 a1 a2 a3 =>
      emitWethDeposit256 context tw0 tw1 tw2 a0 a1 a2 a3 st
  | .wethWithdraw256 tw0 tw1 tw2 a0 a1 a2 a3 =>
      emitWethWithdraw256 context tw0 tw1 tw2 a0 a1 a2 a3 st
  | .swapExact2 rw0 rw1 rw2 a0 a1 a2 b0 b1 b2 i0 i1 i2 i3 m0 m1 m2 m3 =>
      emitSwapExact2 context rw0 rw1 rw2 a0 a1 a2 b0 b1 b2 i0 i1 i2 i3 m0 m1 m2 m3 st
  | .swapExact3 rw0 rw1 rw2 a0 a1 a2 b0 b1 b2 c0 c1 c2 i0 i1 i2 i3 m0 m1 m2 m3 =>
      emitSwapExact3 context rw0 rw1 rw2 a0 a1 a2 b0 b1 b2 c0 c1 c2 i0 i1 i2 i3 m0 m1 m2 m3 st
  | .permit o0 o1 o2 s0 s1 s2 v0 v1 v2 v3 d0 d1 d2 d3 vv r0 r1 r2 r3 z0 z1 z2 z3 =>
      emitPermit context o0 o1 o2 s0 s1 s2 v0 v1 v2 v3 d0 d1 d2 d3 vv r0 r1 r2 r3 z0 z1 z2 z3 st
  | .tokenPermit t0 t1 t2 o0 o1 o2 s0 s1 s2 v0 v1 v2 v3 d0 d1 d2 d3 vv r0 r1 r2 r3 z0 z1 z2 z3 =>
      emitTokenPermit context t0 t1 t2 o0 o1 o2 s0 s1 s2 v0 v1 v2 v3 d0 d1 d2 d3 vv r0 r1 r2 r3 z0 z1 z2 z3 st

end ProofForge.Evm.ClosedCall.Emit
