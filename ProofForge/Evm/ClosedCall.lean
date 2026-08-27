namespace ProofForge.Evm.ClosedCall

/-- Transitive effects for one closed CALL query or call. -/
structure EffectSummary where
  readsStorage : Bool := false
  writesStorage : Bool := false
  logs : Bool := false
  externalCall : Bool := false
  deriving BEq, Repr, Inhabited

/-- Value-producing closed CALLs. Dynamic operands stay in `Val.ext`; `limb` selects
the packed 256-bit word. -/
inductive Query where
  | balance256 (limb : Nat)
  | allowance256 (limb : Nat)
  deriving BEq, Repr, Inhabited

def Query.arity : Query → Nat
  | .balance256 _ => 3
  | .allowance256 _ => 9

def Query.effects : Query → EffectSummary
  | .balance256 _ | .allowance256 _ => { externalCall := true }

def Query.wellFormed : Query → Bool
  | .balance256 limb | .allowance256 limb => limb ≤ 3

private def renderOperands (renderValue : V → String) (operands : Array V) : String :=
  String.intercalate "," (operands.map renderValue).toList

/-- Preserve the closed-union digest spelling (`ext.tokenBalance256` / `ext.tokenAllowance256`). -/
def Query.canonical (renderValue : V → String) (operands : Array V) : Query → String
  | .balance256 limb =>
      s!"ext.ProofForge.Evm.Ops.ValKind.tokenBalance256 {limb}" ++
        s!"({renderOperands renderValue operands})"
  | .allowance256 limb =>
      s!"ext.ProofForge.Evm.Ops.ValKind.tokenAllowance256 {limb}" ++
        s!"({renderOperands renderValue operands})"

/-- Closed ERC-20 / WETH / Uniswap / permit effects. -/
inductive Call (V : Type) where
  | transfer (tw0 tw1 tw2 dw0 dw1 dw2 amount : V)
  | transfer256 (tw0 tw1 tw2 dw0 dw1 dw2 a0 a1 a2 a3 : V)
  | approve256 (tw0 tw1 tw2 sw0 sw1 sw2 a0 a1 a2 a3 : V)
  | transferFrom256 (tw0 tw1 tw2 ow0 ow1 ow2 dw0 dw1 dw2 a0 a1 a2 a3 : V)
  | balanceOfSelf (tw0 tw1 tw2 : V)
  | wethDeposit256 (tw0 tw1 tw2 a0 a1 a2 a3 : V)
  | wethWithdraw256 (tw0 tw1 tw2 a0 a1 a2 a3 : V)
  | swapExact2 (rw0 rw1 rw2 a0 a1 a2 b0 b1 b2 i0 i1 i2 i3 m0 m1 m2 m3 : V)
  | swapExact3 (rw0 rw1 rw2 a0 a1 a2 b0 b1 b2 c0 c1 c2 i0 i1 i2 i3 m0 m1 m2 m3 : V)
  | permit (o0 o1 o2 s0 s1 s2 v0 v1 v2 v3 d0 d1 d2 d3 vv r0 r1 r2 r3 z0 z1 z2 z3 : V)
  | tokenPermit (t0 t1 t2 o0 o1 o2 s0 s1 s2 v0 v1 v2 v3 d0 d1 d2 d3 vv r0 r1 r2 r3 z0 z1 z2 z3 : V)
  deriving BEq, Repr, Inhabited

def Call.mapValues (mapValue : α → β) : Call α → Call β
  | .transfer tw0 tw1 tw2 dw0 dw1 dw2 amount =>
      .transfer (mapValue tw0) (mapValue tw1) (mapValue tw2)
        (mapValue dw0) (mapValue dw1) (mapValue dw2) (mapValue amount)
  | .transfer256 tw0 tw1 tw2 dw0 dw1 dw2 a0 a1 a2 a3 =>
      .transfer256 (mapValue tw0) (mapValue tw1) (mapValue tw2)
        (mapValue dw0) (mapValue dw1) (mapValue dw2)
        (mapValue a0) (mapValue a1) (mapValue a2) (mapValue a3)
  | .approve256 tw0 tw1 tw2 sw0 sw1 sw2 a0 a1 a2 a3 =>
      .approve256 (mapValue tw0) (mapValue tw1) (mapValue tw2)
        (mapValue sw0) (mapValue sw1) (mapValue sw2)
        (mapValue a0) (mapValue a1) (mapValue a2) (mapValue a3)
  | .transferFrom256 tw0 tw1 tw2 ow0 ow1 ow2 dw0 dw1 dw2 a0 a1 a2 a3 =>
      .transferFrom256 (mapValue tw0) (mapValue tw1) (mapValue tw2)
        (mapValue ow0) (mapValue ow1) (mapValue ow2)
        (mapValue dw0) (mapValue dw1) (mapValue dw2)
        (mapValue a0) (mapValue a1) (mapValue a2) (mapValue a3)
  | .balanceOfSelf tw0 tw1 tw2 =>
      .balanceOfSelf (mapValue tw0) (mapValue tw1) (mapValue tw2)
  | .wethDeposit256 tw0 tw1 tw2 a0 a1 a2 a3 =>
      .wethDeposit256 (mapValue tw0) (mapValue tw1) (mapValue tw2)
        (mapValue a0) (mapValue a1) (mapValue a2) (mapValue a3)
  | .wethWithdraw256 tw0 tw1 tw2 a0 a1 a2 a3 =>
      .wethWithdraw256 (mapValue tw0) (mapValue tw1) (mapValue tw2)
        (mapValue a0) (mapValue a1) (mapValue a2) (mapValue a3)
  | .swapExact2 rw0 rw1 rw2 a0 a1 a2 b0 b1 b2 i0 i1 i2 i3 m0 m1 m2 m3 =>
      .swapExact2 (mapValue rw0) (mapValue rw1) (mapValue rw2)
        (mapValue a0) (mapValue a1) (mapValue a2)
        (mapValue b0) (mapValue b1) (mapValue b2)
        (mapValue i0) (mapValue i1) (mapValue i2) (mapValue i3)
        (mapValue m0) (mapValue m1) (mapValue m2) (mapValue m3)
  | .swapExact3 rw0 rw1 rw2 a0 a1 a2 b0 b1 b2 c0 c1 c2 i0 i1 i2 i3 m0 m1 m2 m3 =>
      .swapExact3 (mapValue rw0) (mapValue rw1) (mapValue rw2)
        (mapValue a0) (mapValue a1) (mapValue a2)
        (mapValue b0) (mapValue b1) (mapValue b2)
        (mapValue c0) (mapValue c1) (mapValue c2)
        (mapValue i0) (mapValue i1) (mapValue i2) (mapValue i3)
        (mapValue m0) (mapValue m1) (mapValue m2) (mapValue m3)
  | .permit o0 o1 o2 s0 s1 s2 v0 v1 v2 v3 d0 d1 d2 d3 vv r0 r1 r2 r3 z0 z1 z2 z3 =>
      .permit (mapValue o0) (mapValue o1) (mapValue o2)
        (mapValue s0) (mapValue s1) (mapValue s2)
        (mapValue v0) (mapValue v1) (mapValue v2) (mapValue v3)
        (mapValue d0) (mapValue d1) (mapValue d2) (mapValue d3)
        (mapValue vv)
        (mapValue r0) (mapValue r1) (mapValue r2) (mapValue r3)
        (mapValue z0) (mapValue z1) (mapValue z2) (mapValue z3)
  | .tokenPermit t0 t1 t2 o0 o1 o2 s0 s1 s2 v0 v1 v2 v3 d0 d1 d2 d3 vv r0 r1 r2 r3 z0 z1 z2 z3 =>
      .tokenPermit (mapValue t0) (mapValue t1) (mapValue t2)
        (mapValue o0) (mapValue o1) (mapValue o2)
        (mapValue s0) (mapValue s1) (mapValue s2)
        (mapValue v0) (mapValue v1) (mapValue v2) (mapValue v3)
        (mapValue d0) (mapValue d1) (mapValue d2) (mapValue d3)
        (mapValue vv)
        (mapValue r0) (mapValue r1) (mapValue r2) (mapValue r3)
        (mapValue z0) (mapValue z1) (mapValue z2) (mapValue z3)

def Call.mapValuesM [Monad m] (mapValue : α → m β) : Call α → m (Call β)
  | .transfer tw0 tw1 tw2 dw0 dw1 dw2 amount =>
      return .transfer (← mapValue tw0) (← mapValue tw1) (← mapValue tw2)
        (← mapValue dw0) (← mapValue dw1) (← mapValue dw2) (← mapValue amount)
  | .transfer256 tw0 tw1 tw2 dw0 dw1 dw2 a0 a1 a2 a3 =>
      return .transfer256 (← mapValue tw0) (← mapValue tw1) (← mapValue tw2)
        (← mapValue dw0) (← mapValue dw1) (← mapValue dw2)
        (← mapValue a0) (← mapValue a1) (← mapValue a2) (← mapValue a3)
  | .approve256 tw0 tw1 tw2 sw0 sw1 sw2 a0 a1 a2 a3 =>
      return .approve256 (← mapValue tw0) (← mapValue tw1) (← mapValue tw2)
        (← mapValue sw0) (← mapValue sw1) (← mapValue sw2)
        (← mapValue a0) (← mapValue a1) (← mapValue a2) (← mapValue a3)
  | .transferFrom256 tw0 tw1 tw2 ow0 ow1 ow2 dw0 dw1 dw2 a0 a1 a2 a3 =>
      return .transferFrom256 (← mapValue tw0) (← mapValue tw1) (← mapValue tw2)
        (← mapValue ow0) (← mapValue ow1) (← mapValue ow2)
        (← mapValue dw0) (← mapValue dw1) (← mapValue dw2)
        (← mapValue a0) (← mapValue a1) (← mapValue a2) (← mapValue a3)
  | .balanceOfSelf tw0 tw1 tw2 =>
      return .balanceOfSelf (← mapValue tw0) (← mapValue tw1) (← mapValue tw2)
  | .wethDeposit256 tw0 tw1 tw2 a0 a1 a2 a3 =>
      return .wethDeposit256 (← mapValue tw0) (← mapValue tw1) (← mapValue tw2)
        (← mapValue a0) (← mapValue a1) (← mapValue a2) (← mapValue a3)
  | .wethWithdraw256 tw0 tw1 tw2 a0 a1 a2 a3 =>
      return .wethWithdraw256 (← mapValue tw0) (← mapValue tw1) (← mapValue tw2)
        (← mapValue a0) (← mapValue a1) (← mapValue a2) (← mapValue a3)
  | .swapExact2 rw0 rw1 rw2 a0 a1 a2 b0 b1 b2 i0 i1 i2 i3 m0 m1 m2 m3 =>
      return .swapExact2 (← mapValue rw0) (← mapValue rw1) (← mapValue rw2)
        (← mapValue a0) (← mapValue a1) (← mapValue a2)
        (← mapValue b0) (← mapValue b1) (← mapValue b2)
        (← mapValue i0) (← mapValue i1) (← mapValue i2) (← mapValue i3)
        (← mapValue m0) (← mapValue m1) (← mapValue m2) (← mapValue m3)
  | .swapExact3 rw0 rw1 rw2 a0 a1 a2 b0 b1 b2 c0 c1 c2 i0 i1 i2 i3 m0 m1 m2 m3 =>
      return .swapExact3 (← mapValue rw0) (← mapValue rw1) (← mapValue rw2)
        (← mapValue a0) (← mapValue a1) (← mapValue a2)
        (← mapValue b0) (← mapValue b1) (← mapValue b2)
        (← mapValue c0) (← mapValue c1) (← mapValue c2)
        (← mapValue i0) (← mapValue i1) (← mapValue i2) (← mapValue i3)
        (← mapValue m0) (← mapValue m1) (← mapValue m2) (← mapValue m3)
  | .permit o0 o1 o2 s0 s1 s2 v0 v1 v2 v3 d0 d1 d2 d3 vv r0 r1 r2 r3 z0 z1 z2 z3 =>
      return .permit (← mapValue o0) (← mapValue o1) (← mapValue o2)
        (← mapValue s0) (← mapValue s1) (← mapValue s2)
        (← mapValue v0) (← mapValue v1) (← mapValue v2) (← mapValue v3)
        (← mapValue d0) (← mapValue d1) (← mapValue d2) (← mapValue d3)
        (← mapValue vv)
        (← mapValue r0) (← mapValue r1) (← mapValue r2) (← mapValue r3)
        (← mapValue z0) (← mapValue z1) (← mapValue z2) (← mapValue z3)
  | .tokenPermit t0 t1 t2 o0 o1 o2 s0 s1 s2 v0 v1 v2 v3 d0 d1 d2 d3 vv r0 r1 r2 r3 z0 z1 z2 z3 =>
      return .tokenPermit (← mapValue t0) (← mapValue t1) (← mapValue t2)
        (← mapValue o0) (← mapValue o1) (← mapValue o2)
        (← mapValue s0) (← mapValue s1) (← mapValue s2)
        (← mapValue v0) (← mapValue v1) (← mapValue v2) (← mapValue v3)
        (← mapValue d0) (← mapValue d1) (← mapValue d2) (← mapValue d3)
        (← mapValue vv)
        (← mapValue r0) (← mapValue r1) (← mapValue r2) (← mapValue r3)
        (← mapValue z0) (← mapValue z1) (← mapValue z2) (← mapValue z3)

def Call.values : Call V → Array V
  | .transfer tw0 tw1 tw2 dw0 dw1 dw2 amount =>
      #[tw0, tw1, tw2, dw0, dw1, dw2, amount]
  | .transfer256 tw0 tw1 tw2 dw0 dw1 dw2 a0 a1 a2 a3 =>
      #[tw0, tw1, tw2, dw0, dw1, dw2, a0, a1, a2, a3]
  | .approve256 tw0 tw1 tw2 sw0 sw1 sw2 a0 a1 a2 a3 =>
      #[tw0, tw1, tw2, sw0, sw1, sw2, a0, a1, a2, a3]
  | .transferFrom256 tw0 tw1 tw2 ow0 ow1 ow2 dw0 dw1 dw2 a0 a1 a2 a3 =>
      #[tw0, tw1, tw2, ow0, ow1, ow2, dw0, dw1, dw2, a0, a1, a2, a3]
  | .balanceOfSelf tw0 tw1 tw2 => #[tw0, tw1, tw2]
  | .wethDeposit256 tw0 tw1 tw2 a0 a1 a2 a3 => #[tw0, tw1, tw2, a0, a1, a2, a3]
  | .wethWithdraw256 tw0 tw1 tw2 a0 a1 a2 a3 => #[tw0, tw1, tw2, a0, a1, a2, a3]
  | .swapExact2 rw0 rw1 rw2 a0 a1 a2 b0 b1 b2 i0 i1 i2 i3 m0 m1 m2 m3 =>
      #[rw0, rw1, rw2, a0, a1, a2, b0, b1, b2, i0, i1, i2, i3, m0, m1, m2, m3]
  | .swapExact3 rw0 rw1 rw2 a0 a1 a2 b0 b1 b2 c0 c1 c2 i0 i1 i2 i3 m0 m1 m2 m3 =>
      #[rw0, rw1, rw2, a0, a1, a2, b0, b1, b2, c0, c1, c2, i0, i1, i2, i3, m0, m1, m2, m3]
  | .permit o0 o1 o2 s0 s1 s2 v0 v1 v2 v3 d0 d1 d2 d3 vv r0 r1 r2 r3 z0 z1 z2 z3 =>
      #[o0, o1, o2, s0, s1, s2, v0, v1, v2, v3, d0, d1, d2, d3, vv, r0, r1, r2, r3, z0, z1, z2, z3]
  | .tokenPermit t0 t1 t2 o0 o1 o2 s0 s1 s2 v0 v1 v2 v3 d0 d1 d2 d3 vv r0 r1 r2 r3 z0 z1 z2 z3 =>
      #[t0, t1, t2, o0, o1, o2, s0, s1, s2, v0, v1, v2, v3, d0, d1, d2, d3, vv, r0, r1, r2, r3, z0, z1, z2, z3]

def Call.anyValue (predicate : V → Bool) (call : Call V) : Bool :=
  call.values.any predicate

def Call.allValues (predicate : V → Bool) (call : Call V) : Bool :=
  call.values.all predicate

def Call.effects : Call V → EffectSummary
  | .permit .. =>
      { readsStorage := true, writesStorage := true, logs := true, externalCall := true }
  | _ => { externalCall := true }

def Call.wellFormed (valueWellFormed : V → Bool) (call : Call V) : Bool :=
  call.allValues valueWellFormed

def Call.emitsExpired : Call V → Bool
  | .permit .. => true
  | _ => false

def Call.emitsUnauthorized : Call V → Bool
  | .permit .. => true
  | _ => false

/-- Preserve the closed-union digest spelling (`ttxfer` / `wethdep` / `permit`). -/
def Call.canonical (renderValue : V → String) : Call V → String
  | .transfer a b c d e f g =>
      s!"ttxfer({renderValue a},{renderValue b},{renderValue c},{renderValue d},{renderValue e},{renderValue f},{renderValue g})"
  | .transfer256 a b c d e f g0 g1 g2 g3 =>
      s!"ttxfer256({renderValue a},{renderValue b},{renderValue c},{renderValue d},{renderValue e},{renderValue f},{renderValue g0},{renderValue g1},{renderValue g2},{renderValue g3})"
  | .approve256 a b c d e f g0 g1 g2 g3 =>
      s!"tapprove256({renderValue a},{renderValue b},{renderValue c},{renderValue d},{renderValue e},{renderValue f},{renderValue g0},{renderValue g1},{renderValue g2},{renderValue g3})"
  | .transferFrom256 a b c d e f g h i j k l m =>
      s!"ttxferfrom256({renderValue a},{renderValue b},{renderValue c},{renderValue d},{renderValue e},{renderValue f},{renderValue g},{renderValue h},{renderValue i},{renderValue j},{renderValue k},{renderValue l},{renderValue m})"
  | .balanceOfSelf a b c =>
      s!"tbal({renderValue a},{renderValue b},{renderValue c})"
  | .wethDeposit256 a b c d0 d1 d2 d3 =>
      s!"wethdep({renderValue a},{renderValue b},{renderValue c},{renderValue d0},{renderValue d1},{renderValue d2},{renderValue d3})"
  | .wethWithdraw256 a b c d0 d1 d2 d3 =>
      s!"wethwd({renderValue a},{renderValue b},{renderValue c},{renderValue d0},{renderValue d1},{renderValue d2},{renderValue d3})"
  | .swapExact2 r0 r1 r2 a0 a1 a2 b0 b1 b2 i0 i1 i2 i3 m0 m1 m2 m3 =>
      s!"swap2({renderValue r0},{renderValue r1},{renderValue r2},{renderValue a0},{renderValue a1},{renderValue a2},{renderValue b0},{renderValue b1},{renderValue b2},{renderValue i0},{renderValue i1},{renderValue i2},{renderValue i3},{renderValue m0},{renderValue m1},{renderValue m2},{renderValue m3})"
  | .swapExact3 r0 r1 r2 a0 a1 a2 b0 b1 b2 c0 c1 c2 i0 i1 i2 i3 m0 m1 m2 m3 =>
      s!"swap3({renderValue r0},{renderValue r1},{renderValue r2},{renderValue a0},{renderValue a1},{renderValue a2},{renderValue b0},{renderValue b1},{renderValue b2},{renderValue c0},{renderValue c1},{renderValue c2},{renderValue i0},{renderValue i1},{renderValue i2},{renderValue i3},{renderValue m0},{renderValue m1},{renderValue m2},{renderValue m3})"
  | .permit o0 o1 o2 s0 s1 s2 v0 v1 v2 v3 d0 d1 d2 d3 vv r0 r1 r2 r3 z0 z1 z2 z3 =>
      s!"permit({renderValue o0},{renderValue o1},{renderValue o2},{renderValue s0},{renderValue s1},{renderValue s2},{renderValue v0},{renderValue v1},{renderValue v2},{renderValue v3},{renderValue d0},{renderValue d1},{renderValue d2},{renderValue d3},{renderValue vv},{renderValue r0},{renderValue r1},{renderValue r2},{renderValue r3},{renderValue z0},{renderValue z1},{renderValue z2},{renderValue z3})"
  | .tokenPermit t0 t1 t2 o0 o1 o2 s0 s1 s2 v0 v1 v2 v3 d0 d1 d2 d3 vv r0 r1 r2 r3 z0 z1 z2 z3 =>
      s!"tpermit({renderValue t0},{renderValue t1},{renderValue t2},{renderValue o0},{renderValue o1},{renderValue o2},{renderValue s0},{renderValue s1},{renderValue s2},{renderValue v0},{renderValue v1},{renderValue v2},{renderValue v3},{renderValue d0},{renderValue d1},{renderValue d2},{renderValue d3},{renderValue vv},{renderValue r0},{renderValue r1},{renderValue r2},{renderValue r3},{renderValue z0},{renderValue z1},{renderValue z2},{renderValue z3})"

end ProofForge.Evm.ClosedCall
