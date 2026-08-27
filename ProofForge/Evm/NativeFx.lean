namespace ProofForge.Evm.NativeFx

/-- Transitive effects for one native ETH / LOG / revert / receive call. -/
structure EffectSummary where
  logs : Bool := false
  externalCall : Bool := false
  payable : Bool := false
  receive : Bool := false
  deriving BEq, Repr, Inhabited

/-- Native ETH, LOG, revert, and receive effects. Dynamic operands stay in the Call. -/
inductive Call (V : Type) where
  | deposit (amount : V)
  | deposit256 (a0 a1 a2 a3 : V)
  | sendEth (w0 w1 w2 amount : V)
  | sendEth256 (w0 w1 w2 a0 a1 a2 a3 : V)
  | log (name : String) (amount : V)
  | logTransfer256 (f0 f1 f2 t0 t1 t2 a0 a1 a2 a3 : V)
  | logApproval256 (o0 o1 o2 s0 s1 s2 a0 a1 a2 a3 : V)
  | revertInsufficient (h0 h1 h2 h3 w0 w1 w2 w3 : V)
  | revertUnauthorized (w0 w1 w2 : V)
  | revertZeroAddress
  | revertPaused
  | receive
  deriving BEq, Repr, Inhabited

def Call.mapValues (mapValue : α → β) : Call α → Call β
  | .deposit amount => .deposit (mapValue amount)
  | .deposit256 a0 a1 a2 a3 =>
      .deposit256 (mapValue a0) (mapValue a1) (mapValue a2) (mapValue a3)
  | .sendEth w0 w1 w2 amount =>
      .sendEth (mapValue w0) (mapValue w1) (mapValue w2) (mapValue amount)
  | .sendEth256 w0 w1 w2 a0 a1 a2 a3 =>
      .sendEth256 (mapValue w0) (mapValue w1) (mapValue w2)
        (mapValue a0) (mapValue a1) (mapValue a2) (mapValue a3)
  | .log name amount => .log name (mapValue amount)
  | .logTransfer256 f0 f1 f2 t0 t1 t2 a0 a1 a2 a3 =>
      .logTransfer256 (mapValue f0) (mapValue f1) (mapValue f2)
        (mapValue t0) (mapValue t1) (mapValue t2)
        (mapValue a0) (mapValue a1) (mapValue a2) (mapValue a3)
  | .logApproval256 o0 o1 o2 s0 s1 s2 a0 a1 a2 a3 =>
      .logApproval256 (mapValue o0) (mapValue o1) (mapValue o2)
        (mapValue s0) (mapValue s1) (mapValue s2)
        (mapValue a0) (mapValue a1) (mapValue a2) (mapValue a3)
  | .revertInsufficient h0 h1 h2 h3 w0 w1 w2 w3 =>
      .revertInsufficient (mapValue h0) (mapValue h1) (mapValue h2) (mapValue h3)
        (mapValue w0) (mapValue w1) (mapValue w2) (mapValue w3)
  | .revertUnauthorized w0 w1 w2 =>
      .revertUnauthorized (mapValue w0) (mapValue w1) (mapValue w2)
  | .revertZeroAddress => .revertZeroAddress
  | .revertPaused => .revertPaused
  | .receive => .receive

def Call.mapValuesM [Monad m] (mapValue : α → m β) : Call α → m (Call β)
  | .deposit amount => return .deposit (← mapValue amount)
  | .deposit256 a0 a1 a2 a3 =>
      return .deposit256 (← mapValue a0) (← mapValue a1) (← mapValue a2) (← mapValue a3)
  | .sendEth w0 w1 w2 amount =>
      return .sendEth (← mapValue w0) (← mapValue w1) (← mapValue w2) (← mapValue amount)
  | .sendEth256 w0 w1 w2 a0 a1 a2 a3 =>
      return .sendEth256 (← mapValue w0) (← mapValue w1) (← mapValue w2)
        (← mapValue a0) (← mapValue a1) (← mapValue a2) (← mapValue a3)
  | .log name amount => return .log name (← mapValue amount)
  | .logTransfer256 f0 f1 f2 t0 t1 t2 a0 a1 a2 a3 =>
      return .logTransfer256 (← mapValue f0) (← mapValue f1) (← mapValue f2)
        (← mapValue t0) (← mapValue t1) (← mapValue t2)
        (← mapValue a0) (← mapValue a1) (← mapValue a2) (← mapValue a3)
  | .logApproval256 o0 o1 o2 s0 s1 s2 a0 a1 a2 a3 =>
      return .logApproval256 (← mapValue o0) (← mapValue o1) (← mapValue o2)
        (← mapValue s0) (← mapValue s1) (← mapValue s2)
        (← mapValue a0) (← mapValue a1) (← mapValue a2) (← mapValue a3)
  | .revertInsufficient h0 h1 h2 h3 w0 w1 w2 w3 =>
      return .revertInsufficient (← mapValue h0) (← mapValue h1) (← mapValue h2)
        (← mapValue h3) (← mapValue w0) (← mapValue w1) (← mapValue w2) (← mapValue w3)
  | .revertUnauthorized w0 w1 w2 =>
      return .revertUnauthorized (← mapValue w0) (← mapValue w1) (← mapValue w2)
  | .revertZeroAddress => pure .revertZeroAddress
  | .revertPaused => pure .revertPaused
  | .receive => pure .receive

def Call.values : Call V → Array V
  | .deposit amount | .log _ amount => #[amount]
  | .deposit256 a0 a1 a2 a3 => #[a0, a1, a2, a3]
  | .sendEth w0 w1 w2 amount => #[w0, w1, w2, amount]
  | .sendEth256 w0 w1 w2 a0 a1 a2 a3 => #[w0, w1, w2, a0, a1, a2, a3]
  | .logTransfer256 f0 f1 f2 t0 t1 t2 a0 a1 a2 a3 =>
      #[f0, f1, f2, t0, t1, t2, a0, a1, a2, a3]
  | .logApproval256 o0 o1 o2 s0 s1 s2 a0 a1 a2 a3 =>
      #[o0, o1, o2, s0, s1, s2, a0, a1, a2, a3]
  | .revertInsufficient h0 h1 h2 h3 w0 w1 w2 w3 =>
      #[h0, h1, h2, h3, w0, w1, w2, w3]
  | .revertUnauthorized w0 w1 w2 => #[w0, w1, w2]
  | .revertZeroAddress | .revertPaused | .receive => #[]

def Call.anyValue (predicate : V → Bool) (call : Call V) : Bool :=
  call.values.any predicate

def Call.allValues (predicate : V → Bool) (call : Call V) : Bool :=
  call.values.all predicate

def Call.effects : Call V → EffectSummary
  | .deposit _ | .deposit256 .. => { payable := true }
  | .sendEth .. | .sendEth256 .. => { externalCall := true }
  | .log .. | .logTransfer256 .. | .logApproval256 .. => { logs := true }
  | .revertInsufficient .. | .revertUnauthorized .. | .revertZeroAddress | .revertPaused => {}
  | .receive => { payable := true, receive := true }

def Call.wellFormed (valueWellFormed : V → Bool) (call : Call V) : Bool :=
  call.allValues valueWellFormed

def Call.isDeposit : Call V → Bool
  | .deposit _ | .deposit256 .. => true
  | _ => false

def Call.isReceive : Call V → Bool
  | .receive => true
  | _ => false

def Call.emitsInsufficient : Call V → Bool
  | .revertInsufficient .. => true
  | _ => false

def Call.emitsUnauthorized : Call V → Bool
  | .revertUnauthorized .. => true
  | _ => false

def Call.emitsZeroAddress : Call V → Bool
  | .revertZeroAddress => true
  | _ => false

def Call.emitsPaused : Call V → Bool
  | .revertPaused => true
  | _ => false

def Call.logName : Call V → Option String
  | .log name _ => some name
  | .logTransfer256 .. => some "Transfer256"
  | .logApproval256 .. => some "Approval256"
  | _ => none

/-- Preserve the closed-union digest spelling (`edep` / `elog3.Transfer` / `err.ZeroAddress`). -/
def Call.canonical (renderValue : V → String) : Call V → String
  | .deposit v => s!"edep({renderValue v})"
  | .deposit256 a0 a1 a2 a3 =>
      s!"edep256({renderValue a0},{renderValue a1},{renderValue a2},{renderValue a3})"
  | .sendEth a b c d =>
      s!"esend({renderValue a},{renderValue b},{renderValue c},{renderValue d})"
  | .sendEth256 a b c d0 d1 d2 d3 =>
      s!"esend256({renderValue a},{renderValue b},{renderValue c},{renderValue d0},{renderValue d1},{renderValue d2},{renderValue d3})"
  | .log n v => s!"elog.{n}({renderValue v})"
  | .logTransfer256 f0 f1 f2 t0 t1 t2 a0 a1 a2 a3 =>
      s!"elog3.Transfer({renderValue f0},{renderValue f1},{renderValue f2},{renderValue t0},{renderValue t1},{renderValue t2},{renderValue a0},{renderValue a1},{renderValue a2},{renderValue a3})"
  | .logApproval256 o0 o1 o2 s0 s1 s2 a0 a1 a2 a3 =>
      s!"elog3.Approval({renderValue o0},{renderValue o1},{renderValue o2},{renderValue s0},{renderValue s1},{renderValue s2},{renderValue a0},{renderValue a1},{renderValue a2},{renderValue a3})"
  | .revertInsufficient h0 h1 h2 h3 w0 w1 w2 w3 =>
      s!"err.Insufficient({renderValue h0},{renderValue h1},{renderValue h2},{renderValue h3},{renderValue w0},{renderValue w1},{renderValue w2},{renderValue w3})"
  | .revertUnauthorized w0 w1 w2 =>
      s!"err.Unauthorized({renderValue w0},{renderValue w1},{renderValue w2})"
  | .revertZeroAddress => "err.ZeroAddress"
  | .revertPaused => "err.Paused"
  | .receive => "erecv"

end ProofForge.Evm.NativeFx
