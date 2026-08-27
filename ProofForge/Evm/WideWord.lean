namespace ProofForge.Evm.WideWord

/-- Packed 256-bit compare / checked arith. These are value queries: they do not
touch storage, logs, or CALL. Dynamic operands stay in `Val.ext`. -/
inductive Query where
  /-- `a ≥ b` on packed 256-bit words. Eight operands: a0..a3, b0..b3. -/
  | ge256
  /-- Packed address equality. Six operands: a0..a2, b0..b2. -/
  | eq20
  /-- Checked 256-bit `add`/`sub`/`mul`; `limb` is 0..3 (w0 lowest).
  `op` is 0 add, 1 sub, 2 mul. Eight operands: a0..a3, b0..b3. -/
  | arith256 (op : Nat) (limb : Nat)
  deriving BEq, Repr, Inhabited

def Query.arity : Query → Nat
  | .ge256 | .arith256 _ _ => 8
  | .eq20 => 6

def Query.wellFormed : Query → Bool
  | .ge256 | .eq20 => true
  | .arith256 op limb => op ≤ 2 && limb ≤ 3

private def renderOperands (renderValue : V → String) (operands : Array V) : String :=
  String.intercalate "," (operands.map renderValue).toList

/-- Preserve the closed-union digest spelling (`ext.{repr kind}(...)`). -/
def Query.canonical (renderValue : V → String) (operands : Array V) : Query → String
  | .ge256 =>
      s!"ext.ProofForge.Evm.Ops.ValKind.ge256({renderOperands renderValue operands})"
  | .eq20 =>
      s!"ext.ProofForge.Evm.Ops.ValKind.eq20({renderOperands renderValue operands})"
  | .arith256 op limb =>
      s!"ext.ProofForge.Evm.Ops.ValKind.arith256 {op} {limb}" ++
        s!"({renderOperands renderValue operands})"

end ProofForge.Evm.WideWord
