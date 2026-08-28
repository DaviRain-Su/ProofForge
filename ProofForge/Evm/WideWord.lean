namespace ProofForge.Evm.WideWord

/-- Typed unsigned packed-word relation. The legacy `ge256` query remains for artifact stability;
new source APIs use this enum instead of numeric operation tags. -/
inductive Comparison where
  | eq
  | lt
  | le
  | gt
  | ge
  deriving BEq, Repr, Inhabited

inductive Bitwise where
  | and
  | or
  | xor
  deriving BEq, Repr, Inhabited

inductive Shift where
  | left
  | right
  deriving BEq, Repr, Inhabited

/-- Packed 256-bit compare, checked arithmetic, bitwise operations, and logical shifts.
These are value queries: they do not touch storage, logs, or CALL. Dynamic operands stay in
`Val.ext`. -/
inductive Query where
  /-- `a ≥ b` on packed 256-bit words. Eight operands: a0..a3, b0..b3. -/
  | ge256
  /-- Typed unsigned comparison on packed 256-bit words. Eight operands: a0..a3, b0..b3. -/
  | compare256 (comparison : Comparison)
  /-- Packed address equality. Six operands: a0..a2, b0..b2. -/
  | eq20
  /-- Packed binary bitwise operation; `limb` is 0..3. Eight operands. -/
  | bitwise256 (operation : Bitwise) (limb : Nat)
  /-- Packed bitwise complement; `limb` is 0..3. Four operands. -/
  | not256 (limb : Nat)
  /-- Packed logical shift by one UInt64 amount; `limb` is 0..3. Five operands. -/
  | shift256 (direction : Shift) (limb : Nat)
  /-- Checked 256-bit `add`/`sub`/`mul`; `limb` is 0..3 (w0 lowest).
  `op` is 0 add, 1 sub, 2 mul. Eight operands: a0..a3, b0..b3. -/
  | arith256 (op : Nat) (limb : Nat)
  deriving BEq, Repr, Inhabited

def Query.arity : Query → Nat
  | .ge256 | .compare256 _ | .bitwise256 _ _ | .arith256 _ _ => 8
  | .not256 _ => 4
  | .shift256 _ _ => 5
  | .eq20 => 6

def Query.wellFormed : Query → Bool
  | .ge256 | .compare256 _ | .eq20 => true
  | .bitwise256 _ limb | .not256 limb | .shift256 _ limb => limb ≤ 3
  | .arith256 op limb => op ≤ 2 && limb ≤ 3

private def renderOperands (renderValue : V → String) (operands : Array V) : String :=
  String.intercalate "," (operands.map renderValue).toList

/-- Preserve the closed-union digest spelling (`ext.{repr kind}(...)`). -/
def Query.canonical (renderValue : V → String) (operands : Array V) : Query → String
  | .ge256 =>
      s!"ext.ProofForge.Evm.Ops.ValKind.ge256({renderOperands renderValue operands})"
  | .compare256 comparison =>
      s!"ext.ProofForge.Evm.Ops.ValKind.compare256.{repr comparison}" ++
        s!"({renderOperands renderValue operands})"
  | .eq20 =>
      s!"ext.ProofForge.Evm.Ops.ValKind.eq20({renderOperands renderValue operands})"
  | .bitwise256 operation limb =>
      s!"ext.ProofForge.Evm.Ops.ValKind.bitwise256.{repr operation} {limb}" ++
        s!"({renderOperands renderValue operands})"
  | .not256 limb =>
      s!"ext.ProofForge.Evm.Ops.ValKind.not256 {limb}" ++
        s!"({renderOperands renderValue operands})"
  | .shift256 direction limb =>
      s!"ext.ProofForge.Evm.Ops.ValKind.shift256.{repr direction} {limb}" ++
        s!"({renderOperands renderValue operands})"
  | .arith256 op limb =>
      s!"ext.ProofForge.Evm.Ops.ValKind.arith256 {op} {limb}" ++
        s!"({renderOperands renderValue operands})"

end ProofForge.Evm.WideWord
