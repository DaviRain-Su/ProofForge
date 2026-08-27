namespace ProofForge.Evm.HashedMap

/-- Transitive storage effects for one hashed-map query or call. -/
structure EffectSummary where
  readsStorage : Bool := false
  writesStorage : Bool := false
  deriving BEq, Repr, Inhabited

/-- Value-producing hashed-map reads. Dynamic operands stay in `Val.ext`; this descriptor
holds only the static shape and, for 256-bit payloads, the selected limb. -/
inductive Query where
  | getU64
  | getAddr
  | getPair
  | getAddr256 (limb : Nat)
  | getPair256 (limb : Nat)
  deriving BEq, Repr, Inhabited

def Query.arity : Query → Nat
  | .getU64 => 2
  | .getAddr | .getAddr256 _ => 4
  | .getPair | .getPair256 _ => 7

def Query.effects : Query → EffectSummary
  | .getU64 | .getAddr | .getPair | .getAddr256 _ | .getPair256 _ =>
      { readsStorage := true }

def Query.wellFormed : Query → Bool
  | .getU64 | .getAddr | .getPair => true
  | .getAddr256 limb | .getPair256 limb => limb ≤ 3

private def renderOperands (renderValue : V → String) (operands : Array V) : String :=
  String.intercalate "," (operands.map renderValue).toList

/-- Preserve the closed-union digest spelling (`vg` / `vga` / `vgp` / `ext.mapGet*256`). -/
def Query.canonical (renderValue : V → String) (operands : Array V) : Query → String
  | .getU64 =>
      if operands.size == 2 then s!"vg({renderOperands renderValue operands})"
      else s!"invalid-vg-{operands.size}"
  | .getAddr =>
      if operands.size == 4 then s!"vga({renderOperands renderValue operands})"
      else s!"invalid-vga-{operands.size}"
  | .getPair =>
      if operands.size == 7 then s!"vgp({renderOperands renderValue operands})"
      else s!"invalid-vgp-{operands.size}"
  | .getAddr256 limb =>
      s!"ext.ProofForge.Evm.Ops.ValKind.mapGetAddr256 {limb}" ++
        s!"({renderOperands renderValue operands})"
  | .getPair256 limb =>
      s!"ext.ProofForge.Evm.Ops.ValKind.mapGetPair256 {limb}" ++
        s!"({renderOperands renderValue operands})"

/-- Hashed-map effects. Reads that appear as statements share this vocabulary with writes
so the main emitter does not grow a parallel map family. -/
inductive Call (V : Type) where
  | getU64 (base key : V)
  | setU64 (base key value : V)
  | getAddr (base w0 w1 w2 : V)
  | setAddr (base w0 w1 w2 value : V)
  | getPair (base o0 o1 o2 s0 s1 s2 : V)
  | setPair (base o0 o1 o2 s0 s1 s2 value : V)
  | setAddr256 (base w0 w1 w2 v0 v1 v2 v3 : V)
  | setPair256 (base o0 o1 o2 s0 s1 s2 v0 v1 v2 v3 : V)
  deriving BEq, Repr, Inhabited

def Call.mapValues (mapValue : α → β) : Call α → Call β
  | .getU64 base key => .getU64 (mapValue base) (mapValue key)
  | .setU64 base key value => .setU64 (mapValue base) (mapValue key) (mapValue value)
  | .getAddr base w0 w1 w2 =>
      .getAddr (mapValue base) (mapValue w0) (mapValue w1) (mapValue w2)
  | .setAddr base w0 w1 w2 value =>
      .setAddr (mapValue base) (mapValue w0) (mapValue w1) (mapValue w2) (mapValue value)
  | .getPair base o0 o1 o2 s0 s1 s2 =>
      .getPair (mapValue base) (mapValue o0) (mapValue o1) (mapValue o2)
        (mapValue s0) (mapValue s1) (mapValue s2)
  | .setPair base o0 o1 o2 s0 s1 s2 value =>
      .setPair (mapValue base) (mapValue o0) (mapValue o1) (mapValue o2)
        (mapValue s0) (mapValue s1) (mapValue s2) (mapValue value)
  | .setAddr256 base w0 w1 w2 v0 v1 v2 v3 =>
      .setAddr256 (mapValue base) (mapValue w0) (mapValue w1) (mapValue w2)
        (mapValue v0) (mapValue v1) (mapValue v2) (mapValue v3)
  | .setPair256 base o0 o1 o2 s0 s1 s2 v0 v1 v2 v3 =>
      .setPair256 (mapValue base) (mapValue o0) (mapValue o1) (mapValue o2)
        (mapValue s0) (mapValue s1) (mapValue s2)
        (mapValue v0) (mapValue v1) (mapValue v2) (mapValue v3)

def Call.mapValuesM [Monad m] (mapValue : α → m β) : Call α → m (Call β)
  | .getU64 base key =>
      return .getU64 (← mapValue base) (← mapValue key)
  | .setU64 base key value =>
      return .setU64 (← mapValue base) (← mapValue key) (← mapValue value)
  | .getAddr base w0 w1 w2 =>
      return .getAddr (← mapValue base) (← mapValue w0) (← mapValue w1) (← mapValue w2)
  | .setAddr base w0 w1 w2 value =>
      return .setAddr (← mapValue base) (← mapValue w0) (← mapValue w1) (← mapValue w2)
        (← mapValue value)
  | .getPair base o0 o1 o2 s0 s1 s2 =>
      return .getPair (← mapValue base) (← mapValue o0) (← mapValue o1) (← mapValue o2)
        (← mapValue s0) (← mapValue s1) (← mapValue s2)
  | .setPair base o0 o1 o2 s0 s1 s2 value =>
      return .setPair (← mapValue base) (← mapValue o0) (← mapValue o1) (← mapValue o2)
        (← mapValue s0) (← mapValue s1) (← mapValue s2) (← mapValue value)
  | .setAddr256 base w0 w1 w2 v0 v1 v2 v3 =>
      return .setAddr256 (← mapValue base) (← mapValue w0) (← mapValue w1) (← mapValue w2)
        (← mapValue v0) (← mapValue v1) (← mapValue v2) (← mapValue v3)
  | .setPair256 base o0 o1 o2 s0 s1 s2 v0 v1 v2 v3 =>
      return .setPair256 (← mapValue base) (← mapValue o0) (← mapValue o1) (← mapValue o2)
        (← mapValue s0) (← mapValue s1) (← mapValue s2)
        (← mapValue v0) (← mapValue v1) (← mapValue v2) (← mapValue v3)

def Call.values : Call V → Array V
  | .getU64 base key => #[base, key]
  | .setU64 base key value => #[base, key, value]
  | .getAddr base w0 w1 w2 => #[base, w0, w1, w2]
  | .setAddr base w0 w1 w2 value => #[base, w0, w1, w2, value]
  | .getPair base o0 o1 o2 s0 s1 s2 => #[base, o0, o1, o2, s0, s1, s2]
  | .setPair base o0 o1 o2 s0 s1 s2 value => #[base, o0, o1, o2, s0, s1, s2, value]
  | .setAddr256 base w0 w1 w2 v0 v1 v2 v3 => #[base, w0, w1, w2, v0, v1, v2, v3]
  | .setPair256 base o0 o1 o2 s0 s1 s2 v0 v1 v2 v3 =>
      #[base, o0, o1, o2, s0, s1, s2, v0, v1, v2, v3]

def Call.anyValue (predicate : V → Bool) (call : Call V) : Bool :=
  call.values.any predicate

def Call.allValues (predicate : V → Bool) (call : Call V) : Bool :=
  call.values.all predicate

def Call.effects : Call V → EffectSummary
  | .getU64 .. | .getAddr .. | .getPair .. => { readsStorage := true }
  | .setU64 .. | .setAddr .. | .setPair .. | .setAddr256 .. | .setPair256 .. =>
      { readsStorage := true, writesStorage := true }

def Call.wellFormed (valueWellFormed : V → Bool) (call : Call V) : Bool :=
  call.allValues valueWellFormed

/-- Preserve the closed-union digest spelling (`mget` / `mset` / `mseta256`). -/
def Call.canonical (renderValue : V → String) : Call V → String
  | .getU64 base key => s!"mget({renderValue base},{renderValue key})"
  | .setU64 base key value =>
      s!"mset({renderValue base},{renderValue key},{renderValue value})"
  | .getAddr base w0 w1 w2 =>
      s!"mgeta({renderValue base},{renderValue w0},{renderValue w1},{renderValue w2})"
  | .setAddr base w0 w1 w2 value =>
      s!"mseta({renderValue base},{renderValue w0},{renderValue w1},{renderValue w2},{renderValue value})"
  | .getPair base o0 o1 o2 s0 s1 s2 =>
      s!"mgetp({renderValue base},{renderValue o0},{renderValue o1},{renderValue o2},{renderValue s0},{renderValue s1},{renderValue s2})"
  | .setPair base o0 o1 o2 s0 s1 s2 value =>
      s!"msetp({renderValue base},{renderValue o0},{renderValue o1},{renderValue o2},{renderValue s0},{renderValue s1},{renderValue s2},{renderValue value})"
  | .setAddr256 base w0 w1 w2 v0 v1 v2 v3 =>
      s!"mseta256({renderValue base},{renderValue w0},{renderValue w1},{renderValue w2},{renderValue v0},{renderValue v1},{renderValue v2},{renderValue v3})"
  | .setPair256 base o0 o1 o2 s0 s1 s2 v0 v1 v2 v3 =>
      s!"msetp256({renderValue base},{renderValue o0},{renderValue o1},{renderValue o2},{renderValue s0},{renderValue s1},{renderValue s2},{renderValue v0},{renderValue v1},{renderValue v2},{renderValue v3})"

end ProofForge.Evm.HashedMap
