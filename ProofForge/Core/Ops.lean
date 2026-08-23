namespace ProofForge.Core.Ops

/-- Target-independent comparison used by source values and control flow. -/
inductive Cmp where
  | eq | ne | lt | le | gt | ge
  deriving BEq, Repr, Inhabited, DecidableEq

/--
Target-independent recursive values. A target owns `Ext`; Core only carries the extension kind
and its recursively typed operands.
-/
inductive Val (Ext : Type) where
  | arg (i : Nat)
  | local (i : Nat)
  | field (base : Val Ext) (name : String)
  | lit (n : UInt64)
  | bitAnd (lhs rhs : Val Ext)
  | bitOr (lhs rhs : Val Ext)
  | bitXor (lhs rhs : Val Ext)
  | bitNot (value : Val Ext)
  | shiftL (lhs rhs : Val Ext)
  | shiftR (lhs rhs : Val Ext)
  | indexGet (base : Val Ext) (name : String) (idx : Val Ext) (len : Nat)
      (elemOff : Nat := 0)
  | loopIx
  | select (cmp : Cmp) (lhs rhs thn els : Val Ext)
  | addU64 (lhs rhs : Val Ext)
  | subU64 (lhs rhs : Val Ext)
  | mulU64 (lhs rhs : Val Ext)
  | divU64 (lhs rhs : Val Ext)
  | modU64 (lhs rhs : Val Ext)
  | ext (kind : Ext) (operands : Array (Val Ext))
  deriving Repr

/--
Target-independent effects and control flow. `OpExt V` is target-owned and may carry typed
metadata plus source values, but cannot recursively contain `Op`.
-/
inductive Op (ValExt : Type) (OpExt : Type → Type) where
  | letLocal (i : Nat) (value : Val ValExt)
  | joinLocal (i : Nat)
  | setLocal (i : Nat) (value : Val ValExt)
  | checkedAddU64 (lhs rhs : Val ValExt)
  | checkedSubU64 (lhs rhs : Val ValExt)
  | checkedMulU64 (lhs rhs : Val ValExt)
  | checkedDivU64 (lhs rhs : Val ValExt)
  | checkedModU64 (lhs rhs : Val ValExt)
  | ite (cmp : Cmp) (lhs rhs : Val ValExt)
      (thn els : Array (Op ValExt OpExt))
  | forAccum (n : Nat) (addend : Val ValExt)
  | forBody (n : Nat) (body : Array (Op ValExt OpExt))
  | indexSet (name : String) (idx value : Val ValExt) (len : Nat)
      (elemOff : Nat := 0)
  | storeField (name : String) (value : Val ValExt)
  | okState (value : Val ValExt)
  | errorOverflow
  | errorNamed (name : String)
  | returnU64 (value : Val ValExt)
  | returnState (value : Val ValExt)
  | ext (payload : OpExt (Val ValExt))

/-- Check extension arity and all recursively contained common values. -/
partial def Val.wellFormed (arity : Ext → Nat) : Val Ext → Bool
  | .arg _ | .local _ | .lit _ | .loopIx => true
  | .field base _ | .bitNot base => base.wellFormed arity
  | .bitAnd lhs rhs | .bitOr lhs rhs | .bitXor lhs rhs
  | .shiftL lhs rhs | .shiftR lhs rhs
  | .addU64 lhs rhs | .subU64 lhs rhs | .mulU64 lhs rhs
  | .divU64 lhs rhs | .modU64 lhs rhs =>
      lhs.wellFormed arity && rhs.wellFormed arity
  | .indexGet base _ idx _ _ => base.wellFormed arity && idx.wellFormed arity
  | .select _ lhs rhs thn els =>
      lhs.wellFormed arity && rhs.wellFormed arity &&
        thn.wellFormed arity && els.wellFormed arity
  | .ext kind operands =>
      operands.size == arity kind && operands.all (wellFormed arity)

/-- Walk common control flow while allowing the caller to inspect target extension payloads. -/
partial def Op.wellFormed (arity : ValExt → Nat)
    (validExt : OpExt (Val ValExt) → Bool) : Op ValExt OpExt → Bool
  | .letLocal _ value | .setLocal _ value | .forAccum _ value
  | .storeField _ value | .okState value | .returnU64 value | .returnState value =>
      value.wellFormed arity
  | .joinLocal _ | .errorOverflow | .errorNamed _ => true
  | .checkedAddU64 lhs rhs | .checkedSubU64 lhs rhs | .checkedMulU64 lhs rhs
  | .checkedDivU64 lhs rhs | .checkedModU64 lhs rhs =>
      lhs.wellFormed arity && rhs.wellFormed arity
  | .ite _ lhs rhs thn els =>
      lhs.wellFormed arity && rhs.wellFormed arity &&
        thn.all (wellFormed arity validExt) && els.all (wellFormed arity validExt)
  | .forBody _ body => body.all (wellFormed arity validExt)
  | .indexSet _ idx value _ _ => idx.wellFormed arity && value.wellFormed arity
  | .ext payload => validExt payload

end ProofForge.Core.Ops
