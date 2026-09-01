import ProofForge.Core.Codec

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
  deriving BEq, Repr

instance : Inhabited (Val Ext) := ⟨.lit 0⟩

/-- One logical field of a source error constructor. Core owns declaration-order names, scalar
metadata, and source-limb values; targets own selectors, wire geometry, and error codes. -/
structure ErrorArg (V : Type) where
  name : String
  type : Core.Codec.Scalar
  parts : Array V
  deriving BEq, Repr, Inhabited

/-- Target-neutral fixed error frame preserved from a parameterized `Except.error` constructor. -/
structure ErrorFrame (V : Type) where
  constructor : String
  args : Array (ErrorArg V)
  deriving BEq, Repr, Inhabited

def ErrorArg.mapValues (mapValue : α → β) (arg : ErrorArg α) : ErrorArg β :=
  { arg with parts := arg.parts.map mapValue }

def ErrorFrame.mapValues (mapValue : α → β) (frame : ErrorFrame α) : ErrorFrame β :=
  { frame with args := frame.args.map (·.mapValues mapValue) }

def ErrorArg.mapValuesM [Monad m] (mapValue : α → m β) (arg : ErrorArg α) :
    m (ErrorArg β) := do
  return { arg with parts := ← arg.parts.mapM mapValue }

def ErrorFrame.mapValuesM [Monad m] (mapValue : α → m β) (frame : ErrorFrame α) :
    m (ErrorFrame β) := do
  return { frame with args := ← frame.args.mapM (·.mapValuesM mapValue) }

def ErrorFrame.values (frame : ErrorFrame V) : Array V :=
  frame.args.flatMap (·.parts)

/-- Generic frame invariant. The fixed source representation uses little UInt64 limbs; a target
may impose a smaller scalar vocabulary or total-word bound before emission. -/
def ErrorFrame.wellFormed (valueWellFormed : V → Bool) (frame : ErrorFrame V) : Bool :=
  let names := frame.args.toList.map (·.name)
  !frame.constructor.isEmpty && !frame.args.isEmpty &&
    names.length == names.eraseDups.length &&
    frame.args.all fun arg =>
      !arg.name.isEmpty && arg.type.isWellFormed &&
        arg.parts.size == (arg.type.byteWidth + 7) / 8 &&
        arg.parts.all valueWellFormed

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
  /-- Sum `addend` over `[0, n)`, exposing the final accumulator through `resultLocal`. -/
  | forAccum (n : Nat) (addend : Val ValExt) (resultLocal : Nat)
  | forBody (n : Nat) (body : Array (Op ValExt OpExt))
  /-- Dynamic write identified by its logical leaf name inside a vector element. The extractor
  resolves it against `Schema` before target lowering; an empty name denotes a scalar element. -/
  | indexSetLeaf (name : String) (idx value : Val ValExt) (len : Nat) (leaf : String := "")
  | indexSet (name : String) (idx value : Val ValExt) (len : Nat)
      (elemOff : Nat := 0)
  | storeField (name : String) (value : Val ValExt)
  | okState (value : Val ValExt)
  | errorOverflow
  | errorNamed (name : String)
  | errorTyped (frame : ErrorFrame (Val ValExt))
  | returnU64 (value : Val ValExt)
  | returnState (value : Val ValExt)
  | ext (payload : OpExt (Val ValExt))

instance : Inhabited (Op ValExt OpExt) := ⟨.errorOverflow⟩

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
  | .letLocal _ value | .setLocal _ value | .forAccum _ value _
  | .storeField _ value | .okState value | .returnU64 value | .returnState value =>
      value.wellFormed arity
  | .joinLocal _ | .errorOverflow | .errorNamed _ => true
  | .errorTyped frame => frame.wellFormed (·.wellFormed arity)
  | .checkedAddU64 lhs rhs | .checkedSubU64 lhs rhs | .checkedMulU64 lhs rhs
  | .checkedDivU64 lhs rhs | .checkedModU64 lhs rhs =>
      lhs.wellFormed arity && rhs.wellFormed arity
  | .ite _ lhs rhs thn els =>
      lhs.wellFormed arity && rhs.wellFormed arity &&
        thn.all (wellFormed arity validExt) && els.all (wellFormed arity validExt)
  | .forBody _ body => body.all (wellFormed arity validExt)
  | .indexSetLeaf _ idx value _ _ => idx.wellFormed arity && value.wellFormed arity
  | .indexSet _ idx value _ _ => idx.wellFormed arity && value.wellFormed arity
  | .ext payload => validExt payload

end ProofForge.Core.Ops
