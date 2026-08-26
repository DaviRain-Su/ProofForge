namespace ProofForge.Evm.Component

/-- Transitive storage/log/call effects for a bounded EVM component. Empty until a backend
registers a vocabulary. -/
structure EffectSummary where
  readsStorage : Bool := false
  writesStorage : Bool := false
  logs : Bool := false
  externalCall : Bool := false
  deriving BEq, Repr, Inhabited

/-- Stable value-producing bridge. Generic EVM Ops, IR, CFG, and the main emitter traverse this
wrapper once; component-specific query vocabularies remain in their owning modules.

`empty` is a reserved zero-arity placeholder so the sum is inhabited before the first real
backend lands. Source programs must not emit it. -/
inductive Query where
  | empty
  deriving BEq, Repr, Inhabited

def Query.arity : Query → Nat
  | .empty => 0

def Query.effects : Query → EffectSummary
  | .empty => {}

def Query.wellFormed : Query → Bool
  | .empty => false

def Query.canonical (_renderValue : V → String) (operands : Array V) : Query → String
  | .empty =>
      if operands.isEmpty then "evm.comp.empty"
      else s!"invalid-evm.comp.empty-{operands.size}"

/-- Stable effect bridge. New hashed-map, LOG, or closed-CALL backends extend this layer instead
of adding top-level EVM Ops/IR/main-emitter cases.

`empty` is reserved and not well-formed. -/
inductive Call (V : Type) where
  | empty
  deriving BEq, Repr, Inhabited

def Call.mapValues (_mapValue : α → β) : Call α → Call β
  | .empty => .empty

def Call.mapValuesM [Monad m] (_mapValue : α → m β) : Call α → m (Call β)
  | .empty => pure .empty

def Call.values : Call V → Array V
  | .empty => #[]

def Call.anyValue (predicate : V → Bool) (call : Call V) : Bool :=
  call.values.any predicate

def Call.allValues (predicate : V → Bool) (call : Call V) : Bool :=
  call.values.all predicate

def Call.effects : Call V → EffectSummary
  | .empty => {}

def Call.wellFormed (_valueWellFormed : V → Bool) : Call V → Bool
  | .empty => false

def Call.canonical (_renderValue : V → String) : Call V → String
  | .empty => "evm.comp.empty"

end ProofForge.Evm.Component
