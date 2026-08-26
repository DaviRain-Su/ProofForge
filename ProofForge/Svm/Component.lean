import ProofForge.Svm.AccountStorage

namespace ProofForge.Svm.Component

/-- Highest fixed stack offset owned by current bounded components. Scalar-local planning starts
after this component-wide boundary instead of knowing individual storage/queue/recorder layouts. -/
def stackScratchEnd : Nat := 408

/-- Transitive component effects use one target-owned account summary regardless of component. -/
abbrev EffectSummary := AccountStorage.EffectSummary

/-- Stable value-producing bridge for target-owned bounded components. Generic SVM Ops, IR, CFG,
and the main emitter traverse this wrapper once; component-specific query vocabularies remain in
their owning modules. -/
inductive Query where
  | accountStorage (query : AccountStorage.Query)
  deriving BEq, Repr, Inhabited

def Query.arity : Query → Nat
  | .accountStorage query => query.arity

def Query.effects : Query → EffectSummary
  | .accountStorage query => query.effects

def Query.wellFormed (accountLimit : Nat := 64) : Query → Bool
  | .accountStorage query => query.wellFormed accountLimit

def Query.needsWalk : Query → Bool
  | .accountStorage query => query.needsWalk

def Query.minAccounts (measure : V → Nat) (operands : Array V) : Query → Nat
  | .accountStorage query => query.minAccounts measure operands

def Query.canonical (renderValue : V → String) (operands : Array V) : Query → String
  | .accountStorage query => query.canonical renderValue operands

/-- Stable effect bridge for target-owned bounded components. New queue, map, allocator, recorder,
or codec components extend this layer instead of adding top-level SVM Ops/IR/main-emitter cases. -/
inductive Call (V : Type) where
  | accountStorage (call : AccountStorage.Call V)
  deriving BEq, Repr, Inhabited

def Call.mapValues (mapValue : α → β) : Call α → Call β
  | .accountStorage call => .accountStorage (call.mapValues mapValue)

def Call.mapValuesM [Monad m] (mapValue : α → m β) : Call α → m (Call β)
  | .accountStorage call => return .accountStorage (← call.mapValuesM mapValue)

def Call.values : Call V → Array V
  | .accountStorage call => call.values

def Call.anyValue (predicate : V → Bool) (call : Call V) : Bool :=
  call.values.any predicate

def Call.allValues (predicate : V → Bool) (call : Call V) : Bool :=
  call.values.all predicate

def Call.effects : Call V → EffectSummary
  | .accountStorage call => call.effects

def Call.minAccounts (measure : V → Nat) : Call V → Nat
  | .accountStorage call => call.minAccounts measure

def Call.wellFormed (valueWellFormed : V → Bool) (accountLimit : Nat := 64) : Call V → Bool
  | .accountStorage call => call.wellFormed valueWellFormed accountLimit

def Call.canonical (renderValue : V → String) : Call V → String
  | .accountStorage call => call.canonical renderValue

end ProofForge.Svm.Component
